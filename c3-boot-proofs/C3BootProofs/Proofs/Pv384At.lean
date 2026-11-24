import C3BootProofs.Proofs.P384Mont

/-! Fetch lemmas for `c3_crypto::ecdsa::p384_verify_prehash` (`p384VerifyPrehashCode`). -/

namespace C3.RV32.Pv

open C3.Image

/-- Where `p384_verify_prehash` is in the image. -/
abbrev PV : Word := BitVec.ofNat 32 p384VerifyPrehashAddress

set_option maxRecDepth 20000

theorem pv_at_0 : fetchRel p384VerifyPrehashCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF00, 2) := by decide
theorem pv_at_2 : fetchRel p384VerifyPrehashCode 0x2 = some (.store .sw sp ra 0xFC, 2) := by decide
theorem pv_at_4 : fetchRel p384VerifyPrehashCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xF8, 2) := by decide
theorem pv_at_6 : fetchRel p384VerifyPrehashCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xF4, 2) := by decide
theorem pv_at_8 : fetchRel p384VerifyPrehashCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xF0, 2) := by decide
theorem pv_at_a : fetchRel p384VerifyPrehashCode 0xA = some (.store .sw sp (19 : Fin 32) 0xEC, 2) := by decide
theorem pv_at_c : fetchRel p384VerifyPrehashCode 0xC = some (.store .sw sp (20 : Fin 32) 0xE8, 2) := by decide
theorem pv_at_e : fetchRel p384VerifyPrehashCode 0xE = some (.store .sw sp (21 : Fin 32) 0xE4, 2) := by decide
theorem pv_at_10 : fetchRel p384VerifyPrehashCode 0x10 = some (.store .sw sp (22 : Fin 32) 0xE0, 2) := by decide
theorem pv_at_12 : fetchRel p384VerifyPrehashCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xDC, 2) := by decide
theorem pv_at_14 : fetchRel p384VerifyPrehashCode 0x14 = some (.store .sw sp (24 : Fin 32) 0xD8, 2) := by decide
theorem pv_at_16 : fetchRel p384VerifyPrehashCode 0x16 = some (.store .sw sp (25 : Fin 32) 0xD4, 2) := by decide
theorem pv_at_18 : fetchRel p384VerifyPrehashCode 0x18 = some (.store .sw sp (26 : Fin 32) 0xD0, 2) := by decide
theorem pv_at_1a : fetchRel p384VerifyPrehashCode 0x1A = some (.store .sw sp (27 : Fin 32) 0xCC, 2) := by decide
theorem pv_at_1c : fetchRel p384VerifyPrehashCode 0x1C = some (.lui a5 0x2000, 2) := by decide
theorem pv_at_1e : fetchRel p384VerifyPrehashCode 0x1E = some (.aluImm .add a5 a5 0xFFFFFC80, 4) := by decide
theorem pv_at_22 : fetchRel p384VerifyPrehashCode 0x22 = some (.alu .sub sp sp a5, 4) := by decide
theorem pv_at_26 : fetchRel p384VerifyPrehashCode 0x26 = some (.alu .add (21 : Fin 32) x0 a4, 2) := by decide
theorem pv_at_28 : fetchRel p384VerifyPrehashCode 0x28 = some (.alu .add (9 : Fin 32) x0 a3, 2) := by decide
theorem pv_at_2a : fetchRel p384VerifyPrehashCode 0x2A = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem pv_at_2c : fetchRel p384VerifyPrehashCode 0x2C = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem pv_at_2e : fetchRel p384VerifyPrehashCode 0x2E = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem pv_at_30 : fetchRel p384VerifyPrehashCode 0x30 = some (.lui a2 0x3FCC4000, 4) := by decide
theorem pv_at_34 : fetchRel p384VerifyPrehashCode 0x34 = some (.aluImm .add a2 a2 0x2E0, 4) := by decide
theorem pv_at_38 : fetchRel p384VerifyPrehashCode 0x38 = some (.aluImm .add a1 x0 0x30, 4) := by decide
theorem pv_at_3c : fetchRel p384VerifyPrehashCode 0x3C = some (.aluImm .add a3 x0 0x30, 4) := by decide
theorem pv_at_40 : fetchRel p384VerifyPrehashCode 0x40 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_42 : fetchRel p384VerifyPrehashCode 0x42 = some (.auipc ra 0x0, 4) := by decide
theorem pv_at_46 : fetchRel p384VerifyPrehashCode 0x46 = some (.jalr ra ra 0xFFFFFF8A, 4) := by decide
theorem pv_at_4a : fetchRel p384VerifyPrehashCode 0x4A = some (.branch .beq a0 x0 0xE6, 2) := by decide
theorem pv_at_4c : fetchRel p384VerifyPrehashCode 0x4C = some (.lui a2 0x3FCC4000, 4) := by decide
theorem pv_at_50 : fetchRel p384VerifyPrehashCode 0x50 = some (.aluImm .add a2 a2 0x2E0, 4) := by decide
theorem pv_at_54 : fetchRel p384VerifyPrehashCode 0x54 = some (.aluImm .add a1 x0 0x30, 4) := by decide
theorem pv_at_58 : fetchRel p384VerifyPrehashCode 0x58 = some (.aluImm .add a3 x0 0x30, 4) := by decide
theorem pv_at_5c : fetchRel p384VerifyPrehashCode 0x5C = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem pv_at_5e : fetchRel p384VerifyPrehashCode 0x5E = some (.auipc ra 0x0, 4) := by decide
theorem pv_at_62 : fetchRel p384VerifyPrehashCode 0x62 = some (.jalr ra ra 0xFFFFFF6E, 4) := by decide
theorem pv_at_66 : fetchRel p384VerifyPrehashCode 0x66 = some (.alu .add a1 x0 a0, 2) := by decide
theorem pv_at_68 : fetchRel p384VerifyPrehashCode 0x68 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem pv_at_6a : fetchRel p384VerifyPrehashCode 0x6A = some (.branch .beq a1 x0 0xC6, 2) := by decide
theorem pv_at_6c : fetchRel p384VerifyPrehashCode 0x6C = some (.load .lbu a1 (8 : Fin 32) 0x0, 4) := by decide
theorem pv_at_70 : fetchRel p384VerifyPrehashCode 0x70 = some (.aluImm .add a2 x0 0x4, 2) := by decide
theorem pv_at_72 : fetchRel p384VerifyPrehashCode 0x72 = some (.branch .bne a1 a2 0xBE, 4) := by decide
theorem pv_at_76 : fetchRel p384VerifyPrehashCode 0x76 = some (.aluImm .add a0 sp 0xB8, 2) := by decide
theorem pv_at_78 : fetchRel p384VerifyPrehashCode 0x78 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_7a : fetchRel p384VerifyPrehashCode 0x7A = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem pv_at_7e : fetchRel p384VerifyPrehashCode 0x7E = some (.jalr ra ra 0xFFFFFCB2, 4) := by decide
theorem pv_at_82 : fetchRel p384VerifyPrehashCode 0x82 = some (.load .lw a0 sp 0xB8, 2) := by decide
theorem pv_at_84 : fetchRel p384VerifyPrehashCode 0x84 = some (.branch .bne a0 x0 0xAA, 2) := by decide
theorem pv_at_86 : fetchRel p384VerifyPrehashCode 0x86 = some (.aluImm .add (8 : Fin 32) sp 0x7FF, 4) := by decide
theorem pv_at_8a : fetchRel p384VerifyPrehashCode 0x8A = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x581, 4) := by decide
theorem pv_at_8e : fetchRel p384VerifyPrehashCode 0x8E = some (.aluImm .add a1 sp 0xBC, 2) := by decide
theorem pv_at_90 : fetchRel p384VerifyPrehashCode 0x90 = some (.aluImm .add a0 sp 0x58, 2) := by decide
theorem pv_at_92 : fetchRel p384VerifyPrehashCode 0x92 = some (.aluImm .add a2 x0 0x60, 4) := by decide
theorem pv_at_96 : fetchRel p384VerifyPrehashCode 0x96 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_9a : fetchRel p384VerifyPrehashCode 0x9A = some (.jalr ra ra 0x59A, 4) := by decide
theorem pv_at_9e : fetchRel p384VerifyPrehashCode 0x9E = some (.load .lbu (18 : Fin 32) sp 0x11C, 4) := by decide
theorem pv_at_a2 : fetchRel p384VerifyPrehashCode 0xA2 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_a4 : fetchRel p384VerifyPrehashCode 0xA4 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_a8 : fetchRel p384VerifyPrehashCode 0xA8 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_aa : fetchRel p384VerifyPrehashCode 0xAA = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_ac : fetchRel p384VerifyPrehashCode 0xAC = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem pv_at_b0 : fetchRel p384VerifyPrehashCode 0xB0 = some (.jalr ra ra 0xFFFFFA34, 4) := by decide
theorem pv_at_b4 : fetchRel p384VerifyPrehashCode 0xB4 = some (.load .lw a0 (8 : Fin 32) 0x514, 4) := by decide
theorem pv_at_b8 : fetchRel p384VerifyPrehashCode 0xB8 = some (.branch .bne a0 x0 0x76, 2) := by decide
theorem pv_at_ba : fetchRel p384VerifyPrehashCode 0xBA = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_bc : fetchRel p384VerifyPrehashCode 0xBC = some (.aluImm .add a0 a0 0x298, 4) := by decide
theorem pv_at_c0 : fetchRel p384VerifyPrehashCode 0xC0 = some (.alu .add a1 sp a0, 4) := by decide
theorem pv_at_c4 : fetchRel p384VerifyPrehashCode 0xC4 = some (.aluImm .add a0 sp 0x270, 2) := by decide
theorem pv_at_c6 : fetchRel p384VerifyPrehashCode 0xC6 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_ca : fetchRel p384VerifyPrehashCode 0xCA = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_ce : fetchRel p384VerifyPrehashCode 0xCE = some (.jalr ra ra 0x566, 4) := by decide
theorem pv_at_d2 : fetchRel p384VerifyPrehashCode 0xD2 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_d4 : fetchRel p384VerifyPrehashCode 0xD4 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_d8 : fetchRel p384VerifyPrehashCode 0xD8 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_da : fetchRel p384VerifyPrehashCode 0xDA = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem pv_at_dc : fetchRel p384VerifyPrehashCode 0xDC = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem pv_at_e0 : fetchRel p384VerifyPrehashCode 0xE0 = some (.jalr ra ra 0xFFFFFA04, 4) := by decide
theorem pv_at_e4 : fetchRel p384VerifyPrehashCode 0xE4 = some (.load .lw a0 (8 : Fin 32) 0x514, 4) := by decide
theorem pv_at_e8 : fetchRel p384VerifyPrehashCode 0xE8 = some (.branch .bne a0 x0 0x46, 2) := by decide
theorem pv_at_ea : fetchRel p384VerifyPrehashCode 0xEA = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_ec : fetchRel p384VerifyPrehashCode 0xEC = some (.aluImm .add a0 a0 0x298, 4) := by decide
theorem pv_at_f0 : fetchRel p384VerifyPrehashCode 0xF0 = some (.alu .add a1 sp a0, 4) := by decide
theorem pv_at_f4 : fetchRel p384VerifyPrehashCode 0xF4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_f6 : fetchRel p384VerifyPrehashCode 0xF6 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_fa : fetchRel p384VerifyPrehashCode 0xFA = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_fc : fetchRel p384VerifyPrehashCode 0xFC = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_100 : fetchRel p384VerifyPrehashCode 0x100 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_104 : fetchRel p384VerifyPrehashCode 0x104 = some (.jalr ra ra 0x530, 4) := by decide
theorem pv_at_108 : fetchRel p384VerifyPrehashCode 0x108 = some (.aluImm .add a0 sp 0x270, 2) := by decide
theorem pv_at_10a : fetchRel p384VerifyPrehashCode 0x10A = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem pv_at_10e : fetchRel p384VerifyPrehashCode 0x10E = some (.jalr ra ra 0xFFFFFAAC, 4) := by decide
theorem pv_at_112 : fetchRel p384VerifyPrehashCode 0x112 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem pv_at_116 : fetchRel p384VerifyPrehashCode 0x116 = some (.branch .bne a0 x0 0x18, 2) := by decide
theorem pv_at_118 : fetchRel p384VerifyPrehashCode 0x118 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_11a : fetchRel p384VerifyPrehashCode 0x11A = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_11e : fetchRel p384VerifyPrehashCode 0x11E = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_120 : fetchRel p384VerifyPrehashCode 0x120 = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem pv_at_124 : fetchRel p384VerifyPrehashCode 0x124 = some (.jalr ra ra 0xFFFFFA96, 4) := by decide
theorem pv_at_128 : fetchRel p384VerifyPrehashCode 0x128 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem pv_at_12c : fetchRel p384VerifyPrehashCode 0x12C = some (.branch .beq a0 x0 0x2A, 2) := by decide
theorem pv_at_12e : fetchRel p384VerifyPrehashCode 0x12E = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem pv_at_130 : fetchRel p384VerifyPrehashCode 0x130 = some (.lui a1 0x2000, 2) := by decide
theorem pv_at_132 : fetchRel p384VerifyPrehashCode 0x132 = some (.aluImm .add a1 a1 0xFFFFFC80, 4) := by decide
theorem pv_at_136 : fetchRel p384VerifyPrehashCode 0x136 = some (.alu .add sp sp a1, 2) := by decide
theorem pv_at_138 : fetchRel p384VerifyPrehashCode 0x138 = some (.load .lw ra sp 0xFC, 2) := by decide
theorem pv_at_13a : fetchRel p384VerifyPrehashCode 0x13A = some (.load .lw (8 : Fin 32) sp 0xF8, 2) := by decide
theorem pv_at_13c : fetchRel p384VerifyPrehashCode 0x13C = some (.load .lw (9 : Fin 32) sp 0xF4, 2) := by decide
theorem pv_at_13e : fetchRel p384VerifyPrehashCode 0x13E = some (.load .lw (18 : Fin 32) sp 0xF0, 2) := by decide
theorem pv_at_140 : fetchRel p384VerifyPrehashCode 0x140 = some (.load .lw (19 : Fin 32) sp 0xEC, 2) := by decide
theorem pv_at_142 : fetchRel p384VerifyPrehashCode 0x142 = some (.load .lw (20 : Fin 32) sp 0xE8, 2) := by decide
theorem pv_at_144 : fetchRel p384VerifyPrehashCode 0x144 = some (.load .lw (21 : Fin 32) sp 0xE4, 2) := by decide
theorem pv_at_146 : fetchRel p384VerifyPrehashCode 0x146 = some (.load .lw (22 : Fin 32) sp 0xE0, 2) := by decide
theorem pv_at_148 : fetchRel p384VerifyPrehashCode 0x148 = some (.load .lw (23 : Fin 32) sp 0xDC, 2) := by decide
theorem pv_at_14a : fetchRel p384VerifyPrehashCode 0x14A = some (.load .lw (24 : Fin 32) sp 0xD8, 2) := by decide
theorem pv_at_14c : fetchRel p384VerifyPrehashCode 0x14C = some (.load .lw (25 : Fin 32) sp 0xD4, 2) := by decide
theorem pv_at_14e : fetchRel p384VerifyPrehashCode 0x14E = some (.load .lw (26 : Fin 32) sp 0xD0, 2) := by decide
theorem pv_at_150 : fetchRel p384VerifyPrehashCode 0x150 = some (.load .lw (27 : Fin 32) sp 0xCC, 2) := by decide
theorem pv_at_152 : fetchRel p384VerifyPrehashCode 0x152 = some (.aluImm .add sp sp 0x100, 2) := by decide
theorem pv_at_154 : fetchRel p384VerifyPrehashCode 0x154 = some (.jalr x0 ra 0x0, 2) := by decide
theorem pv_at_156 : fetchRel p384VerifyPrehashCode 0x156 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_158 : fetchRel p384VerifyPrehashCode 0x158 = some (.aluImm .add a0 a0 0x744, 4) := by decide
theorem pv_at_15c : fetchRel p384VerifyPrehashCode 0x15C = some (.alu .add (23 : Fin 32) sp a0, 4) := by decide
theorem pv_at_160 : fetchRel p384VerifyPrehashCode 0x160 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_162 : fetchRel p384VerifyPrehashCode 0x162 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_166 : fetchRel p384VerifyPrehashCode 0x166 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_168 : fetchRel p384VerifyPrehashCode 0x168 = some (.aluImm .add a1 sp 0x270, 2) := by decide
theorem pv_at_16a : fetchRel p384VerifyPrehashCode 0x16A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_16e : fetchRel p384VerifyPrehashCode 0x16E = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_172 : fetchRel p384VerifyPrehashCode 0x172 = some (.jalr ra ra 0x4C2, 4) := by decide
theorem pv_at_176 : fetchRel p384VerifyPrehashCode 0x176 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_178 : fetchRel p384VerifyPrehashCode 0x178 = some (.aluImm .add a0 a0 0x2C4, 4) := by decide
theorem pv_at_17c : fetchRel p384VerifyPrehashCode 0x17C = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_17e : fetchRel p384VerifyPrehashCode 0x17E = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_180 : fetchRel p384VerifyPrehashCode 0x180 = some (.aluImm .add a1 a1 0x7A4, 4) := by decide
theorem pv_at_184 : fetchRel p384VerifyPrehashCode 0x184 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_186 : fetchRel p384VerifyPrehashCode 0x186 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_18a : fetchRel p384VerifyPrehashCode 0x18A = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_18e : fetchRel p384VerifyPrehashCode 0x18E = some (.jalr ra ra 0x4A6, 4) := by decide
theorem pv_at_192 : fetchRel p384VerifyPrehashCode 0x192 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_196 : fetchRel p384VerifyPrehashCode 0x196 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_19a : fetchRel p384VerifyPrehashCode 0x19A = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_19c : fetchRel p384VerifyPrehashCode 0x19C = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_1a0 : fetchRel p384VerifyPrehashCode 0x1A0 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_1a2 : fetchRel p384VerifyPrehashCode 0x1A2 = some (.aluImm .add a2 x0 0x60, 4) := by decide
theorem pv_at_1a6 : fetchRel p384VerifyPrehashCode 0x1A6 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_1aa : fetchRel p384VerifyPrehashCode 0x1AA = some (.jalr ra ra 0x48A, 4) := by decide
theorem pv_at_1ae : fetchRel p384VerifyPrehashCode 0x1AE = some (.aluImm .add a0 sp 0x3F0, 2) := by decide
theorem pv_at_1b0 : fetchRel p384VerifyPrehashCode 0x1B0 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_1b4 : fetchRel p384VerifyPrehashCode 0x1B4 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_1b8 : fetchRel p384VerifyPrehashCode 0x1B8 = some (.aluImm .add a2 x0 0x60, 4) := by decide
theorem pv_at_1bc : fetchRel p384VerifyPrehashCode 0x1BC = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_1c0 : fetchRel p384VerifyPrehashCode 0x1C0 = some (.jalr ra ra 0x474, 4) := by decide
theorem pv_at_1c4 : fetchRel p384VerifyPrehashCode 0x1C4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_1c6 : fetchRel p384VerifyPrehashCode 0x1C6 = some (.aluImm .add a0 a0 0x2C4, 4) := by decide
theorem pv_at_1ca : fetchRel p384VerifyPrehashCode 0x1CA = some (.alu .add (21 : Fin 32) sp a0, 4) := by decide
theorem pv_at_1ce : fetchRel p384VerifyPrehashCode 0x1CE = some (.aluImm .add a1 sp 0x88, 2) := by decide
theorem pv_at_1d0 : fetchRel p384VerifyPrehashCode 0x1D0 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_1d4 : fetchRel p384VerifyPrehashCode 0x1D4 = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem pv_at_1d6 : fetchRel p384VerifyPrehashCode 0x1D6 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_1da : fetchRel p384VerifyPrehashCode 0x1DA = some (.jalr ra ra 0x45A, 4) := by decide
theorem pv_at_1de : fetchRel p384VerifyPrehashCode 0x1DE = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_1e0 : fetchRel p384VerifyPrehashCode 0x1E0 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_1e4 : fetchRel p384VerifyPrehashCode 0x1E4 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_1e6 : fetchRel p384VerifyPrehashCode 0x1E6 = some (.aluImm .add a1 sp 0x58, 2) := by decide
theorem pv_at_1e8 : fetchRel p384VerifyPrehashCode 0x1E8 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_1ec : fetchRel p384VerifyPrehashCode 0x1EC = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_1f0 : fetchRel p384VerifyPrehashCode 0x1F0 = some (.jalr ra ra 0x444, 4) := by decide
theorem pv_at_1f4 : fetchRel p384VerifyPrehashCode 0x1F4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_1f6 : fetchRel p384VerifyPrehashCode 0x1F6 = some (.aluImm .add a0 a0 0x2F4, 4) := by decide
theorem pv_at_1fa : fetchRel p384VerifyPrehashCode 0x1FA = some (.alu .add (22 : Fin 32) sp a0, 4) := by decide
theorem pv_at_1fe : fetchRel p384VerifyPrehashCode 0x1FE = some (.lui a1 0x3FCC4000, 4) := by decide
theorem pv_at_202 : fetchRel p384VerifyPrehashCode 0x202 = some (.aluImm .add a1 a1 0x310, 4) := by decide
theorem pv_at_206 : fetchRel p384VerifyPrehashCode 0x206 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_20a : fetchRel p384VerifyPrehashCode 0x20A = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem pv_at_20c : fetchRel p384VerifyPrehashCode 0x20C = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_210 : fetchRel p384VerifyPrehashCode 0x210 = some (.jalr ra ra 0x424, 4) := by decide
theorem pv_at_214 : fetchRel p384VerifyPrehashCode 0x214 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_216 : fetchRel p384VerifyPrehashCode 0x216 = some (.auipc ra 0x7000, 4) := by decide
theorem pv_at_21a : fetchRel p384VerifyPrehashCode 0x21A = some (.jalr ra ra 0x310, 4) := by decide
theorem pv_at_21e : fetchRel p384VerifyPrehashCode 0x21E = some (.aluImm .and (9 : Fin 32) a0 0xFF, 4) := by decide
theorem pv_at_222 : fetchRel p384VerifyPrehashCode 0x222 = some (.lui (18 : Fin 32) 0x3FCC4000, 4) := by decide
theorem pv_at_226 : fetchRel p384VerifyPrehashCode 0x226 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x340, 4) := by decide
theorem pv_at_22a : fetchRel p384VerifyPrehashCode 0x22A = some (.aluImm .add a0 sp 0x120, 2) := by decide
theorem pv_at_22c : fetchRel p384VerifyPrehashCode 0x22C = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_22e : fetchRel p384VerifyPrehashCode 0x22E = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_232 : fetchRel p384VerifyPrehashCode 0x232 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_234 : fetchRel p384VerifyPrehashCode 0x234 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_236 : fetchRel p384VerifyPrehashCode 0x236 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_238 : fetchRel p384VerifyPrehashCode 0x238 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_23c : fetchRel p384VerifyPrehashCode 0x23C = some (.jalr ra ra 0x3DE, 4) := by decide
theorem pv_at_240 : fetchRel p384VerifyPrehashCode 0x240 = some (.aluImm .add a0 sp 0x150, 2) := by decide
theorem pv_at_242 : fetchRel p384VerifyPrehashCode 0x242 = some (.aluImm .add a2 (18 : Fin 32) 0x30, 4) := by decide
theorem pv_at_246 : fetchRel p384VerifyPrehashCode 0x246 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem pv_at_248 : fetchRel p384VerifyPrehashCode 0x248 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_24a : fetchRel p384VerifyPrehashCode 0x24A = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_24e : fetchRel p384VerifyPrehashCode 0x24E = some (.jalr ra ra 0x3CC, 4) := by decide
theorem pv_at_252 : fetchRel p384VerifyPrehashCode 0x252 = some (.aluImm .add a0 sp 0x180, 2) := by decide
theorem pv_at_254 : fetchRel p384VerifyPrehashCode 0x254 = some (.aluImm .add a2 (18 : Fin 32) 0x60, 4) := by decide
theorem pv_at_258 : fetchRel p384VerifyPrehashCode 0x258 = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem pv_at_25a : fetchRel p384VerifyPrehashCode 0x25A = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_25c : fetchRel p384VerifyPrehashCode 0x25C = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_260 : fetchRel p384VerifyPrehashCode 0x260 = some (.jalr ra ra 0x3BA, 4) := by decide
theorem pv_at_264 : fetchRel p384VerifyPrehashCode 0x264 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_266 : fetchRel p384VerifyPrehashCode 0x266 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_26a : fetchRel p384VerifyPrehashCode 0x26A = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_26c : fetchRel p384VerifyPrehashCode 0x26C = some (.aluImm .add a1 sp 0x3F0, 2) := by decide
theorem pv_at_26e : fetchRel p384VerifyPrehashCode 0x26E = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_272 : fetchRel p384VerifyPrehashCode 0x272 = some (.jalr ra ra 0xFFFFF9EA, 4) := by decide
theorem pv_at_276 : fetchRel p384VerifyPrehashCode 0x276 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_27a : fetchRel p384VerifyPrehashCode 0x27A = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_27e : fetchRel p384VerifyPrehashCode 0x27E = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_280 : fetchRel p384VerifyPrehashCode 0x280 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_284 : fetchRel p384VerifyPrehashCode 0x284 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_286 : fetchRel p384VerifyPrehashCode 0x286 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_28a : fetchRel p384VerifyPrehashCode 0x28A = some (.jalr ra ra 0xFFFFFA00, 4) := by decide
theorem pv_at_28e : fetchRel p384VerifyPrehashCode 0x28E = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_290 : fetchRel p384VerifyPrehashCode 0x290 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_294 : fetchRel p384VerifyPrehashCode 0x294 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_296 : fetchRel p384VerifyPrehashCode 0x296 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_29a : fetchRel p384VerifyPrehashCode 0x29A = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_29e : fetchRel p384VerifyPrehashCode 0x29E = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem pv_at_2a2 : fetchRel p384VerifyPrehashCode 0x2A2 = some (.jalr ra ra 0xFFFFFEBA, 4) := by decide
theorem pv_at_2a6 : fetchRel p384VerifyPrehashCode 0x2A6 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_2a8 : fetchRel p384VerifyPrehashCode 0x2A8 = some (.aluImm .add a0 a0 0x2C4, 4) := by decide
theorem pv_at_2ac : fetchRel p384VerifyPrehashCode 0x2AC = some (.alu .add (9 : Fin 32) sp a0, 4) := by decide
theorem pv_at_2b0 : fetchRel p384VerifyPrehashCode 0x2B0 = some (.aluImm .add a1 sp 0x420, 4) := by decide
theorem pv_at_2b4 : fetchRel p384VerifyPrehashCode 0x2B4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_2b6 : fetchRel p384VerifyPrehashCode 0x2B6 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_2ba : fetchRel p384VerifyPrehashCode 0x2BA = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_2bc : fetchRel p384VerifyPrehashCode 0x2BC = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_2c0 : fetchRel p384VerifyPrehashCode 0x2C0 = some (.jalr ra ra 0xFFFFF99C, 4) := by decide
theorem pv_at_2c4 : fetchRel p384VerifyPrehashCode 0x2C4 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_2c8 : fetchRel p384VerifyPrehashCode 0x2C8 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_2cc : fetchRel p384VerifyPrehashCode 0x2CC = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_2ce : fetchRel p384VerifyPrehashCode 0x2CE = some (.aluImm .add a1 a1 0x7A4, 4) := by decide
theorem pv_at_2d2 : fetchRel p384VerifyPrehashCode 0x2D2 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_2d4 : fetchRel p384VerifyPrehashCode 0x2D4 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_2d8 : fetchRel p384VerifyPrehashCode 0x2D8 = some (.jalr ra ra 0xFFFFF9B2, 4) := by decide
theorem pv_at_2dc : fetchRel p384VerifyPrehashCode 0x2DC = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_2e0 : fetchRel p384VerifyPrehashCode 0x2E0 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_2e4 : fetchRel p384VerifyPrehashCode 0x2E4 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_2e6 : fetchRel p384VerifyPrehashCode 0x2E6 = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem pv_at_2ea : fetchRel p384VerifyPrehashCode 0x2EA = some (.jalr ra ra 0xFFFFFE72, 4) := by decide
theorem pv_at_2ee : fetchRel p384VerifyPrehashCode 0x2EE = some (.aluImm .add a0 sp 0x1B0, 2) := by decide
theorem pv_at_2f0 : fetchRel p384VerifyPrehashCode 0x2F0 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_2f2 : fetchRel p384VerifyPrehashCode 0x2F2 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_2f6 : fetchRel p384VerifyPrehashCode 0x2F6 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_2f8 : fetchRel p384VerifyPrehashCode 0x2F8 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_2fc : fetchRel p384VerifyPrehashCode 0x2FC = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_300 : fetchRel p384VerifyPrehashCode 0x300 = some (.jalr ra ra 0x334, 4) := by decide
theorem pv_at_304 : fetchRel p384VerifyPrehashCode 0x304 = some (.aluImm .add a0 sp 0x1E0, 2) := by decide
theorem pv_at_306 : fetchRel p384VerifyPrehashCode 0x306 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_30a : fetchRel p384VerifyPrehashCode 0x30A = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_30c : fetchRel p384VerifyPrehashCode 0x30C = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_310 : fetchRel p384VerifyPrehashCode 0x310 = some (.jalr ra ra 0x324, 4) := by decide
theorem pv_at_314 : fetchRel p384VerifyPrehashCode 0x314 = some (.aluImm .add a0 sp 0x210, 2) := by decide
theorem pv_at_316 : fetchRel p384VerifyPrehashCode 0x316 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem pv_at_318 : fetchRel p384VerifyPrehashCode 0x318 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem pv_at_31a : fetchRel p384VerifyPrehashCode 0x31A = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem pv_at_31e : fetchRel p384VerifyPrehashCode 0x31E = some (.jalr ra ra 0xFFFFFBA8, 4) := by decide
theorem pv_at_322 : fetchRel p384VerifyPrehashCode 0x322 = some (.lui (18 : Fin 32) 0x3FCC5000, 4) := by decide
theorem pv_at_326 : fetchRel p384VerifyPrehashCode 0x326 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xFFFFFD90, 4) := by decide
theorem pv_at_32a : fetchRel p384VerifyPrehashCode 0x32A = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_32e : fetchRel p384VerifyPrehashCode 0x32E = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_332 : fetchRel p384VerifyPrehashCode 0x332 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_336 : fetchRel p384VerifyPrehashCode 0x336 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_338 : fetchRel p384VerifyPrehashCode 0x338 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_33c : fetchRel p384VerifyPrehashCode 0x33C = some (.jalr ra ra 0x2F8, 4) := by decide
theorem pv_at_340 : fetchRel p384VerifyPrehashCode 0x340 = some (.lui a0 0x17702000, 4) := by decide
theorem pv_at_344 : fetchRel p384VerifyPrehashCode 0x344 = some (.lui a1 0x912BA000, 4) := by decide
theorem pv_at_348 : fetchRel p384VerifyPrehashCode 0x348 = some (.aluImm .add (20 : Fin 32) a0 0x3BB, 4) := by decide
theorem pv_at_34c : fetchRel p384VerifyPrehashCode 0x34C = some (.aluImm .add (22 : Fin 32) a1 0xFFFFFF76, 4) := by decide
theorem pv_at_350 : fetchRel p384VerifyPrehashCode 0x350 = some (.store .sw (8 : Fin 32) (20 : Fin 32) 0xF0, 4) := by decide
theorem pv_at_354 : fetchRel p384VerifyPrehashCode 0x354 = some (.store .sw (8 : Fin 32) (22 : Fin 32) 0xF4, 4) := by decide
theorem pv_at_358 : fetchRel p384VerifyPrehashCode 0x358 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_35c : fetchRel p384VerifyPrehashCode 0x35C = some (.aluImm .add a0 a0 0x641, 4) := by decide
theorem pv_at_360 : fetchRel p384VerifyPrehashCode 0x360 = some (.aluImm .add (9 : Fin 32) (18 : Fin 32) 0x60, 4) := by decide
theorem pv_at_364 : fetchRel p384VerifyPrehashCode 0x364 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_368 : fetchRel p384VerifyPrehashCode 0x368 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_36a : fetchRel p384VerifyPrehashCode 0x36A = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_36e : fetchRel p384VerifyPrehashCode 0x36E = some (.jalr ra ra 0x2C6, 4) := by decide
theorem pv_at_372 : fetchRel p384VerifyPrehashCode 0x372 = some (.aluImm .add a0 sp 0x1E0, 2) := by decide
theorem pv_at_374 : fetchRel p384VerifyPrehashCode 0x374 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_378 : fetchRel p384VerifyPrehashCode 0x378 = some (.jalr ra ra 0x584, 4) := by decide
theorem pv_at_37c : fetchRel p384VerifyPrehashCode 0x37C = some (.aluImm .and (24 : Fin 32) a0 0xFF, 4) := by decide
theorem pv_at_380 : fetchRel p384VerifyPrehashCode 0x380 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_382 : fetchRel p384VerifyPrehashCode 0x382 = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_386 : fetchRel p384VerifyPrehashCode 0x386 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_388 : fetchRel p384VerifyPrehashCode 0x388 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_38c : fetchRel p384VerifyPrehashCode 0x38C = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_38e : fetchRel p384VerifyPrehashCode 0x38E = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_392 : fetchRel p384VerifyPrehashCode 0x392 = some (.jalr ra ra 0x2A2, 4) := by decide
theorem pv_at_396 : fetchRel p384VerifyPrehashCode 0x396 = some (.store .sb (23 : Fin 32) x0 0x0, 4) := by decide
theorem pv_at_39a : fetchRel p384VerifyPrehashCode 0x39A = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_39e : fetchRel p384VerifyPrehashCode 0x39E = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_3a2 : fetchRel p384VerifyPrehashCode 0x3A2 = some (.aluImm .add a1 sp 0x1E0, 2) := by decide
theorem pv_at_3a4 : fetchRel p384VerifyPrehashCode 0x3A4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_3a8 : fetchRel p384VerifyPrehashCode 0x3A8 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_3ac : fetchRel p384VerifyPrehashCode 0x3AC = some (.jalr ra ra 0x288, 4) := by decide
theorem pv_at_3b0 : fetchRel p384VerifyPrehashCode 0x3B0 = some (.store .sb (8 : Fin 32) x0 0x0, 4) := by decide
theorem pv_at_3b4 : fetchRel p384VerifyPrehashCode 0x3B4 = some (.aluImm .add a0 sp 0x270, 2) := by decide
theorem pv_at_3b6 : fetchRel p384VerifyPrehashCode 0x3B6 = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_3ba : fetchRel p384VerifyPrehashCode 0x3BA = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pv_at_3bc : fetchRel p384VerifyPrehashCode 0x3BC = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_3c0 : fetchRel p384VerifyPrehashCode 0x3C0 = some (.jalr ra ra 0x20C, 4) := by decide
theorem pv_at_3c4 : fetchRel p384VerifyPrehashCode 0x3C4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_3c6 : fetchRel p384VerifyPrehashCode 0x3C6 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_3ca : fetchRel p384VerifyPrehashCode 0x3CA = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_3cc : fetchRel p384VerifyPrehashCode 0x3CC = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_3d0 : fetchRel p384VerifyPrehashCode 0x3D0 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_3d2 : fetchRel p384VerifyPrehashCode 0x3D2 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_3d6 : fetchRel p384VerifyPrehashCode 0x3D6 = some (.jalr ra ra 0x25E, 4) := by decide
theorem pv_at_3da : fetchRel p384VerifyPrehashCode 0x3DA = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_3dc : fetchRel p384VerifyPrehashCode 0x3DC = some (.store .sb (23 : Fin 32) x0 0x90, 4) := by decide
theorem pv_at_3e0 : fetchRel p384VerifyPrehashCode 0x3E0 = some (.aluImm .add (21 : Fin 32) x0 0x1, 2) := by decide
theorem pv_at_3e2 : fetchRel p384VerifyPrehashCode 0x3E2 = some (.aluImm .add (23 : Fin 32) x0 0x376, 4) := by decide
theorem pv_at_3e6 : fetchRel p384VerifyPrehashCode 0x3E6 = some (.aluImm .add (26 : Fin 32) x0 0xB, 2) := by decide
theorem pv_at_3e8 : fetchRel p384VerifyPrehashCode 0x3E8 = some (.branch .beq (23 : Fin 32) x0 0x240, 4) := by decide
theorem pv_at_3ec : fetchRel p384VerifyPrehashCode 0x3EC = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem pv_at_3ee : fetchRel p384VerifyPrehashCode 0x3EE = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_3f2 : fetchRel p384VerifyPrehashCode 0x3F2 = some (.aluImm .add a1 a1 0x551, 4) := by decide
theorem pv_at_3f6 : fetchRel p384VerifyPrehashCode 0x3F6 = some (.branch .beq a0 (26 : Fin 32) 0x232, 4) := by decide
theorem pv_at_3fa : fetchRel p384VerifyPrehashCode 0x3FA = some (.load .lw a2 a1 0x0, 2) := by decide
theorem pv_at_3fc : fetchRel p384VerifyPrehashCode 0x3FC = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem pv_at_3fe : fetchRel p384VerifyPrehashCode 0x3FE = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem pv_at_400 : fetchRel p384VerifyPrehashCode 0x400 = some (.branch .beq a2 x0 0xFFFFFFF6, 2) := by decide
theorem pv_at_402 : fetchRel p384VerifyPrehashCode 0x402 = some (.branch .bltu (26 : Fin 32) a0 0x226, 4) := by decide
theorem pv_at_406 : fetchRel p384VerifyPrehashCode 0x406 = some (.store .sw sp (24 : Fin 32) 0x54, 2) := by decide
theorem pv_at_408 : fetchRel p384VerifyPrehashCode 0x408 = some (.alu .add a0 x0 (23 : Fin 32), 2) := by decide
theorem pv_at_40a : fetchRel p384VerifyPrehashCode 0x40A = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_40e : fetchRel p384VerifyPrehashCode 0x40E = some (.jalr ra ra 0x62A, 4) := by decide
theorem pv_at_412 : fetchRel p384VerifyPrehashCode 0x412 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem pv_at_414 : fetchRel p384VerifyPrehashCode 0x414 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_416 : fetchRel p384VerifyPrehashCode 0x416 = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_41a : fetchRel p384VerifyPrehashCode 0x41A = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_41c : fetchRel p384VerifyPrehashCode 0x41C = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_420 : fetchRel p384VerifyPrehashCode 0x420 = some (.jalr ra ra 0x58E, 4) := by decide
theorem pv_at_424 : fetchRel p384VerifyPrehashCode 0x424 = some (.alu .add (27 : Fin 32) x0 a0, 2) := by decide
theorem pv_at_426 : fetchRel p384VerifyPrehashCode 0x426 = some (.alu .add (25 : Fin 32) x0 a1, 2) := by decide
theorem pv_at_428 : fetchRel p384VerifyPrehashCode 0x428 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_42c : fetchRel p384VerifyPrehashCode 0x42C = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_430 : fetchRel p384VerifyPrehashCode 0x430 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_434 : fetchRel p384VerifyPrehashCode 0x434 = some (.jalr ra ra 0x57A, 4) := by decide
theorem pv_at_438 : fetchRel p384VerifyPrehashCode 0x438 = some (.aluImm .add (6 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_43a : fetchRel p384VerifyPrehashCode 0x43A = some (.aluImm .add (24 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_43c : fetchRel p384VerifyPrehashCode 0x43C = some (.aluImm .add (7 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_43e : fetchRel p384VerifyPrehashCode 0x43E = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem pv_at_440 : fetchRel p384VerifyPrehashCode 0x440 = some (.aluImm .add a6 x0 0x0, 2) := by decide
theorem pv_at_442 : fetchRel p384VerifyPrehashCode 0x442 = some (.aluImm .add (17 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_444 : fetchRel p384VerifyPrehashCode 0x444 = some (.aluImm .add (30 : Fin 32) x0 0x1, 2) := by decide
theorem pv_at_446 : fetchRel p384VerifyPrehashCode 0x446 = some (.aluImm .add (9 : Fin 32) x0 0x1, 2) := by decide
theorem pv_at_448 : fetchRel p384VerifyPrehashCode 0x448 = some (.alu .add (5 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem pv_at_44a : fetchRel p384VerifyPrehashCode 0x44A = some (.branch .beq (18 : Fin 32) x0 0xE6, 4) := by decide
theorem pv_at_44e : fetchRel p384VerifyPrehashCode 0x44E = some (.aluImm .and a3 a0 0x1, 4) := by decide
theorem pv_at_452 : fetchRel p384VerifyPrehashCode 0x452 = some (.branch .bne a3 x0 0x1C, 2) := by decide
theorem pv_at_454 : fetchRel p384VerifyPrehashCode 0x454 = some (.aluImm .add a3 (21 : Fin 32) 0x2, 4) := by decide
theorem pv_at_458 : fetchRel p384VerifyPrehashCode 0x458 = some (.alu .add a4 x0 (30 : Fin 32), 2) := by decide
theorem pv_at_45a : fetchRel p384VerifyPrehashCode 0x45A = some (.alu .add (31 : Fin 32) x0 (6 : Fin 32), 2) := by decide
theorem pv_at_45c : fetchRel p384VerifyPrehashCode 0x45C = some (.alu .sltu a5 a3 (21 : Fin 32), 4) := by decide
theorem pv_at_460 : fetchRel p384VerifyPrehashCode 0x460 = some (.alu .add (28 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem pv_at_462 : fetchRel p384VerifyPrehashCode 0x462 = some (.alu .add (19 : Fin 32) (19 : Fin 32) a5, 2) := by decide
theorem pv_at_464 : fetchRel p384VerifyPrehashCode 0x464 = some (.alu .add (29 : Fin 32) x0 (7 : Fin 32), 2) := by decide
theorem pv_at_466 : fetchRel p384VerifyPrehashCode 0x466 = some (.alu .add (21 : Fin 32) x0 a3, 2) := by decide
theorem pv_at_468 : fetchRel p384VerifyPrehashCode 0x468 = some (.alu .add a5 x0 a0, 2) := by decide
theorem pv_at_46a : fetchRel p384VerifyPrehashCode 0x46A = some (.alu .add a3 x0 a1, 2) := by decide
theorem pv_at_46c : fetchRel p384VerifyPrehashCode 0x46C = some (.jal x0 0x92, 2) := by decide
theorem pv_at_46e : fetchRel p384VerifyPrehashCode 0x46E = some (.branch .beq (19 : Fin 32) x0 0x3C, 4) := by decide
theorem pv_at_472 : fetchRel p384VerifyPrehashCode 0x472 = some (.alu .slt a3 x0 (19 : Fin 32), 4) := by decide
theorem pv_at_476 : fetchRel p384VerifyPrehashCode 0x476 = some (.branch .bne a3 x0 0x3A, 2) := by decide
theorem pv_at_478 : fetchRel p384VerifyPrehashCode 0x478 = some (.aluImm .add ra (21 : Fin 32) 0x2, 4) := by decide
theorem pv_at_47c : fetchRel p384VerifyPrehashCode 0x47C = some (.alu .add a5 (27 : Fin 32) a0, 4) := by decide
theorem pv_at_480 : fetchRel p384VerifyPrehashCode 0x480 = some (.alu .add a1 a1 (25 : Fin 32), 2) := by decide
theorem pv_at_482 : fetchRel p384VerifyPrehashCode 0x482 = some (.alu .sltu a3 a5 (27 : Fin 32), 4) := by decide
theorem pv_at_486 : fetchRel p384VerifyPrehashCode 0x486 = some (.alu .sltu a0 ra (21 : Fin 32), 4) := by decide
theorem pv_at_48a : fetchRel p384VerifyPrehashCode 0x48A = some (.alu .add a3 a3 a1, 2) := by decide
theorem pv_at_48c : fetchRel p384VerifyPrehashCode 0x48C = some (.alu .add (19 : Fin 32) (19 : Fin 32) a0, 2) := by decide
theorem pv_at_48e : fetchRel p384VerifyPrehashCode 0x48E = some (.alu .add (28 : Fin 32) (9 : Fin 32) (24 : Fin 32), 4) := by decide
theorem pv_at_492 : fetchRel p384VerifyPrehashCode 0x492 = some (.alu .sltu (29 : Fin 32) (28 : Fin 32) (9 : Fin 32), 4) := by decide
theorem pv_at_496 : fetchRel p384VerifyPrehashCode 0x496 = some (.alu .add (7 : Fin 32) (7 : Fin 32) (17 : Fin 32), 2) := by decide
theorem pv_at_498 : fetchRel p384VerifyPrehashCode 0x498 = some (.alu .add (29 : Fin 32) (29 : Fin 32) (7 : Fin 32), 2) := by decide
theorem pv_at_49a : fetchRel p384VerifyPrehashCode 0x49A = some (.alu .add a4 a2 (30 : Fin 32), 4) := by decide
theorem pv_at_49e : fetchRel p384VerifyPrehashCode 0x49E = some (.alu .sltu (31 : Fin 32) a4 a2, 4) := by decide
theorem pv_at_4a2 : fetchRel p384VerifyPrehashCode 0x4A2 = some (.alu .add (6 : Fin 32) (6 : Fin 32) a6, 2) := by decide
theorem pv_at_4a4 : fetchRel p384VerifyPrehashCode 0x4A4 = some (.alu .add (31 : Fin 32) (31 : Fin 32) (6 : Fin 32), 2) := by decide
theorem pv_at_4a6 : fetchRel p384VerifyPrehashCode 0x4A6 = some (.alu .add (21 : Fin 32) x0 ra, 2) := by decide
theorem pv_at_4a8 : fetchRel p384VerifyPrehashCode 0x4A8 = some (.jal x0 0x56, 2) := by decide
theorem pv_at_4aa : fetchRel p384VerifyPrehashCode 0x4AA = some (.alu .sltu a3 x0 (21 : Fin 32), 4) := by decide
theorem pv_at_4ae : fetchRel p384VerifyPrehashCode 0x4AE = some (.branch .beq a3 x0 0xFFFFFFCA, 2) := by decide
theorem pv_at_4b0 : fetchRel p384VerifyPrehashCode 0x4B0 = some (.alu .sltu a3 a0 (27 : Fin 32), 4) := by decide
theorem pv_at_4b4 : fetchRel p384VerifyPrehashCode 0x4B4 = some (.alu .sub a4 a1 (25 : Fin 32), 4) := by decide
theorem pv_at_4b8 : fetchRel p384VerifyPrehashCode 0x4B8 = some (.alu .sub a3 a4 a3, 4) := by decide
theorem pv_at_4bc : fetchRel p384VerifyPrehashCode 0x4BC = some (.aluImm .add (28 : Fin 32) x0 0x2, 2) := by decide
theorem pv_at_4be : fetchRel p384VerifyPrehashCode 0x4BE = some (.alu .sltu a4 (28 : Fin 32) (21 : Fin 32), 4) := by decide
theorem pv_at_4c2 : fetchRel p384VerifyPrehashCode 0x4C2 = some (.alu .sub (8 : Fin 32) x0 (19 : Fin 32), 4) := by decide
theorem pv_at_4c6 : fetchRel p384VerifyPrehashCode 0x4C6 = some (.alu .sub a5 a0 (27 : Fin 32), 4) := by decide
theorem pv_at_4ca : fetchRel p384VerifyPrehashCode 0x4CA = some (.alu .sub (19 : Fin 32) (8 : Fin 32) a4, 4) := by decide
theorem pv_at_4ce : fetchRel p384VerifyPrehashCode 0x4CE = some (.alu .sltu a4 (24 : Fin 32) (9 : Fin 32), 4) := by decide
theorem pv_at_4d2 : fetchRel p384VerifyPrehashCode 0x4D2 = some (.alu .sub (8 : Fin 32) (7 : Fin 32) (17 : Fin 32), 4) := by decide
theorem pv_at_4d6 : fetchRel p384VerifyPrehashCode 0x4D6 = some (.alu .sub (21 : Fin 32) (28 : Fin 32) (21 : Fin 32), 4) := by decide
theorem pv_at_4da : fetchRel p384VerifyPrehashCode 0x4DA = some (.alu .sub (29 : Fin 32) (8 : Fin 32) a4, 4) := by decide
theorem pv_at_4de : fetchRel p384VerifyPrehashCode 0x4DE = some (.alu .sltu a4 (30 : Fin 32) a2, 4) := by decide
theorem pv_at_4e2 : fetchRel p384VerifyPrehashCode 0x4E2 = some (.alu .sub (8 : Fin 32) (6 : Fin 32) a6, 4) := by decide
theorem pv_at_4e6 : fetchRel p384VerifyPrehashCode 0x4E6 = some (.alu .sub (28 : Fin 32) (24 : Fin 32) (9 : Fin 32), 4) := by decide
theorem pv_at_4ea : fetchRel p384VerifyPrehashCode 0x4EA = some (.alu .sub (31 : Fin 32) (8 : Fin 32) a4, 4) := by decide
theorem pv_at_4ee : fetchRel p384VerifyPrehashCode 0x4EE = some (.alu .sub a4 (30 : Fin 32) a2, 4) := by decide
theorem pv_at_4f2 : fetchRel p384VerifyPrehashCode 0x4F2 = some (.alu .add a2 x0 (30 : Fin 32), 2) := by decide
theorem pv_at_4f4 : fetchRel p384VerifyPrehashCode 0x4F4 = some (.alu .add a6 x0 (6 : Fin 32), 2) := by decide
theorem pv_at_4f6 : fetchRel p384VerifyPrehashCode 0x4F6 = some (.alu .add (9 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem pv_at_4f8 : fetchRel p384VerifyPrehashCode 0x4F8 = some (.alu .add (17 : Fin 32) x0 (7 : Fin 32), 2) := by decide
theorem pv_at_4fa : fetchRel p384VerifyPrehashCode 0x4FA = some (.alu .add (27 : Fin 32) x0 a0, 2) := by decide
theorem pv_at_4fc : fetchRel p384VerifyPrehashCode 0x4FC = some (.alu .add (25 : Fin 32) x0 a1, 2) := by decide
theorem pv_at_4fe : fetchRel p384VerifyPrehashCode 0x4FE = some (.aluImm .srl a5 a5 0x1, 2) := by decide
theorem pv_at_500 : fetchRel p384VerifyPrehashCode 0x500 = some (.aluImm .sll a0 a3 0x1F, 4) := by decide
theorem pv_at_504 : fetchRel p384VerifyPrehashCode 0x504 = some (.alu .or a0 a0 a5, 2) := by decide
theorem pv_at_506 : fetchRel p384VerifyPrehashCode 0x506 = some (.aluImm .srl a5 (9 : Fin 32) 0x1F, 4) := by decide
theorem pv_at_50a : fetchRel p384VerifyPrehashCode 0x50A = some (.aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x1, 2) := by decide
theorem pv_at_50c : fetchRel p384VerifyPrehashCode 0x50C = some (.aluImm .sra a1 a3 0x1, 4) := by decide
theorem pv_at_510 : fetchRel p384VerifyPrehashCode 0x510 = some (.alu .or (17 : Fin 32) (17 : Fin 32) a5, 4) := by decide
theorem pv_at_514 : fetchRel p384VerifyPrehashCode 0x514 = some (.aluImm .srl a3 a2 0x1F, 4) := by decide
theorem pv_at_518 : fetchRel p384VerifyPrehashCode 0x518 = some (.aluImm .sll a6 a6 0x1, 2) := by decide
theorem pv_at_51a : fetchRel p384VerifyPrehashCode 0x51A = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem pv_at_51c : fetchRel p384VerifyPrehashCode 0x51C = some (.alu .or a6 a6 a3, 4) := by decide
theorem pv_at_520 : fetchRel p384VerifyPrehashCode 0x520 = some (.aluImm .sll a2 a2 0x1, 2) := by decide
theorem pv_at_522 : fetchRel p384VerifyPrehashCode 0x522 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem pv_at_524 : fetchRel p384VerifyPrehashCode 0x524 = some (.alu .add (30 : Fin 32) x0 a4, 2) := by decide
theorem pv_at_526 : fetchRel p384VerifyPrehashCode 0x526 = some (.alu .add (6 : Fin 32) x0 (31 : Fin 32), 2) := by decide
theorem pv_at_528 : fetchRel p384VerifyPrehashCode 0x528 = some (.alu .add (24 : Fin 32) x0 (28 : Fin 32), 2) := by decide
theorem pv_at_52a : fetchRel p384VerifyPrehashCode 0x52A = some (.alu .add (7 : Fin 32) x0 (29 : Fin 32), 2) := by decide
theorem pv_at_52c : fetchRel p384VerifyPrehashCode 0x52C = some (.branch .bne (5 : Fin 32) x0 0xFFFFFF22, 4) := by decide
theorem pv_at_530 : fetchRel p384VerifyPrehashCode 0x530 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_532 : fetchRel p384VerifyPrehashCode 0x532 = some (.aluImm .add a0 a0 0x744, 4) := by decide
theorem pv_at_536 : fetchRel p384VerifyPrehashCode 0x536 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_538 : fetchRel p384VerifyPrehashCode 0x538 = some (.store .sw a0 (9 : Fin 32) 0x524, 4) := by decide
theorem pv_at_53c : fetchRel p384VerifyPrehashCode 0x53C = some (.store .sw a0 (17 : Fin 32) 0x528, 4) := by decide
theorem pv_at_540 : fetchRel p384VerifyPrehashCode 0x540 = some (.store .sw a0 a2 0x52C, 4) := by decide
theorem pv_at_544 : fetchRel p384VerifyPrehashCode 0x544 = some (.store .sw a0 a6 0x530, 4) := by decide
theorem pv_at_548 : fetchRel p384VerifyPrehashCode 0x548 = some (.store .sw a0 (24 : Fin 32) 0x534, 4) := by decide
theorem pv_at_54c : fetchRel p384VerifyPrehashCode 0x54C = some (.store .sw a0 (7 : Fin 32) 0x538, 4) := by decide
theorem pv_at_550 : fetchRel p384VerifyPrehashCode 0x550 = some (.store .sw a0 (30 : Fin 32) 0x53C, 4) := by decide
theorem pv_at_554 : fetchRel p384VerifyPrehashCode 0x554 = some (.store .sw a0 (6 : Fin 32) 0x540, 4) := by decide
theorem pv_at_558 : fetchRel p384VerifyPrehashCode 0x558 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_55a : fetchRel p384VerifyPrehashCode 0x55A = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_55e : fetchRel p384VerifyPrehashCode 0x55E = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_560 : fetchRel p384VerifyPrehashCode 0x560 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_562 : fetchRel p384VerifyPrehashCode 0x562 = some (.aluImm .add a1 a1 0x714, 4) := by decide
theorem pv_at_566 : fetchRel p384VerifyPrehashCode 0x566 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_568 : fetchRel p384VerifyPrehashCode 0x568 = some (.aluImm .add a2 sp 0x7FF, 4) := by decide
theorem pv_at_56c : fetchRel p384VerifyPrehashCode 0x56C = some (.aluImm .add a2 a2 0x551, 4) := by decide
theorem pv_at_570 : fetchRel p384VerifyPrehashCode 0x570 = some (.lui a3 0x2000, 2) := by decide
theorem pv_at_572 : fetchRel p384VerifyPrehashCode 0x572 = some (.aluImm .add a3 a3 0xFFFFFC68, 4) := by decide
theorem pv_at_576 : fetchRel p384VerifyPrehashCode 0x576 = some (.alu .add a3 a3 sp, 2) := by decide
theorem pv_at_578 : fetchRel p384VerifyPrehashCode 0x578 = some (.alu .add a4 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_57a : fetchRel p384VerifyPrehashCode 0x57A = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_57e : fetchRel p384VerifyPrehashCode 0x57E = some (.jalr ra ra 0x452, 4) := by decide
theorem pv_at_582 : fetchRel p384VerifyPrehashCode 0x582 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_584 : fetchRel p384VerifyPrehashCode 0x584 = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_588 : fetchRel p384VerifyPrehashCode 0x588 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_58a : fetchRel p384VerifyPrehashCode 0x58A = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_58c : fetchRel p384VerifyPrehashCode 0x58C = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_590 : fetchRel p384VerifyPrehashCode 0x590 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_592 : fetchRel p384VerifyPrehashCode 0x592 = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_596 : fetchRel p384VerifyPrehashCode 0x596 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_59a : fetchRel p384VerifyPrehashCode 0x59A = some (.jalr ra ra 0x9A, 4) := by decide
theorem pv_at_59e : fetchRel p384VerifyPrehashCode 0x59E = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_5a2 : fetchRel p384VerifyPrehashCode 0x5A2 = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_5a6 : fetchRel p384VerifyPrehashCode 0x5A6 = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_5aa : fetchRel p384VerifyPrehashCode 0x5AA = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_5ac : fetchRel p384VerifyPrehashCode 0x5AC = some (.aluImm .add a1 a1 0x2C8, 4) := by decide
theorem pv_at_5b0 : fetchRel p384VerifyPrehashCode 0x5B0 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_5b2 : fetchRel p384VerifyPrehashCode 0x5B2 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_5b6 : fetchRel p384VerifyPrehashCode 0x5B6 = some (.jalr ra ra 0x7E, 4) := by decide
theorem pv_at_5ba : fetchRel p384VerifyPrehashCode 0x5BA = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_5bc : fetchRel p384VerifyPrehashCode 0x5BC = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_5c0 : fetchRel p384VerifyPrehashCode 0x5C0 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_5c2 : fetchRel p384VerifyPrehashCode 0x5C2 = some (.aluImm .add a1 sp 0x270, 2) := by decide
theorem pv_at_5c4 : fetchRel p384VerifyPrehashCode 0x5C4 = some (.lui a2 0x1000, 2) := by decide
theorem pv_at_5c6 : fetchRel p384VerifyPrehashCode 0x5C6 = some (.aluImm .add a2 a2 0x7A4, 4) := by decide
theorem pv_at_5ca : fetchRel p384VerifyPrehashCode 0x5CA = some (.alu .add a2 a2 sp, 2) := by decide
theorem pv_at_5cc : fetchRel p384VerifyPrehashCode 0x5CC = some (.aluImm .add a3 sp 0x7FF, 4) := by decide
theorem pv_at_5d0 : fetchRel p384VerifyPrehashCode 0x5D0 = some (.aluImm .add a3 a3 0x611, 4) := by decide
theorem pv_at_5d4 : fetchRel p384VerifyPrehashCode 0x5D4 = some (.lui a4 0x2000, 2) := by decide
theorem pv_at_5d6 : fetchRel p384VerifyPrehashCode 0x5D6 = some (.aluImm .add a4 a4 0xFFFFFC68, 4) := by decide
theorem pv_at_5da : fetchRel p384VerifyPrehashCode 0x5DA = some (.alu .add a6 sp a4, 4) := by decide
theorem pv_at_5de : fetchRel p384VerifyPrehashCode 0x5DE = some (.alu .add a4 x0 (20 : Fin 32), 2) := by decide
theorem pv_at_5e0 : fetchRel p384VerifyPrehashCode 0x5E0 = some (.alu .add a5 x0 (22 : Fin 32), 2) := by decide
theorem pv_at_5e2 : fetchRel p384VerifyPrehashCode 0x5E2 = some (.alu .add (17 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem pv_at_5e4 : fetchRel p384VerifyPrehashCode 0x5E4 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_5e8 : fetchRel p384VerifyPrehashCode 0x5E8 = some (.jalr ra ra 0x472, 4) := by decide
theorem pv_at_5ec : fetchRel p384VerifyPrehashCode 0x5EC = some (.aluImm .add a0 sp 0x270, 2) := by decide
theorem pv_at_5ee : fetchRel p384VerifyPrehashCode 0x5EE = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_5f0 : fetchRel p384VerifyPrehashCode 0x5F0 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_5f4 : fetchRel p384VerifyPrehashCode 0x5F4 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_5f6 : fetchRel p384VerifyPrehashCode 0x5F6 = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_5fa : fetchRel p384VerifyPrehashCode 0x5FA = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_5fe : fetchRel p384VerifyPrehashCode 0x5FE = some (.jalr ra ra 0x36, 4) := by decide
theorem pv_at_602 : fetchRel p384VerifyPrehashCode 0x602 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_604 : fetchRel p384VerifyPrehashCode 0x604 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_608 : fetchRel p384VerifyPrehashCode 0x608 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_60a : fetchRel p384VerifyPrehashCode 0x60A = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_60e : fetchRel p384VerifyPrehashCode 0x60E = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_610 : fetchRel p384VerifyPrehashCode 0x610 = some (.aluImm .add a1 a1 0x2C8, 4) := by decide
theorem pv_at_614 : fetchRel p384VerifyPrehashCode 0x614 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_616 : fetchRel p384VerifyPrehashCode 0x616 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_61a : fetchRel p384VerifyPrehashCode 0x61A = some (.jalr ra ra 0x1A, 4) := by decide
theorem pv_at_61e : fetchRel p384VerifyPrehashCode 0x61E = some (.alu .sub (23 : Fin 32) (23 : Fin 32) (18 : Fin 32), 4) := by decide
theorem pv_at_622 : fetchRel p384VerifyPrehashCode 0x622 = some (.load .lw (24 : Fin 32) sp 0x54, 2) := by decide
theorem pv_at_624 : fetchRel p384VerifyPrehashCode 0x624 = some (.branch .bne (23 : Fin 32) x0 0xFFFFFDC8, 4) := by decide
theorem pv_at_628 : fetchRel p384VerifyPrehashCode 0x628 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_62a : fetchRel p384VerifyPrehashCode 0x62A = some (.aluImm .add a0 a0 0x744, 4) := by decide
theorem pv_at_62e : fetchRel p384VerifyPrehashCode 0x62E = some (.alu .add (9 : Fin 32) sp a0, 4) := by decide
theorem pv_at_632 : fetchRel p384VerifyPrehashCode 0x632 = some (.load .lbu a2 (9 : Fin 32) 0x0, 4) := by decide
theorem pv_at_636 : fetchRel p384VerifyPrehashCode 0x636 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_638 : fetchRel p384VerifyPrehashCode 0x638 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_63c : fetchRel p384VerifyPrehashCode 0x63C = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_63e : fetchRel p384VerifyPrehashCode 0x63E = some (.aluImm .add a1 sp 0x270, 2) := by decide
theorem pv_at_640 : fetchRel p384VerifyPrehashCode 0x640 = some (.aluImm .add a3 sp 0x7FF, 4) := by decide
theorem pv_at_644 : fetchRel p384VerifyPrehashCode 0x644 = some (.aluImm .add a3 a3 0x611, 4) := by decide
theorem pv_at_648 : fetchRel p384VerifyPrehashCode 0x648 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_64c : fetchRel p384VerifyPrehashCode 0x64C = some (.jalr ra ra 0x2CA, 4) := by decide
theorem pv_at_650 : fetchRel p384VerifyPrehashCode 0x650 = some (.lui a1 0x3FCC5000, 4) := by decide
theorem pv_at_654 : fetchRel p384VerifyPrehashCode 0x654 = some (.aluImm .add a1 a1 0xFFFFFCC4, 4) := by decide
theorem pv_at_658 : fetchRel p384VerifyPrehashCode 0x658 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_65a : fetchRel p384VerifyPrehashCode 0x65A = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_65e : fetchRel p384VerifyPrehashCode 0x65E = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_660 : fetchRel p384VerifyPrehashCode 0x660 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_664 : fetchRel p384VerifyPrehashCode 0x664 = some (.jalr ra ra 0xE4, 4) := by decide
theorem pv_at_668 : fetchRel p384VerifyPrehashCode 0x668 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem pv_at_66c : fetchRel p384VerifyPrehashCode 0x66C = some (.alu .and (8 : Fin 32) a0 (24 : Fin 32), 4) := by decide
theorem pv_at_670 : fetchRel p384VerifyPrehashCode 0x670 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_672 : fetchRel p384VerifyPrehashCode 0x672 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_676 : fetchRel p384VerifyPrehashCode 0x676 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_678 : fetchRel p384VerifyPrehashCode 0x678 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_67a : fetchRel p384VerifyPrehashCode 0x67A = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_67e : fetchRel p384VerifyPrehashCode 0x67E = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_680 : fetchRel p384VerifyPrehashCode 0x680 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_684 : fetchRel p384VerifyPrehashCode 0x684 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_688 : fetchRel p384VerifyPrehashCode 0x688 = some (.jalr ra ra 0xFFFFFFAC, 4) := by decide
theorem pv_at_68c : fetchRel p384VerifyPrehashCode 0x68C = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_68e : fetchRel p384VerifyPrehashCode 0x68E = some (.auipc ra 0x7000, 4) := by decide
theorem pv_at_692 : fetchRel p384VerifyPrehashCode 0x692 = some (.jalr ra ra 0xFFFFFE98, 4) := by decide
theorem pv_at_696 : fetchRel p384VerifyPrehashCode 0x696 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem pv_at_698 : fetchRel p384VerifyPrehashCode 0x698 = some (.store .sb (9 : Fin 32) a0 0x90, 4) := by decide
theorem pv_at_69c : fetchRel p384VerifyPrehashCode 0x69C = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_6a0 : fetchRel p384VerifyPrehashCode 0x6A0 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_6a4 : fetchRel p384VerifyPrehashCode 0x6A4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_6a8 : fetchRel p384VerifyPrehashCode 0x6A8 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pv_at_6aa : fetchRel p384VerifyPrehashCode 0x6AA = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_6ae : fetchRel p384VerifyPrehashCode 0x6AE = some (.jalr ra ra 0xFFFFFF1E, 4) := by decide
theorem pv_at_6b2 : fetchRel p384VerifyPrehashCode 0x6B2 = some (.aluImm .and (9 : Fin 32) (8 : Fin 32) 0xFF, 4) := by decide
theorem pv_at_6b6 : fetchRel p384VerifyPrehashCode 0x6B6 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_6b8 : fetchRel p384VerifyPrehashCode 0x6B8 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_6bc : fetchRel p384VerifyPrehashCode 0x6BC = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_6be : fetchRel p384VerifyPrehashCode 0x6BE = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_6c2 : fetchRel p384VerifyPrehashCode 0x6C2 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_6c6 : fetchRel p384VerifyPrehashCode 0x6C6 = some (.lui a2 0x1000, 2) := by decide
theorem pv_at_6c8 : fetchRel p384VerifyPrehashCode 0x6C8 = some (.aluImm .add a2 a2 0x7A4, 4) := by decide
theorem pv_at_6cc : fetchRel p384VerifyPrehashCode 0x6CC = some (.alu .add a2 a2 sp, 2) := by decide
theorem pv_at_6ce : fetchRel p384VerifyPrehashCode 0x6CE = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_6d0 : fetchRel p384VerifyPrehashCode 0x6D0 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_6d4 : fetchRel p384VerifyPrehashCode 0x6D4 = some (.jalr ra ra 0xFFFFFF46, 4) := by decide
theorem pv_at_6d8 : fetchRel p384VerifyPrehashCode 0x6D8 = some (.aluImm .add (25 : Fin 32) sp 0x7FF, 4) := by decide
theorem pv_at_6dc : fetchRel p384VerifyPrehashCode 0x6DC = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x581, 4) := by decide
theorem pv_at_6e0 : fetchRel p384VerifyPrehashCode 0x6E0 = some (.store .sb (25 : Fin 32) (8 : Fin 32) 0x544, 4) := by decide
theorem pv_at_6e4 : fetchRel p384VerifyPrehashCode 0x6E4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_6e6 : fetchRel p384VerifyPrehashCode 0x6E6 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_6ea : fetchRel p384VerifyPrehashCode 0x6EA = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_6ec : fetchRel p384VerifyPrehashCode 0x6EC = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_6f0 : fetchRel p384VerifyPrehashCode 0x6F0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pv_at_6f2 : fetchRel p384VerifyPrehashCode 0x6F2 = some (.lui a3 0x1000, 2) := by decide
theorem pv_at_6f4 : fetchRel p384VerifyPrehashCode 0x6F4 = some (.aluImm .add a3 a3 0x7A4, 4) := by decide
theorem pv_at_6f8 : fetchRel p384VerifyPrehashCode 0x6F8 = some (.alu .add (18 : Fin 32) sp a3, 4) := by decide
theorem pv_at_6fc : fetchRel p384VerifyPrehashCode 0x6FC = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_700 : fetchRel p384VerifyPrehashCode 0x700 = some (.jalr ra ra 0xFFFFFECC, 4) := by decide
theorem pv_at_704 : fetchRel p384VerifyPrehashCode 0x704 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_708 : fetchRel p384VerifyPrehashCode 0x708 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_70c : fetchRel p384VerifyPrehashCode 0x70C = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_70e : fetchRel p384VerifyPrehashCode 0x70E = some (.aluImm .add a1 a1 0x7A4, 4) := by decide
theorem pv_at_712 : fetchRel p384VerifyPrehashCode 0x712 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_714 : fetchRel p384VerifyPrehashCode 0x714 = some (.lui a2 0x1000, 2) := by decide
theorem pv_at_716 : fetchRel p384VerifyPrehashCode 0x716 = some (.aluImm .add a2 a2 0x294, 4) := by decide
theorem pv_at_71a : fetchRel p384VerifyPrehashCode 0x71A = some (.alu .add a2 a2 sp, 2) := by decide
theorem pv_at_71c : fetchRel p384VerifyPrehashCode 0x71C = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_71e : fetchRel p384VerifyPrehashCode 0x71E = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_722 : fetchRel p384VerifyPrehashCode 0x722 = some (.jalr ra ra 0xFFFFFEF8, 4) := by decide
theorem pv_at_726 : fetchRel p384VerifyPrehashCode 0x726 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem pv_at_728 : fetchRel p384VerifyPrehashCode 0x728 = some (.store .sb (25 : Fin 32) (8 : Fin 32) 0x514, 4) := by decide
theorem pv_at_72c : fetchRel p384VerifyPrehashCode 0x72C = some (.branch .bne (9 : Fin 32) a0 0xAA4, 4) := by decide
theorem pv_at_730 : fetchRel p384VerifyPrehashCode 0x730 = some (.aluImm .add a0 sp 0x240, 2) := by decide
theorem pv_at_732 : fetchRel p384VerifyPrehashCode 0x732 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_736 : fetchRel p384VerifyPrehashCode 0x736 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_73a : fetchRel p384VerifyPrehashCode 0x73A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_73e : fetchRel p384VerifyPrehashCode 0x73E = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_742 : fetchRel p384VerifyPrehashCode 0x742 = some (.jalr ra ra 0xFFFFFEF2, 4) := by decide
theorem pv_at_746 : fetchRel p384VerifyPrehashCode 0x746 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_74a : fetchRel p384VerifyPrehashCode 0x74A = some (.aluImm .add a0 a0 0x6A1, 4) := by decide
theorem pv_at_74e : fetchRel p384VerifyPrehashCode 0x74E = some (.aluImm .add a1 sp 0x210, 2) := by decide
theorem pv_at_750 : fetchRel p384VerifyPrehashCode 0x750 = some (.aluImm .add a2 sp 0x240, 2) := by decide
theorem pv_at_752 : fetchRel p384VerifyPrehashCode 0x752 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_756 : fetchRel p384VerifyPrehashCode 0x756 = some (.jalr ra ra 0x412, 4) := by decide
theorem pv_at_75a : fetchRel p384VerifyPrehashCode 0x75A = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_75c : fetchRel p384VerifyPrehashCode 0x75C = some (.aluImm .add a0 a0 0x324, 4) := by decide
theorem pv_at_760 : fetchRel p384VerifyPrehashCode 0x760 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_762 : fetchRel p384VerifyPrehashCode 0x762 = some (.aluImm .add a1 sp 0x1B0, 2) := by decide
theorem pv_at_764 : fetchRel p384VerifyPrehashCode 0x764 = some (.aluImm .add a2 sp 0x240, 2) := by decide
theorem pv_at_766 : fetchRel p384VerifyPrehashCode 0x766 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_76a : fetchRel p384VerifyPrehashCode 0x76A = some (.jalr ra ra 0x3FE, 4) := by decide
theorem pv_at_76e : fetchRel p384VerifyPrehashCode 0x76E = some (.lui (23 : Fin 32) 0x3FCC4000, 4) := by decide
theorem pv_at_772 : fetchRel p384VerifyPrehashCode 0x772 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x470, 4) := by decide
theorem pv_at_776 : fetchRel p384VerifyPrehashCode 0x776 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_77a : fetchRel p384VerifyPrehashCode 0x77A = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_77e : fetchRel p384VerifyPrehashCode 0x77E = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem pv_at_782 : fetchRel p384VerifyPrehashCode 0x782 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem pv_at_784 : fetchRel p384VerifyPrehashCode 0x784 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_788 : fetchRel p384VerifyPrehashCode 0x788 = some (.jalr ra ra 0xFFFFFEAC, 4) := by decide
theorem pv_at_78c : fetchRel p384VerifyPrehashCode 0x78C = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_78e : fetchRel p384VerifyPrehashCode 0x78E = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_792 : fetchRel p384VerifyPrehashCode 0x792 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_794 : fetchRel p384VerifyPrehashCode 0x794 = some (.aluImm .add a1 sp 0x120, 2) := by decide
theorem pv_at_796 : fetchRel p384VerifyPrehashCode 0x796 = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem pv_at_79a : fetchRel p384VerifyPrehashCode 0x79A = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_79e : fetchRel p384VerifyPrehashCode 0x79E = some (.jalr ra ra 0xFFFFFE96, 4) := by decide
theorem pv_at_7a2 : fetchRel p384VerifyPrehashCode 0x7A2 = some (.aluImm .add a0 sp 0x270, 2) := by decide
theorem pv_at_7a4 : fetchRel p384VerifyPrehashCode 0x7A4 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_7a8 : fetchRel p384VerifyPrehashCode 0x7A8 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_7ac : fetchRel p384VerifyPrehashCode 0x7AC = some (.aluImm .add a2 x0 0xC0, 4) := by decide
theorem pv_at_7b0 : fetchRel p384VerifyPrehashCode 0x7B0 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_7b4 : fetchRel p384VerifyPrehashCode 0x7B4 = some (.jalr ra ra 0xFFFFFE80, 4) := by decide
theorem pv_at_7b8 : fetchRel p384VerifyPrehashCode 0x7B8 = some (.aluImm .add a0 sp 0x330, 2) := by decide
theorem pv_at_7ba : fetchRel p384VerifyPrehashCode 0x7BA = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_7bc : fetchRel p384VerifyPrehashCode 0x7BC = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_7c0 : fetchRel p384VerifyPrehashCode 0x7C0 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_7c2 : fetchRel p384VerifyPrehashCode 0x7C2 = some (.aluImm .add a2 x0 0xC0, 4) := by decide
theorem pv_at_7c6 : fetchRel p384VerifyPrehashCode 0x7C6 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_7ca : fetchRel p384VerifyPrehashCode 0x7CA = some (.jalr ra ra 0xFFFFFE6A, 4) := by decide
theorem pv_at_7ce : fetchRel p384VerifyPrehashCode 0x7CE = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_7d0 : fetchRel p384VerifyPrehashCode 0x7D0 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_7d4 : fetchRel p384VerifyPrehashCode 0x7D4 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_7d6 : fetchRel p384VerifyPrehashCode 0x7D6 = some (.aluImm .add a1 sp 0x270, 2) := by decide
theorem pv_at_7d8 : fetchRel p384VerifyPrehashCode 0x7D8 = some (.aluImm .add a2 x0 0x180, 4) := by decide
theorem pv_at_7dc : fetchRel p384VerifyPrehashCode 0x7DC = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_7e0 : fetchRel p384VerifyPrehashCode 0x7E0 = some (.jalr ra ra 0xFFFFFE54, 4) := by decide
theorem pv_at_7e4 : fetchRel p384VerifyPrehashCode 0x7E4 = some (.aluImm .add (19 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_7e6 : fetchRel p384VerifyPrehashCode 0x7E6 = some (.aluImm .add (20 : Fin 32) x0 0x2, 2) := by decide
theorem pv_at_7e8 : fetchRel p384VerifyPrehashCode 0x7E8 = some (.aluImm .add (21 : Fin 32) x0 0x480, 4) := by decide
theorem pv_at_7ec : fetchRel p384VerifyPrehashCode 0x7EC = some (.aluImm .add (22 : Fin 32) sp 0x450, 4) := by decide
theorem pv_at_7f0 : fetchRel p384VerifyPrehashCode 0x7F0 = some (.branch .beq (20 : Fin 32) x0 0x118, 4) := by decide
theorem pv_at_7f4 : fetchRel p384VerifyPrehashCode 0x7F4 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_7f8 : fetchRel p384VerifyPrehashCode 0x7F8 = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_7fc : fetchRel p384VerifyPrehashCode 0x7FC = some (.aluImm .add a2 x0 0xC0, 4) := by decide
theorem pv_at_800 : fetchRel p384VerifyPrehashCode 0x800 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_802 : fetchRel p384VerifyPrehashCode 0x802 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_806 : fetchRel p384VerifyPrehashCode 0x806 = some (.jalr ra ra 0xFFFFFE2E, 4) := by decide
theorem pv_at_80a : fetchRel p384VerifyPrehashCode 0x80A = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_80c : fetchRel p384VerifyPrehashCode 0x80C = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_810 : fetchRel p384VerifyPrehashCode 0x810 = some (.alu .add (8 : Fin 32) sp a0, 4) := by decide
theorem pv_at_814 : fetchRel p384VerifyPrehashCode 0x814 = some (.aluImm .add (9 : Fin 32) x0 0x8, 2) := by decide
theorem pv_at_816 : fetchRel p384VerifyPrehashCode 0x816 = some (.branch .beq (9 : Fin 32) x0 0x1A, 2) := by decide
theorem pv_at_818 : fetchRel p384VerifyPrehashCode 0x818 = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem pv_at_81c : fetchRel p384VerifyPrehashCode 0x81C = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_81e : fetchRel p384VerifyPrehashCode 0x81E = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem pv_at_820 : fetchRel p384VerifyPrehashCode 0x820 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_824 : fetchRel p384VerifyPrehashCode 0x824 = some (.jalr ra ra 0xFFFFFE10, 4) := by decide
theorem pv_at_828 : fetchRel p384VerifyPrehashCode 0x828 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x90, 4) := by decide
theorem pv_at_82c : fetchRel p384VerifyPrehashCode 0x82C = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem pv_at_82e : fetchRel p384VerifyPrehashCode 0x82E = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFEA, 2) := by decide
theorem pv_at_830 : fetchRel p384VerifyPrehashCode 0x830 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_834 : fetchRel p384VerifyPrehashCode 0x834 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_838 : fetchRel p384VerifyPrehashCode 0x838 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_83a : fetchRel p384VerifyPrehashCode 0x83A = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_83e : fetchRel p384VerifyPrehashCode 0x83E = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_840 : fetchRel p384VerifyPrehashCode 0x840 = some (.aluImm .add a2 x0 0x480, 4) := by decide
theorem pv_at_844 : fetchRel p384VerifyPrehashCode 0x844 = some (.aluImm .add (8 : Fin 32) sp 0x7FF, 4) := by decide
theorem pv_at_848 : fetchRel p384VerifyPrehashCode 0x848 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x611, 4) := by decide
theorem pv_at_84c : fetchRel p384VerifyPrehashCode 0x84C = some (.aluImm .add (9 : Fin 32) x0 0x480, 4) := by decide
theorem pv_at_850 : fetchRel p384VerifyPrehashCode 0x850 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_854 : fetchRel p384VerifyPrehashCode 0x854 = some (.jalr ra ra 0xFFFFFDE0, 4) := by decide
theorem pv_at_858 : fetchRel p384VerifyPrehashCode 0x858 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_85a : fetchRel p384VerifyPrehashCode 0x85A = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_85e : fetchRel p384VerifyPrehashCode 0x85E = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_860 : fetchRel p384VerifyPrehashCode 0x860 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_864 : fetchRel p384VerifyPrehashCode 0x864 = some (.aluImm .add a1 a1 0x551, 4) := by decide
theorem pv_at_868 : fetchRel p384VerifyPrehashCode 0x868 = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem pv_at_86c : fetchRel p384VerifyPrehashCode 0x86C = some (.jalr ra ra 0x364, 4) := by decide
theorem pv_at_870 : fetchRel p384VerifyPrehashCode 0x870 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_872 : fetchRel p384VerifyPrehashCode 0x872 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_876 : fetchRel p384VerifyPrehashCode 0x876 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_878 : fetchRel p384VerifyPrehashCode 0x878 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_87c : fetchRel p384VerifyPrehashCode 0x87C = some (.aluImm .add a1 a1 0x551, 4) := by decide
theorem pv_at_880 : fetchRel p384VerifyPrehashCode 0x880 = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem pv_at_884 : fetchRel p384VerifyPrehashCode 0x884 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_888 : fetchRel p384VerifyPrehashCode 0x888 = some (.jalr ra ra 0xFFFFFDAC, 4) := by decide
theorem pv_at_88c : fetchRel p384VerifyPrehashCode 0x88C = some (.branch .beq (9 : Fin 32) x0 0x3C, 2) := by decide
theorem pv_at_88e : fetchRel p384VerifyPrehashCode 0x88E = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_890 : fetchRel p384VerifyPrehashCode 0x890 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_894 : fetchRel p384VerifyPrehashCode 0x894 = some (.alu .add a1 sp a0, 4) := by decide
theorem pv_at_898 : fetchRel p384VerifyPrehashCode 0x898 = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem pv_at_89c : fetchRel p384VerifyPrehashCode 0x89C = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_89e : fetchRel p384VerifyPrehashCode 0x89E = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_8a2 : fetchRel p384VerifyPrehashCode 0x8A2 = some (.jalr ra ra 0xFFFFFD92, 4) := by decide
theorem pv_at_8a6 : fetchRel p384VerifyPrehashCode 0x8A6 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_8a8 : fetchRel p384VerifyPrehashCode 0x8A8 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_8ac : fetchRel p384VerifyPrehashCode 0x8AC = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_8ae : fetchRel p384VerifyPrehashCode 0x8AE = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_8b0 : fetchRel p384VerifyPrehashCode 0x8B0 = some (.aluImm .add a1 a1 0x714, 4) := by decide
theorem pv_at_8b4 : fetchRel p384VerifyPrehashCode 0x8B4 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_8b6 : fetchRel p384VerifyPrehashCode 0x8B6 = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem pv_at_8ba : fetchRel p384VerifyPrehashCode 0x8BA = some (.jalr ra ra 0x574, 4) := by decide
theorem pv_at_8be : fetchRel p384VerifyPrehashCode 0x8BE = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x90, 4) := by decide
theorem pv_at_8c2 : fetchRel p384VerifyPrehashCode 0x8C2 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFF70, 4) := by decide
theorem pv_at_8c6 : fetchRel p384VerifyPrehashCode 0x8C6 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFC8, 2) := by decide
theorem pv_at_8c8 : fetchRel p384VerifyPrehashCode 0x8C8 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xC0, 4) := by decide
theorem pv_at_8cc : fetchRel p384VerifyPrehashCode 0x8CC = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_8ce : fetchRel p384VerifyPrehashCode 0x8CE = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_8d2 : fetchRel p384VerifyPrehashCode 0x8D2 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_8d4 : fetchRel p384VerifyPrehashCode 0x8D4 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_8d8 : fetchRel p384VerifyPrehashCode 0x8D8 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_8dc : fetchRel p384VerifyPrehashCode 0x8DC = some (.aluImm .add a2 x0 0x480, 4) := by decide
theorem pv_at_8e0 : fetchRel p384VerifyPrehashCode 0x8E0 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_8e4 : fetchRel p384VerifyPrehashCode 0x8E4 = some (.jalr ra ra 0xFFFFFD50, 4) := by decide
theorem pv_at_8e8 : fetchRel p384VerifyPrehashCode 0x8E8 = some (.alu .mul a0 (19 : Fin 32) (21 : Fin 32), 4) := by decide
theorem pv_at_8ec : fetchRel p384VerifyPrehashCode 0x8EC = some (.alu .add a0 a0 (22 : Fin 32), 2) := by decide
theorem pv_at_8ee : fetchRel p384VerifyPrehashCode 0x8EE = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_8f0 : fetchRel p384VerifyPrehashCode 0x8F0 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_8f4 : fetchRel p384VerifyPrehashCode 0x8F4 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_8f6 : fetchRel p384VerifyPrehashCode 0x8F6 = some (.aluImm .add a2 x0 0x480, 4) := by decide
theorem pv_at_8fa : fetchRel p384VerifyPrehashCode 0x8FA = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_8fe : fetchRel p384VerifyPrehashCode 0x8FE = some (.jalr ra ra 0xFFFFFD36, 4) := by decide
theorem pv_at_902 : fetchRel p384VerifyPrehashCode 0x902 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1, 2) := by decide
theorem pv_at_904 : fetchRel p384VerifyPrehashCode 0x904 = some (.branch .bne (19 : Fin 32) (20 : Fin 32) 0xFFFFFEF0, 4) := by decide
theorem pv_at_908 : fetchRel p384VerifyPrehashCode 0x908 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_90a : fetchRel p384VerifyPrehashCode 0x90A = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_90e : fetchRel p384VerifyPrehashCode 0x90E = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_910 : fetchRel p384VerifyPrehashCode 0x910 = some (.aluImm .add a1 sp 0x270, 2) := by decide
theorem pv_at_912 : fetchRel p384VerifyPrehashCode 0x912 = some (.aluImm .add a2 x0 0x180, 4) := by decide
theorem pv_at_916 : fetchRel p384VerifyPrehashCode 0x916 = some (.lui a3 0x1000, 2) := by decide
theorem pv_at_918 : fetchRel p384VerifyPrehashCode 0x918 = some (.aluImm .add a3 a3 0x7A4, 4) := by decide
theorem pv_at_91c : fetchRel p384VerifyPrehashCode 0x91C = some (.alu .add (21 : Fin 32) sp a3, 4) := by decide
theorem pv_at_920 : fetchRel p384VerifyPrehashCode 0x920 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_924 : fetchRel p384VerifyPrehashCode 0x924 = some (.jalr ra ra 0xFFFFFD10, 4) := by decide
theorem pv_at_928 : fetchRel p384VerifyPrehashCode 0x928 = some (.aluImm .add (9 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_92a : fetchRel p384VerifyPrehashCode 0x92A = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_92c : fetchRel p384VerifyPrehashCode 0x92C = some (.aluImm .add a0 a0 0x298, 4) := by decide
theorem pv_at_930 : fetchRel p384VerifyPrehashCode 0x930 = some (.alu .add (19 : Fin 32) sp a0, 4) := by decide
theorem pv_at_934 : fetchRel p384VerifyPrehashCode 0x934 = some (.aluImm .add (22 : Fin 32) x0 0x2, 2) := by decide
theorem pv_at_936 : fetchRel p384VerifyPrehashCode 0x936 = some (.lui a0 0xE88FE000, 4) := by decide
theorem pv_at_93a : fetchRel p384VerifyPrehashCode 0x93A = some (.lui (18 : Fin 32) 0x3FCC5000, 4) := by decide
theorem pv_at_93e : fetchRel p384VerifyPrehashCode 0x93E = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xFFFFFD90, 4) := by decide
theorem pv_at_942 : fetchRel p384VerifyPrehashCode 0x942 = some (.aluImm .add (20 : Fin 32) a0 0xFFFFFC45, 4) := by decide
theorem pv_at_946 : fetchRel p384VerifyPrehashCode 0x946 = some (.aluImm .add (23 : Fin 32) x0 0x188, 4) := by decide
theorem pv_at_94a : fetchRel p384VerifyPrehashCode 0x94A = some (.lui a0 0x2000, 2) := by decide
theorem pv_at_94c : fetchRel p384VerifyPrehashCode 0x94C = some (.aluImm .add a0 a0 0xFFFFF924, 4) := by decide
theorem pv_at_950 : fetchRel p384VerifyPrehashCode 0x950 = some (.alu .add (24 : Fin 32) sp a0, 4) := by decide
theorem pv_at_954 : fetchRel p384VerifyPrehashCode 0x954 = some (.branch .beq (22 : Fin 32) x0 0x122, 4) := by decide
theorem pv_at_958 : fetchRel p384VerifyPrehashCode 0x958 = some (.aluImm .add (8 : Fin 32) (21 : Fin 32) 0x90, 4) := by decide
theorem pv_at_95c : fetchRel p384VerifyPrehashCode 0x95C = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_960 : fetchRel p384VerifyPrehashCode 0x960 = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_964 : fetchRel p384VerifyPrehashCode 0x964 = some (.auipc ra 0x7000, 4) := by decide
theorem pv_at_968 : fetchRel p384VerifyPrehashCode 0x968 = some (.jalr ra ra 0xFFFFFB6E, 4) := by decide
theorem pv_at_96c : fetchRel p384VerifyPrehashCode 0x96C = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_970 : fetchRel p384VerifyPrehashCode 0x970 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_974 : fetchRel p384VerifyPrehashCode 0x974 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_976 : fetchRel p384VerifyPrehashCode 0x976 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_978 : fetchRel p384VerifyPrehashCode 0x978 = some (.alu .add a3 x0 (20 : Fin 32), 2) := by decide
theorem pv_at_97a : fetchRel p384VerifyPrehashCode 0x97A = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_97e : fetchRel p384VerifyPrehashCode 0x97E = some (.jalr ra ra 0x21E, 4) := by decide
theorem pv_at_982 : fetchRel p384VerifyPrehashCode 0x982 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_986 : fetchRel p384VerifyPrehashCode 0x986 = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_98a : fetchRel p384VerifyPrehashCode 0x98A = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_98e : fetchRel p384VerifyPrehashCode 0x98E = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_992 : fetchRel p384VerifyPrehashCode 0x992 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_996 : fetchRel p384VerifyPrehashCode 0x996 = some (.jalr ra ra 0x342, 4) := by decide
theorem pv_at_99a : fetchRel p384VerifyPrehashCode 0x99A = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_99e : fetchRel p384VerifyPrehashCode 0x99E = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_9a2 : fetchRel p384VerifyPrehashCode 0x9A2 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_9a6 : fetchRel p384VerifyPrehashCode 0x9A6 = some (.aluImm .add a1 a1 0x551, 4) := by decide
theorem pv_at_9aa : fetchRel p384VerifyPrehashCode 0x9AA = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_9ae : fetchRel p384VerifyPrehashCode 0x9AE = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_9b2 : fetchRel p384VerifyPrehashCode 0x9B2 = some (.jalr ra ra 0xFFFFFC82, 4) := by decide
theorem pv_at_9b6 : fetchRel p384VerifyPrehashCode 0x9B6 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_9ba : fetchRel p384VerifyPrehashCode 0x9BA = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_9be : fetchRel p384VerifyPrehashCode 0x9BE = some (.aluImm .add a1 x0 0x30, 4) := by decide
theorem pv_at_9c2 : fetchRel p384VerifyPrehashCode 0x9C2 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem pv_at_9c6 : fetchRel p384VerifyPrehashCode 0x9C6 = some (.jalr ra ra 0xFFFFFF30, 4) := by decide
theorem pv_at_9ca : fetchRel p384VerifyPrehashCode 0x9CA = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_9ce : fetchRel p384VerifyPrehashCode 0x9CE = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_9d2 : fetchRel p384VerifyPrehashCode 0x9D2 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_9d6 : fetchRel p384VerifyPrehashCode 0x9D6 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_9da : fetchRel p384VerifyPrehashCode 0x9DA = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_9de : fetchRel p384VerifyPrehashCode 0x9DE = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_9e2 : fetchRel p384VerifyPrehashCode 0x9E2 = some (.jalr ra ra 0xFFFFFC52, 4) := by decide
theorem pv_at_9e6 : fetchRel p384VerifyPrehashCode 0x9E6 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_9ea : fetchRel p384VerifyPrehashCode 0x9EA = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_9ee : fetchRel p384VerifyPrehashCode 0x9EE = some (.aluImm .add a1 x0 0x181, 4) := by decide
theorem pv_at_9f2 : fetchRel p384VerifyPrehashCode 0x9F2 = some (.branch .beq a1 x0 0xC, 2) := by decide
theorem pv_at_9f4 : fetchRel p384VerifyPrehashCode 0x9F4 = some (.store .sb a0 x0 0x0, 4) := by decide
theorem pv_at_9f8 : fetchRel p384VerifyPrehashCode 0x9F8 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem pv_at_9fa : fetchRel p384VerifyPrehashCode 0x9FA = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem pv_at_9fc : fetchRel p384VerifyPrehashCode 0x9FC = some (.branch .bne a1 x0 0xFFFFFFF8, 2) := by decide
theorem pv_at_9fe : fetchRel p384VerifyPrehashCode 0x9FE = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0xC0, 4) := by decide
theorem pv_at_a02 : fetchRel p384VerifyPrehashCode 0xA02 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_a06 : fetchRel p384VerifyPrehashCode 0xA06 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_a0a : fetchRel p384VerifyPrehashCode 0xA0A = some (.aluImm .add a2 x0 0x181, 4) := by decide
theorem pv_at_a0e : fetchRel p384VerifyPrehashCode 0xA0E = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem pv_at_a10 : fetchRel p384VerifyPrehashCode 0xA10 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_a14 : fetchRel p384VerifyPrehashCode 0xA14 = some (.jalr ra ra 0xFFFFFC20, 4) := by decide
theorem pv_at_a18 : fetchRel p384VerifyPrehashCode 0xA18 = some (.aluImm .add a1 x0 0x181, 4) := by decide
theorem pv_at_a1c : fetchRel p384VerifyPrehashCode 0xA1C = some (.aluImm .add a2 sp 0x7FF, 4) := by decide
theorem pv_at_a20 : fetchRel p384VerifyPrehashCode 0xA20 = some (.aluImm .add a2 a2 0x551, 4) := by decide
theorem pv_at_a24 : fetchRel p384VerifyPrehashCode 0xA24 = some (.aluImm .add a3 x0 0x30, 4) := by decide
theorem pv_at_a28 : fetchRel p384VerifyPrehashCode 0xA28 = some (.aluImm .add a4 x0 0x180, 4) := by decide
theorem pv_at_a2c : fetchRel p384VerifyPrehashCode 0xA2C = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem pv_at_a2e : fetchRel p384VerifyPrehashCode 0xA2E = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem pv_at_a32 : fetchRel p384VerifyPrehashCode 0xA32 = some (.jalr ra ra 0xFFFFFEE8, 4) := by decide
theorem pv_at_a36 : fetchRel p384VerifyPrehashCode 0xA36 = some (.store .sw (25 : Fin 32) a0 0x514, 4) := by decide
theorem pv_at_a3a : fetchRel p384VerifyPrehashCode 0xA3A = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_a3e : fetchRel p384VerifyPrehashCode 0xA3E = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_a42 : fetchRel p384VerifyPrehashCode 0xA42 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_a44 : fetchRel p384VerifyPrehashCode 0xA44 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_a48 : fetchRel p384VerifyPrehashCode 0xA48 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_a4a : fetchRel p384VerifyPrehashCode 0xA4A = some (.aluImm .add a2 x0 0x188, 4) := by decide
theorem pv_at_a4e : fetchRel p384VerifyPrehashCode 0xA4E = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_a52 : fetchRel p384VerifyPrehashCode 0xA52 = some (.jalr ra ra 0xFFFFFBE2, 4) := by decide
theorem pv_at_a56 : fetchRel p384VerifyPrehashCode 0xA56 = some (.alu .mul a0 (9 : Fin 32) (23 : Fin 32), 4) := by decide
theorem pv_at_a5a : fetchRel p384VerifyPrehashCode 0xA5A = some (.alu .add a0 a0 (24 : Fin 32), 2) := by decide
theorem pv_at_a5c : fetchRel p384VerifyPrehashCode 0xA5C = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_a60 : fetchRel p384VerifyPrehashCode 0xA60 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_a64 : fetchRel p384VerifyPrehashCode 0xA64 = some (.aluImm .add a2 x0 0x188, 4) := by decide
theorem pv_at_a68 : fetchRel p384VerifyPrehashCode 0xA68 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_a6c : fetchRel p384VerifyPrehashCode 0xA6C = some (.jalr ra ra 0xFFFFFBC8, 4) := by decide
theorem pv_at_a70 : fetchRel p384VerifyPrehashCode 0xA70 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1, 2) := by decide
theorem pv_at_a72 : fetchRel p384VerifyPrehashCode 0xA72 = some (.branch .bne (9 : Fin 32) (22 : Fin 32) 0xFFFFFEE6, 4) := by decide
theorem pv_at_a76 : fetchRel p384VerifyPrehashCode 0xA76 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_a78 : fetchRel p384VerifyPrehashCode 0xA78 = some (.aluImm .add a0 a0 0x744, 4) := by decide
theorem pv_at_a7c : fetchRel p384VerifyPrehashCode 0xA7C = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_a7e : fetchRel p384VerifyPrehashCode 0xA7E = some (.load .lw (9 : Fin 32) a0 0x1E0, 4) := by decide
theorem pv_at_a82 : fetchRel p384VerifyPrehashCode 0xA82 = some (.load .lw a0 a0 0x368, 4) := by decide
theorem pv_at_a86 : fetchRel p384VerifyPrehashCode 0xA86 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pv_at_a88 : fetchRel p384VerifyPrehashCode 0xA88 = some (.aluImm .and a1 a1 0x1, 2) := by decide
theorem pv_at_a8a : fetchRel p384VerifyPrehashCode 0xA8A = some (.branch .bne a1 x0 0xC, 2) := by decide
theorem pv_at_a8c : fetchRel p384VerifyPrehashCode 0xA8C = some (.branch .bltu a0 (9 : Fin 32) 0x6, 4) := by decide
theorem pv_at_a90 : fetchRel p384VerifyPrehashCode 0xA90 = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem pv_at_a92 : fetchRel p384VerifyPrehashCode 0xA92 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem pv_at_a94 : fetchRel p384VerifyPrehashCode 0xA94 = some (.jal x0 0xFFFFFFF4, 2) := by decide
theorem pv_at_a96 : fetchRel p384VerifyPrehashCode 0xA96 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem pv_at_a9a : fetchRel p384VerifyPrehashCode 0xA9A = some (.aluImm .add a1 a1 0x340, 4) := by decide
theorem pv_at_a9e : fetchRel p384VerifyPrehashCode 0xA9E = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_aa2 : fetchRel p384VerifyPrehashCode 0xAA2 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_aa6 : fetchRel p384VerifyPrehashCode 0xAA6 = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem pv_at_aaa : fetchRel p384VerifyPrehashCode 0xAAA = some (.aluImm .add (20 : Fin 32) x0 0x90, 4) := by decide
theorem pv_at_aae : fetchRel p384VerifyPrehashCode 0xAAE = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_ab2 : fetchRel p384VerifyPrehashCode 0xAB2 = some (.jalr ra ra 0xFFFFFB82, 4) := by decide
theorem pv_at_ab6 : fetchRel p384VerifyPrehashCode 0xAB6 = some (.aluImm .add (21 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_ab8 : fetchRel p384VerifyPrehashCode 0xAB8 = some (.lui a0 0x2000, 2) := by decide
theorem pv_at_aba : fetchRel p384VerifyPrehashCode 0xABA = some (.aluImm .add a0 a0 0xFFFFF924, 4) := by decide
theorem pv_at_abe : fetchRel p384VerifyPrehashCode 0xABE = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_ac0 : fetchRel p384VerifyPrehashCode 0xAC0 = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem pv_at_ac2 : fetchRel p384VerifyPrehashCode 0xAC2 = some (.aluImm .add (23 : Fin 32) a0 0x3, 4) := by decide
theorem pv_at_ac6 : fetchRel p384VerifyPrehashCode 0xAC6 = some (.aluImm .add (22 : Fin 32) x0 0x188, 4) := by decide
theorem pv_at_aca : fetchRel p384VerifyPrehashCode 0xACA = some (.aluImm .add (8 : Fin 32) x0 0x2, 2) := by decide
theorem pv_at_acc : fetchRel p384VerifyPrehashCode 0xACC = some (.aluImm .add (24 : Fin 32) x0 0x181, 4) := by decide
theorem pv_at_ad0 : fetchRel p384VerifyPrehashCode 0xAD0 = some (.aluImm .add (25 : Fin 32) x0 0x480, 4) := by decide
theorem pv_at_ad4 : fetchRel p384VerifyPrehashCode 0xAD4 = some (.aluImm .add (26 : Fin 32) sp 0x450, 4) := by decide
theorem pv_at_ad8 : fetchRel p384VerifyPrehashCode 0xAD8 = some (.aluImm .add (27 : Fin 32) x0 0x10, 2) := by decide
theorem pv_at_ada : fetchRel p384VerifyPrehashCode 0xADA = some (.branch .beq (9 : Fin 32) x0 0x114, 4) := by decide
theorem pv_at_ade : fetchRel p384VerifyPrehashCode 0xADE = some (.aluImm .and a0 (21 : Fin 32) 0x1, 4) := by decide
theorem pv_at_ae2 : fetchRel p384VerifyPrehashCode 0xAE2 = some (.branch .beq a0 x0 0x36, 2) := by decide
theorem pv_at_ae4 : fetchRel p384VerifyPrehashCode 0xAE4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_ae6 : fetchRel p384VerifyPrehashCode 0xAE6 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_aea : fetchRel p384VerifyPrehashCode 0xAEA = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_aec : fetchRel p384VerifyPrehashCode 0xAEC = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_af0 : fetchRel p384VerifyPrehashCode 0xAF0 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_af4 : fetchRel p384VerifyPrehashCode 0xAF4 = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem pv_at_af8 : fetchRel p384VerifyPrehashCode 0xAF8 = some (.jalr ra ra 0xD8, 4) := by decide
theorem pv_at_afc : fetchRel p384VerifyPrehashCode 0xAFC = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_b00 : fetchRel p384VerifyPrehashCode 0xB00 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_b04 : fetchRel p384VerifyPrehashCode 0xB04 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_b06 : fetchRel p384VerifyPrehashCode 0xB06 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_b0a : fetchRel p384VerifyPrehashCode 0xB0A = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_b0c : fetchRel p384VerifyPrehashCode 0xB0C = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem pv_at_b10 : fetchRel p384VerifyPrehashCode 0xB10 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_b14 : fetchRel p384VerifyPrehashCode 0xB14 = some (.jalr ra ra 0xFFFFFB20, 4) := by decide
theorem pv_at_b18 : fetchRel p384VerifyPrehashCode 0xB18 = some (.aluImm .add (18 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_b1a : fetchRel p384VerifyPrehashCode 0xB1A = some (.aluImm .add (19 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 4) := by decide
theorem pv_at_b1e : fetchRel p384VerifyPrehashCode 0xB1E = some (.alu .mul a0 (18 : Fin 32) (22 : Fin 32), 4) := by decide
theorem pv_at_b22 : fetchRel p384VerifyPrehashCode 0xB22 = some (.alu .add a0 a0 (23 : Fin 32), 2) := by decide
theorem pv_at_b24 : fetchRel p384VerifyPrehashCode 0xB24 = some (.branch .beq (18 : Fin 32) (8 : Fin 32) 0xC2, 4) := by decide
theorem pv_at_b28 : fetchRel p384VerifyPrehashCode 0xB28 = some (.branch .bltu (24 : Fin 32) (9 : Fin 32) 0xA, 4) := by decide
theorem pv_at_b2c : fetchRel p384VerifyPrehashCode 0xB2C = some (.load .lbu a2 a0 0x0, 4) := by decide
theorem pv_at_b30 : fetchRel p384VerifyPrehashCode 0xB30 = some (.branch .bne a2 x0 0xE, 2) := by decide
theorem pv_at_b32 : fetchRel p384VerifyPrehashCode 0xB32 = some (.aluImm .add a0 a0 0x188, 4) := by decide
theorem pv_at_b36 : fetchRel p384VerifyPrehashCode 0xB36 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1, 2) := by decide
theorem pv_at_b38 : fetchRel p384VerifyPrehashCode 0xB38 = some (.branch .beq (18 : Fin 32) (8 : Fin 32) 0xAE, 4) := by decide
theorem pv_at_b3c : fetchRel p384VerifyPrehashCode 0xB3C = some (.jal x0 0xFFFFFFEC, 2) := by decide
theorem pv_at_b3e : fetchRel p384VerifyPrehashCode 0xB3E = some (.alu .mul a1 (18 : Fin 32) (25 : Fin 32), 4) := by decide
theorem pv_at_b42 : fetchRel p384VerifyPrehashCode 0xB42 = some (.aluImm .sll a0 a2 0x18, 4) := by decide
theorem pv_at_b46 : fetchRel p384VerifyPrehashCode 0xB46 = some (.aluImm .sra a0 a0 0x18, 2) := by decide
theorem pv_at_b48 : fetchRel p384VerifyPrehashCode 0xB48 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1, 2) := by decide
theorem pv_at_b4a : fetchRel p384VerifyPrehashCode 0xB4A = some (.alu .add a1 a1 (26 : Fin 32), 2) := by decide
theorem pv_at_b4c : fetchRel p384VerifyPrehashCode 0xB4C = some (.branch .bge x0 a0 0x1C, 4) := by decide
theorem pv_at_b50 : fetchRel p384VerifyPrehashCode 0xB50 = some (.aluImm .srl a0 a2 0x1, 4) := by decide
theorem pv_at_b54 : fetchRel p384VerifyPrehashCode 0xB54 = some (.branch .bgeu a2 (27 : Fin 32) 0x68C, 4) := by decide
theorem pv_at_b58 : fetchRel p384VerifyPrehashCode 0xB58 = some (.alu .mul a0 a0 (20 : Fin 32), 4) := by decide
theorem pv_at_b5c : fetchRel p384VerifyPrehashCode 0xB5C = some (.alu .add a1 a1 a0, 2) := by decide
theorem pv_at_b5e : fetchRel p384VerifyPrehashCode 0xB5E = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_b62 : fetchRel p384VerifyPrehashCode 0xB62 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_b66 : fetchRel p384VerifyPrehashCode 0xB66 = some (.jal x0 0x74, 2) := by decide
theorem pv_at_b68 : fetchRel p384VerifyPrehashCode 0xB68 = some (.alu .sub a0 x0 a2, 4) := by decide
theorem pv_at_b6c : fetchRel p384VerifyPrehashCode 0xB6C = some (.aluImm .sll a0 a0 0x18, 2) := by decide
theorem pv_at_b6e : fetchRel p384VerifyPrehashCode 0xB6E = some (.aluImm .sra a0 a0 0x18, 2) := by decide
theorem pv_at_b70 : fetchRel p384VerifyPrehashCode 0xB70 = some (.alu .div a0 a0 (8 : Fin 32), 4) := by decide
theorem pv_at_b74 : fetchRel p384VerifyPrehashCode 0xB74 = some (.aluImm .and a2 a0 0xFF, 4) := by decide
theorem pv_at_b78 : fetchRel p384VerifyPrehashCode 0xB78 = some (.aluImm .sll a0 a0 0x18, 2) := by decide
theorem pv_at_b7a : fetchRel p384VerifyPrehashCode 0xB7A = some (.aluImm .sra a0 a0 0x18, 2) := by decide
theorem pv_at_b7c : fetchRel p384VerifyPrehashCode 0xB7C = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem pv_at_b7e : fetchRel p384VerifyPrehashCode 0xB7E = some (.branch .bgeu a2 a3 0x662, 4) := by decide
theorem pv_at_b82 : fetchRel p384VerifyPrehashCode 0xB82 = some (.alu .mul (21 : Fin 32) a0 (20 : Fin 32), 4) := by decide
theorem pv_at_b86 : fetchRel p384VerifyPrehashCode 0xB86 = some (.alu .add (21 : Fin 32) (21 : Fin 32) a1, 2) := by decide
theorem pv_at_b88 : fetchRel p384VerifyPrehashCode 0xB88 = some (.aluImm .add a1 (21 : Fin 32) 0x30, 4) := by decide
theorem pv_at_b8c : fetchRel p384VerifyPrehashCode 0xB8C = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_b8e : fetchRel p384VerifyPrehashCode 0xB8E = some (.aluImm .add a0 a0 0x2C4, 4) := by decide
theorem pv_at_b92 : fetchRel p384VerifyPrehashCode 0xB92 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_b94 : fetchRel p384VerifyPrehashCode 0xB94 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem pv_at_b98 : fetchRel p384VerifyPrehashCode 0xB98 = some (.jalr ra ra 0xFFFFFCB8, 4) := by decide
theorem pv_at_b9c : fetchRel p384VerifyPrehashCode 0xB9C = some (.aluImm .add a1 (21 : Fin 32) 0x60, 4) := by decide
theorem pv_at_ba0 : fetchRel p384VerifyPrehashCode 0xBA0 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_ba4 : fetchRel p384VerifyPrehashCode 0xBA4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_ba6 : fetchRel p384VerifyPrehashCode 0xBA6 = some (.aluImm .add a0 a0 0x2F4, 4) := by decide
theorem pv_at_baa : fetchRel p384VerifyPrehashCode 0xBAA = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_bac : fetchRel p384VerifyPrehashCode 0xBAC = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_bb0 : fetchRel p384VerifyPrehashCode 0xBB0 = some (.jalr ra ra 0xFFFFFA84, 4) := by decide
theorem pv_at_bb4 : fetchRel p384VerifyPrehashCode 0xBB4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_bb6 : fetchRel p384VerifyPrehashCode 0xBB6 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_bba : fetchRel p384VerifyPrehashCode 0xBBA = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_bbc : fetchRel p384VerifyPrehashCode 0xBBC = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_bc0 : fetchRel p384VerifyPrehashCode 0xBC0 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem pv_at_bc2 : fetchRel p384VerifyPrehashCode 0xBC2 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_bc6 : fetchRel p384VerifyPrehashCode 0xBC6 = some (.jalr ra ra 0xFFFFFA6E, 4) := by decide
theorem pv_at_bca : fetchRel p384VerifyPrehashCode 0xBCA = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_bce : fetchRel p384VerifyPrehashCode 0xBCE = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_bd2 : fetchRel p384VerifyPrehashCode 0xBD2 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_bd4 : fetchRel p384VerifyPrehashCode 0xBD4 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_bd8 : fetchRel p384VerifyPrehashCode 0xBD8 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_bda : fetchRel p384VerifyPrehashCode 0xBDA = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem pv_at_bde : fetchRel p384VerifyPrehashCode 0xBDE = some (.jalr ra ra 0x250, 4) := by decide
theorem pv_at_be2 : fetchRel p384VerifyPrehashCode 0xBE2 = some (.aluImm .add (21 : Fin 32) x0 0x1, 2) := by decide
theorem pv_at_be4 : fetchRel p384VerifyPrehashCode 0xBE4 = some (.jal x0 0xFFFFFF3A, 2) := by decide
theorem pv_at_be6 : fetchRel p384VerifyPrehashCode 0xBE6 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem pv_at_be8 : fetchRel p384VerifyPrehashCode 0xBE8 = some (.alu .add (9 : Fin 32) x0 (19 : Fin 32), 2) := by decide
theorem pv_at_bea : fetchRel p384VerifyPrehashCode 0xBEA = some (.branch .bne (19 : Fin 32) x0 0xFFFFFEF4, 4) := by decide
theorem pv_at_bee : fetchRel p384VerifyPrehashCode 0xBEE = some (.lui a0 0x2000, 2) := by decide
theorem pv_at_bf0 : fetchRel p384VerifyPrehashCode 0xBF0 = some (.aluImm .add a0 a0 0xFFFFFC88, 4) := by decide
theorem pv_at_bf4 : fetchRel p384VerifyPrehashCode 0xBF4 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_bf6 : fetchRel p384VerifyPrehashCode 0xBF6 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_bfa : fetchRel p384VerifyPrehashCode 0xBFA = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_bfe : fetchRel p384VerifyPrehashCode 0xBFE = some (.aluImm .add a2 x0 0x90, 4) := by decide
theorem pv_at_c02 : fetchRel p384VerifyPrehashCode 0xC02 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_c06 : fetchRel p384VerifyPrehashCode 0xC06 = some (.jalr ra ra 0xFFFFFA2E, 4) := by decide
theorem pv_at_c0a : fetchRel p384VerifyPrehashCode 0xC0A = some (.lui a0 0x2000, 2) := by decide
theorem pv_at_c0c : fetchRel p384VerifyPrehashCode 0xC0C = some (.aluImm .add a0 a0 0xFFFFFCE8, 4) := by decide
theorem pv_at_c10 : fetchRel p384VerifyPrehashCode 0xC10 = some (.alu .add (18 : Fin 32) sp a0, 4) := by decide
theorem pv_at_c14 : fetchRel p384VerifyPrehashCode 0xC14 = some (.lui (9 : Fin 32) 0x3FCC5000, 4) := by decide
theorem pv_at_c18 : fetchRel p384VerifyPrehashCode 0xC18 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFCF4, 4) := by decide
theorem pv_at_c1c : fetchRel p384VerifyPrehashCode 0xC1C = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_c20 : fetchRel p384VerifyPrehashCode 0xC20 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_c24 : fetchRel p384VerifyPrehashCode 0xC24 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_c28 : fetchRel p384VerifyPrehashCode 0xC28 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_c2a : fetchRel p384VerifyPrehashCode 0xC2A = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_c2e : fetchRel p384VerifyPrehashCode 0xC2E = some (.jalr ra ra 0xFFFFFA06, 4) := by decide
theorem pv_at_c32 : fetchRel p384VerifyPrehashCode 0xC32 = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem pv_at_c34 : fetchRel p384VerifyPrehashCode 0xC34 = some (.aluImm .add a1 x0 0xFFFFFFFE, 2) := by decide
theorem pv_at_c36 : fetchRel p384VerifyPrehashCode 0xC36 = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) := by decide
theorem pv_at_c3a : fetchRel p384VerifyPrehashCode 0xC3A = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x581, 4) := by decide
theorem pv_at_c3e : fetchRel p384VerifyPrehashCode 0xC3E = some (.store .sw (24 : Fin 32) a0 0xF0, 4) := by decide
theorem pv_at_c42 : fetchRel p384VerifyPrehashCode 0xC42 = some (.store .sw (24 : Fin 32) a1 0xF4, 4) := by decide
theorem pv_at_c46 : fetchRel p384VerifyPrehashCode 0xC46 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_c4a : fetchRel p384VerifyPrehashCode 0xC4A = some (.aluImm .add a0 a0 0x641, 4) := by decide
theorem pv_at_c4e : fetchRel p384VerifyPrehashCode 0xC4E = some (.aluImm .add (8 : Fin 32) (9 : Fin 32) 0x60, 4) := by decide
theorem pv_at_c52 : fetchRel p384VerifyPrehashCode 0xC52 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_c56 : fetchRel p384VerifyPrehashCode 0xC56 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_c58 : fetchRel p384VerifyPrehashCode 0xC58 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_c5c : fetchRel p384VerifyPrehashCode 0xC5C = some (.jalr ra ra 0xFFFFF9D8, 4) := by decide
theorem pv_at_c60 : fetchRel p384VerifyPrehashCode 0xC60 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_c62 : fetchRel p384VerifyPrehashCode 0xC62 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_c66 : fetchRel p384VerifyPrehashCode 0xC66 = some (.jalr ra ra 0xFFFFFC96, 4) := by decide
theorem pv_at_c6a : fetchRel p384VerifyPrehashCode 0xC6A = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem pv_at_c6e : fetchRel p384VerifyPrehashCode 0xC6E = some (.store .sw sp a0 0x10, 2) := by decide
theorem pv_at_c70 : fetchRel p384VerifyPrehashCode 0xC70 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_c72 : fetchRel p384VerifyPrehashCode 0xC72 = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_c76 : fetchRel p384VerifyPrehashCode 0xC76 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_c78 : fetchRel p384VerifyPrehashCode 0xC78 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_c7c : fetchRel p384VerifyPrehashCode 0xC7C = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_c7e : fetchRel p384VerifyPrehashCode 0xC7E = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_c82 : fetchRel p384VerifyPrehashCode 0xC82 = some (.jalr ra ra 0xFFFFF9B2, 4) := by decide
theorem pv_at_c86 : fetchRel p384VerifyPrehashCode 0xC86 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_c88 : fetchRel p384VerifyPrehashCode 0xC88 = some (.aluImm .add a0 a0 0x744, 4) := by decide
theorem pv_at_c8c : fetchRel p384VerifyPrehashCode 0xC8C = some (.alu .add (9 : Fin 32) sp a0, 4) := by decide
theorem pv_at_c90 : fetchRel p384VerifyPrehashCode 0xC90 = some (.store .sb (9 : Fin 32) x0 0x0, 4) := by decide
theorem pv_at_c94 : fetchRel p384VerifyPrehashCode 0xC94 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_c98 : fetchRel p384VerifyPrehashCode 0xC98 = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_c9c : fetchRel p384VerifyPrehashCode 0xC9C = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_ca0 : fetchRel p384VerifyPrehashCode 0xCA0 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_ca2 : fetchRel p384VerifyPrehashCode 0xCA2 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_ca6 : fetchRel p384VerifyPrehashCode 0xCA6 = some (.jalr ra ra 0xFFFFF98E, 4) := by decide
theorem pv_at_caa : fetchRel p384VerifyPrehashCode 0xCAA = some (.alu .add (19 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem pv_at_cac : fetchRel p384VerifyPrehashCode 0xCAC = some (.store .sb (24 : Fin 32) x0 0x0, 4) := by decide
theorem pv_at_cb0 : fetchRel p384VerifyPrehashCode 0xCB0 = some (.aluImm .add a0 sp 0x270, 2) := by decide
theorem pv_at_cb2 : fetchRel p384VerifyPrehashCode 0xCB2 = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_cb6 : fetchRel p384VerifyPrehashCode 0xCB6 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pv_at_cb8 : fetchRel p384VerifyPrehashCode 0xCB8 = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_cbc : fetchRel p384VerifyPrehashCode 0xCBC = some (.jalr ra ra 0xFFFFF910, 4) := by decide
theorem pv_at_cc0 : fetchRel p384VerifyPrehashCode 0xCC0 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_cc2 : fetchRel p384VerifyPrehashCode 0xCC2 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_cc6 : fetchRel p384VerifyPrehashCode 0xCC6 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_cc8 : fetchRel p384VerifyPrehashCode 0xCC8 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_ccc : fetchRel p384VerifyPrehashCode 0xCCC = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_cce : fetchRel p384VerifyPrehashCode 0xCCE = some (.auipc ra 0xE000, 4) := by decide
theorem pv_at_cd2 : fetchRel p384VerifyPrehashCode 0xCD2 = some (.jalr ra ra 0xFFFFF962, 4) := by decide
theorem pv_at_cd6 : fetchRel p384VerifyPrehashCode 0xCD6 = some (.aluImm .add (24 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_cd8 : fetchRel p384VerifyPrehashCode 0xCD8 = some (.store .sb (9 : Fin 32) x0 0x90, 4) := by decide
theorem pv_at_cdc : fetchRel p384VerifyPrehashCode 0xCDC = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem pv_at_cde : fetchRel p384VerifyPrehashCode 0xCDE = some (.store .sw sp a0 0x40, 2) := by decide
theorem pv_at_ce0 : fetchRel p384VerifyPrehashCode 0xCE0 = some (.aluImm .add a0 x0 0x376, 4) := by decide
theorem pv_at_ce4 : fetchRel p384VerifyPrehashCode 0xCE4 = some (.branch .beq a0 x0 0x318, 4) := by decide
theorem pv_at_ce8 : fetchRel p384VerifyPrehashCode 0xCE8 = some (.store .sw sp a0 0x18, 2) := by decide
theorem pv_at_cea : fetchRel p384VerifyPrehashCode 0xCEA = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_cee : fetchRel p384VerifyPrehashCode 0xCEE = some (.jalr ra ra 0xFFFFFD4A, 4) := by decide
theorem pv_at_cf2 : fetchRel p384VerifyPrehashCode 0xCF2 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem pv_at_cf4 : fetchRel p384VerifyPrehashCode 0xCF4 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_cf6 : fetchRel p384VerifyPrehashCode 0xCF6 = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_cfa : fetchRel p384VerifyPrehashCode 0xCFA = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_cfc : fetchRel p384VerifyPrehashCode 0xCFC = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_d00 : fetchRel p384VerifyPrehashCode 0xD00 = some (.jalr ra ra 0xFFFFFCAE, 4) := by decide
theorem pv_at_d04 : fetchRel p384VerifyPrehashCode 0xD04 = some (.store .sw sp a0 0x50, 2) := by decide
theorem pv_at_d06 : fetchRel p384VerifyPrehashCode 0xD06 = some (.store .sw sp a1 0x48, 2) := by decide
theorem pv_at_d08 : fetchRel p384VerifyPrehashCode 0xD08 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_d0c : fetchRel p384VerifyPrehashCode 0xD0C = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_d10 : fetchRel p384VerifyPrehashCode 0xD10 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_d14 : fetchRel p384VerifyPrehashCode 0xD14 = some (.jalr ra ra 0xFFFFFC9A, 4) := by decide
theorem pv_at_d18 : fetchRel p384VerifyPrehashCode 0xD18 = some (.store .sw sp a0 0x44, 2) := by decide
theorem pv_at_d1a : fetchRel p384VerifyPrehashCode 0xD1A = some (.store .sw sp a1 0x4C, 2) := by decide
theorem pv_at_d1c : fetchRel p384VerifyPrehashCode 0xD1C = some (.aluImm .add a3 x0 0x0, 2) := by decide
theorem pv_at_d1e : fetchRel p384VerifyPrehashCode 0xD1E = some (.store .sw sp x0 0x54, 2) := by decide
theorem pv_at_d20 : fetchRel p384VerifyPrehashCode 0xD20 = some (.aluImm .add (18 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_d22 : fetchRel p384VerifyPrehashCode 0xD22 = some (.aluImm .add (20 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_d24 : fetchRel p384VerifyPrehashCode 0xD24 = some (.aluImm .add (25 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_d26 : fetchRel p384VerifyPrehashCode 0xD26 = some (.aluImm .add (26 : Fin 32) x0 0x0, 2) := by decide
theorem pv_at_d28 : fetchRel p384VerifyPrehashCode 0xD28 = some (.aluImm .add (22 : Fin 32) x0 0x1, 2) := by decide
theorem pv_at_d2a : fetchRel p384VerifyPrehashCode 0xD2A = some (.aluImm .add (23 : Fin 32) x0 0x1, 2) := by decide
theorem pv_at_d2c : fetchRel p384VerifyPrehashCode 0xD2C = some (.store .sw sp (8 : Fin 32) 0x14, 2) := by decide
theorem pv_at_d2e : fetchRel p384VerifyPrehashCode 0xD2E = some (.alu .add a4 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_d30 : fetchRel p384VerifyPrehashCode 0xD30 = some (.alu .add (8 : Fin 32) x0 (19 : Fin 32), 2) := by decide
theorem pv_at_d32 : fetchRel p384VerifyPrehashCode 0xD32 = some (.branch .beq a4 x0 0x1D0, 4) := by decide
theorem pv_at_d36 : fetchRel p384VerifyPrehashCode 0xD36 = some (.load .lw (21 : Fin 32) sp 0x44, 2) := by decide
theorem pv_at_d38 : fetchRel p384VerifyPrehashCode 0xD38 = some (.aluImm .and (27 : Fin 32) (21 : Fin 32) 0x1, 4) := by decide
theorem pv_at_d3c : fetchRel p384VerifyPrehashCode 0xD3C = some (.lui a5 0x80000000, 4) := by decide
theorem pv_at_d40 : fetchRel p384VerifyPrehashCode 0xD40 = some (.alu .xor a0 (24 : Fin 32) a5, 4) := by decide
theorem pv_at_d44 : fetchRel p384VerifyPrehashCode 0xD44 = some (.store .sb (8 : Fin 32) (27 : Fin 32) 0x514, 4) := by decide
theorem pv_at_d48 : fetchRel p384VerifyPrehashCode 0xD48 = some (.alu .add (19 : Fin 32) x0 (20 : Fin 32), 2) := by decide
theorem pv_at_d4a : fetchRel p384VerifyPrehashCode 0xD4A = some (.load .lw (9 : Fin 32) sp 0x40, 2) := by decide
theorem pv_at_d4c : fetchRel p384VerifyPrehashCode 0xD4C = some (.store .sw sp (25 : Fin 32) 0x30, 2) := by decide
theorem pv_at_d4e : fetchRel p384VerifyPrehashCode 0xD4E = some (.alu .sltu a2 x0 (9 : Fin 32), 4) := by decide
theorem pv_at_d52 : fetchRel p384VerifyPrehashCode 0xD52 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_d54 : fetchRel p384VerifyPrehashCode 0xD54 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_d58 : fetchRel p384VerifyPrehashCode 0xD58 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_d5a : fetchRel p384VerifyPrehashCode 0xD5A = some (.aluImm .add a1 (9 : Fin 32) 0x2, 4) := by decide
theorem pv_at_d5e : fetchRel p384VerifyPrehashCode 0xD5E = some (.store .sw sp a3 0x28, 2) := by decide
theorem pv_at_d60 : fetchRel p384VerifyPrehashCode 0xD60 = some (.store .sw sp a4 0x3C, 2) := by decide
theorem pv_at_d62 : fetchRel p384VerifyPrehashCode 0xD62 = some (.load .lbu a4 (8 : Fin 32) 0x514, 4) := by decide
theorem pv_at_d66 : fetchRel p384VerifyPrehashCode 0xD66 = some (.aluImm .add a6 x0 0x2, 2) := by decide
theorem pv_at_d68 : fetchRel p384VerifyPrehashCode 0xD68 = some (.alu .sub a3 a6 (9 : Fin 32), 4) := by decide
theorem pv_at_d6c : fetchRel p384VerifyPrehashCode 0xD6C = some (.alu .sub a5 a5 a0, 2) := by decide
theorem pv_at_d6e : fetchRel p384VerifyPrehashCode 0xD6E = some (.alu .sub a5 a5 a2, 2) := by decide
theorem pv_at_d70 : fetchRel p384VerifyPrehashCode 0xD70 = some (.alu .sltu a2 a1 (9 : Fin 32), 4) := by decide
theorem pv_at_d74 : fetchRel p384VerifyPrehashCode 0xD74 = some (.alu .add a2 a2 (24 : Fin 32), 2) := by decide
theorem pv_at_d76 : fetchRel p384VerifyPrehashCode 0xD76 = some (.alu .and a0 a0 a5, 2) := by decide
theorem pv_at_d78 : fetchRel p384VerifyPrehashCode 0xD78 = some (.aluImm .srl a5 a0 0x1F, 4) := by decide
theorem pv_at_d7c : fetchRel p384VerifyPrehashCode 0xD7C = some (.store .sw sp a5 0x24, 2) := by decide
theorem pv_at_d7e : fetchRel p384VerifyPrehashCode 0xD7E = some (.aluImm .sltu a0 a4 0x1, 4) := by decide
theorem pv_at_d82 : fetchRel p384VerifyPrehashCode 0xD82 = some (.alu .sub a4 x0 a4, 4) := by decide
theorem pv_at_d86 : fetchRel p384VerifyPrehashCode 0xD86 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem pv_at_d88 : fetchRel p384VerifyPrehashCode 0xD88 = some (.store .sw sp (18 : Fin 32) 0x1C, 2) := by decide
theorem pv_at_d8a : fetchRel p384VerifyPrehashCode 0xD8A = some (.alu .add (18 : Fin 32) x0 (22 : Fin 32), 2) := by decide
theorem pv_at_d8c : fetchRel p384VerifyPrehashCode 0xD8C = some (.load .lw (22 : Fin 32) sp 0x48, 2) := by decide
theorem pv_at_d8e : fetchRel p384VerifyPrehashCode 0xD8E = some (.load .lw (20 : Fin 32) sp 0x50, 2) := by decide
theorem pv_at_d90 : fetchRel p384VerifyPrehashCode 0xD90 = some (.alu .and (8 : Fin 32) (20 : Fin 32) a4, 4) := by decide
theorem pv_at_d94 : fetchRel p384VerifyPrehashCode 0xD94 = some (.alu .sltu a4 a6 (9 : Fin 32), 4) := by decide
theorem pv_at_d98 : fetchRel p384VerifyPrehashCode 0xD98 = some (.alu .and (25 : Fin 32) (22 : Fin 32) a0, 4) := by decide
theorem pv_at_d9c : fetchRel p384VerifyPrehashCode 0xD9C = some (.alu .sub a0 x0 (24 : Fin 32), 4) := by decide
theorem pv_at_da0 : fetchRel p384VerifyPrehashCode 0xDA0 = some (.alu .sub a4 a0 a4, 4) := by decide
theorem pv_at_da4 : fetchRel p384VerifyPrehashCode 0xDA4 = some (.alu .and (24 : Fin 32) (27 : Fin 32) a5, 4) := by decide
theorem pv_at_da8 : fetchRel p384VerifyPrehashCode 0xDA8 = some (.alu .add a0 x0 (24 : Fin 32), 2) := by decide
theorem pv_at_daa : fetchRel p384VerifyPrehashCode 0xDAA = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_dae : fetchRel p384VerifyPrehashCode 0xDAE = some (.jalr ra ra 0xFFFFFCD8, 4) := by decide
theorem pv_at_db2 : fetchRel p384VerifyPrehashCode 0xDB2 = some (.store .sw sp a0 0x40, 2) := by decide
theorem pv_at_db4 : fetchRel p384VerifyPrehashCode 0xDB4 = some (.store .sw sp a1 0x38, 2) := by decide
theorem pv_at_db6 : fetchRel p384VerifyPrehashCode 0xDB6 = some (.alu .add a0 x0 (24 : Fin 32), 2) := by decide
theorem pv_at_db8 : fetchRel p384VerifyPrehashCode 0xDB8 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem pv_at_dba : fetchRel p384VerifyPrehashCode 0xDBA = some (.alu .add a2 x0 (22 : Fin 32), 2) := by decide
theorem pv_at_dbc : fetchRel p384VerifyPrehashCode 0xDBC = some (.alu .add (22 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem pv_at_dbe : fetchRel p384VerifyPrehashCode 0xDBE = some (.alu .add a3 x0 (21 : Fin 32), 2) := by decide
theorem pv_at_dc0 : fetchRel p384VerifyPrehashCode 0xDC0 = some (.load .lw (9 : Fin 32) sp 0x4C, 2) := by decide
theorem pv_at_dc2 : fetchRel p384VerifyPrehashCode 0xDC2 = some (.alu .add a4 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_dc4 : fetchRel p384VerifyPrehashCode 0xDC4 = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_dc8 : fetchRel p384VerifyPrehashCode 0xDC8 = some (.jalr ra ra 0xFFFFFCBE, 4) := by decide
theorem pv_at_dcc : fetchRel p384VerifyPrehashCode 0xDCC = some (.store .sw sp a0 0x50, 2) := by decide
theorem pv_at_dce : fetchRel p384VerifyPrehashCode 0xDCE = some (.store .sw sp a1 0x48, 2) := by decide
theorem pv_at_dd0 : fetchRel p384VerifyPrehashCode 0xDD0 = some (.alu .add a1 (8 : Fin 32) (21 : Fin 32), 4) := by decide
theorem pv_at_dd4 : fetchRel p384VerifyPrehashCode 0xDD4 = some (.alu .sltu a2 a1 (8 : Fin 32), 4) := by decide
theorem pv_at_dd8 : fetchRel p384VerifyPrehashCode 0xDD8 = some (.alu .add a0 (25 : Fin 32) (9 : Fin 32), 4) := by decide
theorem pv_at_ddc : fetchRel p384VerifyPrehashCode 0xDDC = some (.alu .add a2 a2 a0, 2) := by decide
theorem pv_at_dde : fetchRel p384VerifyPrehashCode 0xDDE = some (.alu .sltu a0 (21 : Fin 32) (8 : Fin 32), 4) := by decide
theorem pv_at_de2 : fetchRel p384VerifyPrehashCode 0xDE2 = some (.alu .sub a4 (9 : Fin 32) (25 : Fin 32), 4) := by decide
theorem pv_at_de6 : fetchRel p384VerifyPrehashCode 0xDE6 = some (.alu .sub a4 a4 a0, 2) := by decide
theorem pv_at_de8 : fetchRel p384VerifyPrehashCode 0xDE8 = some (.alu .sub a3 (21 : Fin 32) (8 : Fin 32), 4) := by decide
theorem pv_at_dec : fetchRel p384VerifyPrehashCode 0xDEC = some (.alu .add a0 x0 (24 : Fin 32), 2) := by decide
theorem pv_at_dee : fetchRel p384VerifyPrehashCode 0xDEE = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_df2 : fetchRel p384VerifyPrehashCode 0xDF2 = some (.jalr ra ra 0xFFFFFC94, 4) := by decide
theorem pv_at_df6 : fetchRel p384VerifyPrehashCode 0xDF6 = some (.aluImm .sll a2 a1 0x1F, 4) := by decide
theorem pv_at_dfa : fetchRel p384VerifyPrehashCode 0xDFA = some (.aluImm .srl a0 a0 0x1, 2) := by decide
theorem pv_at_dfc : fetchRel p384VerifyPrehashCode 0xDFC = some (.alu .or a0 a0 a2, 2) := by decide
theorem pv_at_dfe : fetchRel p384VerifyPrehashCode 0xDFE = some (.store .sw sp a0 0x44, 2) := by decide
theorem pv_at_e00 : fetchRel p384VerifyPrehashCode 0xE00 = some (.aluImm .sra a1 a1 0x1, 2) := by decide
theorem pv_at_e02 : fetchRel p384VerifyPrehashCode 0xE02 = some (.store .sw sp a1 0x4C, 2) := by decide
theorem pv_at_e04 : fetchRel p384VerifyPrehashCode 0xE04 = some (.alu .add a0 x0 (24 : Fin 32), 2) := by decide
theorem pv_at_e06 : fetchRel p384VerifyPrehashCode 0xE06 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem pv_at_e08 : fetchRel p384VerifyPrehashCode 0xE08 = some (.alu .add a2 x0 (26 : Fin 32), 2) := by decide
theorem pv_at_e0a : fetchRel p384VerifyPrehashCode 0xE0A = some (.load .lw (18 : Fin 32) sp 0x54, 2) := by decide
theorem pv_at_e0c : fetchRel p384VerifyPrehashCode 0xE0C = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem pv_at_e0e : fetchRel p384VerifyPrehashCode 0xE0E = some (.load .lw (25 : Fin 32) sp 0x1C, 2) := by decide
theorem pv_at_e10 : fetchRel p384VerifyPrehashCode 0xE10 = some (.alu .add a4 x0 (25 : Fin 32), 2) := by decide
theorem pv_at_e12 : fetchRel p384VerifyPrehashCode 0xE12 = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_e16 : fetchRel p384VerifyPrehashCode 0xE16 = some (.jalr ra ra 0xFFFFFC70, 4) := by decide
theorem pv_at_e1a : fetchRel p384VerifyPrehashCode 0xE1A = some (.aluImm .srl a2 a0 0x1F, 4) := by decide
theorem pv_at_e1e : fetchRel p384VerifyPrehashCode 0xE1E = some (.aluImm .sll a1 a1 0x1, 2) := by decide
theorem pv_at_e20 : fetchRel p384VerifyPrehashCode 0xE20 = some (.alu .or a1 a1 a2, 2) := by decide
theorem pv_at_e22 : fetchRel p384VerifyPrehashCode 0xE22 = some (.store .sw sp a1 0x34, 2) := by decide
theorem pv_at_e24 : fetchRel p384VerifyPrehashCode 0xE24 = some (.aluImm .sll a0 a0 0x1, 2) := by decide
theorem pv_at_e26 : fetchRel p384VerifyPrehashCode 0xE26 = some (.store .sw sp a0 0x2C, 2) := by decide
theorem pv_at_e28 : fetchRel p384VerifyPrehashCode 0xE28 = some (.alu .add a0 x0 (24 : Fin 32), 2) := by decide
theorem pv_at_e2a : fetchRel p384VerifyPrehashCode 0xE2A = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem pv_at_e2c : fetchRel p384VerifyPrehashCode 0xE2C = some (.load .lw (8 : Fin 32) sp 0x30, 2) := by decide
theorem pv_at_e2e : fetchRel p384VerifyPrehashCode 0xE2E = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_e30 : fetchRel p384VerifyPrehashCode 0xE30 = some (.alu .add a3 x0 (22 : Fin 32), 2) := by decide
theorem pv_at_e32 : fetchRel p384VerifyPrehashCode 0xE32 = some (.load .lw (21 : Fin 32) sp 0x28, 2) := by decide
theorem pv_at_e34 : fetchRel p384VerifyPrehashCode 0xE34 = some (.alu .add a4 x0 (21 : Fin 32), 2) := by decide
theorem pv_at_e36 : fetchRel p384VerifyPrehashCode 0xE36 = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_e3a : fetchRel p384VerifyPrehashCode 0xE3A = some (.jalr ra ra 0xFFFFFC4C, 4) := by decide
theorem pv_at_e3e : fetchRel p384VerifyPrehashCode 0xE3E = some (.aluImm .srl a2 a0 0x1F, 4) := by decide
theorem pv_at_e42 : fetchRel p384VerifyPrehashCode 0xE42 = some (.aluImm .sll a1 a1 0x1, 2) := by decide
theorem pv_at_e44 : fetchRel p384VerifyPrehashCode 0xE44 = some (.aluImm .sll (20 : Fin 32) a0 0x1, 4) := by decide
theorem pv_at_e48 : fetchRel p384VerifyPrehashCode 0xE48 = some (.alu .or a1 a1 a2, 2) := by decide
theorem pv_at_e4a : fetchRel p384VerifyPrehashCode 0xE4A = some (.store .sw sp a1 0x20, 2) := by decide
theorem pv_at_e4c : fetchRel p384VerifyPrehashCode 0xE4C = some (.alu .sltu a0 x0 (23 : Fin 32), 4) := by decide
theorem pv_at_e50 : fetchRel p384VerifyPrehashCode 0xE50 = some (.alu .sub a4 x0 (26 : Fin 32), 4) := by decide
theorem pv_at_e54 : fetchRel p384VerifyPrehashCode 0xE54 = some (.alu .sub a3 x0 (23 : Fin 32), 4) := by decide
theorem pv_at_e58 : fetchRel p384VerifyPrehashCode 0xE58 = some (.alu .sub a4 a4 a0, 2) := by decide
theorem pv_at_e5a : fetchRel p384VerifyPrehashCode 0xE5A = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem pv_at_e5c : fetchRel p384VerifyPrehashCode 0xE5C = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_e5e : fetchRel p384VerifyPrehashCode 0xE5E = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem pv_at_e60 : fetchRel p384VerifyPrehashCode 0xE60 = some (.alu .add a2 x0 (26 : Fin 32), 2) := by decide
theorem pv_at_e62 : fetchRel p384VerifyPrehashCode 0xE62 = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_e66 : fetchRel p384VerifyPrehashCode 0xE66 = some (.jalr ra ra 0xFFFFFC20, 4) := by decide
theorem pv_at_e6a : fetchRel p384VerifyPrehashCode 0xE6A = some (.aluImm .add a2 sp 0x7FF, 4) := by decide
theorem pv_at_e6e : fetchRel p384VerifyPrehashCode 0xE6E = some (.aluImm .add a2 a2 0x581, 4) := by decide
theorem pv_at_e72 : fetchRel p384VerifyPrehashCode 0xE72 = some (.store .sb a2 (27 : Fin 32) 0x514, 4) := by decide
theorem pv_at_e76 : fetchRel p384VerifyPrehashCode 0xE76 = some (.lui a2 0x1000, 2) := by decide
theorem pv_at_e78 : fetchRel p384VerifyPrehashCode 0xE78 = some (.aluImm .add a2 a2 0x294, 4) := by decide
theorem pv_at_e7c : fetchRel p384VerifyPrehashCode 0xE7C = some (.alu .add (23 : Fin 32) sp a2, 4) := by decide
theorem pv_at_e80 : fetchRel p384VerifyPrehashCode 0xE80 = some (.aluImm .add a2 sp 0x7FF, 4) := by decide
theorem pv_at_e84 : fetchRel p384VerifyPrehashCode 0xE84 = some (.aluImm .add a2 a2 0x581, 4) := by decide
theorem pv_at_e88 : fetchRel p384VerifyPrehashCode 0xE88 = some (.load .lbu a2 a2 0x514, 4) := by decide
theorem pv_at_e8c : fetchRel p384VerifyPrehashCode 0xE8C = some (.alu .sub a3 x0 a2, 4) := by decide
theorem pv_at_e90 : fetchRel p384VerifyPrehashCode 0xE90 = some (.aluImm .sltu a2 a2 0x1, 4) := by decide
theorem pv_at_e94 : fetchRel p384VerifyPrehashCode 0xE94 = some (.alu .and a0 a0 a3, 2) := by decide
theorem pv_at_e96 : fetchRel p384VerifyPrehashCode 0xE96 = some (.alu .sltu a4 x0 (19 : Fin 32), 4) := by decide
theorem pv_at_e9a : fetchRel p384VerifyPrehashCode 0xE9A = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem pv_at_e9c : fetchRel p384VerifyPrehashCode 0xE9C = some (.alu .and a1 a1 a2, 2) := by decide
theorem pv_at_e9e : fetchRel p384VerifyPrehashCode 0xE9E = some (.alu .add (18 : Fin 32) (18 : Fin 32) a0, 2) := by decide
theorem pv_at_ea0 : fetchRel p384VerifyPrehashCode 0xEA0 = some (.store .sw sp (18 : Fin 32) 0x54, 2) := by decide
theorem pv_at_ea2 : fetchRel p384VerifyPrehashCode 0xEA2 = some (.alu .sltu a0 (18 : Fin 32) a0, 4) := by decide
theorem pv_at_ea6 : fetchRel p384VerifyPrehashCode 0xEA6 = some (.alu .add a1 a1 (25 : Fin 32), 2) := by decide
theorem pv_at_ea8 : fetchRel p384VerifyPrehashCode 0xEA8 = some (.alu .sub a5 x0 (8 : Fin 32), 4) := by decide
theorem pv_at_eac : fetchRel p384VerifyPrehashCode 0xEAC = some (.alu .add (18 : Fin 32) a1 a0, 4) := by decide
theorem pv_at_eb0 : fetchRel p384VerifyPrehashCode 0xEB0 = some (.alu .sub a3 x0 (19 : Fin 32), 4) := by decide
theorem pv_at_eb4 : fetchRel p384VerifyPrehashCode 0xEB4 = some (.alu .sub a4 a5 a4, 4) := by decide
theorem pv_at_eb8 : fetchRel p384VerifyPrehashCode 0xEB8 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem pv_at_eba : fetchRel p384VerifyPrehashCode 0xEBA = some (.aluImm .add (24 : Fin 32) sp 0x7FF, 4) := by decide
theorem pv_at_ebe : fetchRel p384VerifyPrehashCode 0xEBE = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x581, 4) := by decide
theorem pv_at_ec2 : fetchRel p384VerifyPrehashCode 0xEC2 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem pv_at_ec4 : fetchRel p384VerifyPrehashCode 0xEC4 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_ec6 : fetchRel p384VerifyPrehashCode 0xEC6 = some (.auipc ra 0xB000, 4) := by decide
theorem pv_at_eca : fetchRel p384VerifyPrehashCode 0xECA = some (.jalr ra ra 0xFFFFFBBC, 4) := by decide
theorem pv_at_ece : fetchRel p384VerifyPrehashCode 0xECE = some (.alu .add (8 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem pv_at_ed0 : fetchRel p384VerifyPrehashCode 0xED0 = some (.load .lw a4 sp 0x3C, 2) := by decide
theorem pv_at_ed2 : fetchRel p384VerifyPrehashCode 0xED2 = some (.store .sb (24 : Fin 32) (27 : Fin 32) 0x514, 4) := by decide
theorem pv_at_ed6 : fetchRel p384VerifyPrehashCode 0xED6 = some (.load .lbu a2 (24 : Fin 32) 0x514, 4) := by decide
theorem pv_at_eda : fetchRel p384VerifyPrehashCode 0xEDA = some (.aluImm .add a4 a4 0xFFFFFFFF, 2) := by decide
theorem pv_at_edc : fetchRel p384VerifyPrehashCode 0xEDC = some (.alu .sub a3 x0 a2, 4) := by decide
theorem pv_at_ee0 : fetchRel p384VerifyPrehashCode 0xEE0 = some (.aluImm .sltu a2 a2 0x1, 4) := by decide
theorem pv_at_ee4 : fetchRel p384VerifyPrehashCode 0xEE4 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem pv_at_ee6 : fetchRel p384VerifyPrehashCode 0xEE6 = some (.alu .and a0 a0 a3, 2) := by decide
theorem pv_at_ee8 : fetchRel p384VerifyPrehashCode 0xEE8 = some (.alu .and a1 a1 a2, 2) := by decide
theorem pv_at_eea : fetchRel p384VerifyPrehashCode 0xEEA = some (.alu .add (22 : Fin 32) (22 : Fin 32) a0, 2) := by decide
theorem pv_at_eec : fetchRel p384VerifyPrehashCode 0xEEC = some (.alu .sltu a0 (22 : Fin 32) a0, 4) := by decide
theorem pv_at_ef0 : fetchRel p384VerifyPrehashCode 0xEF0 = some (.alu .add a1 a1 (21 : Fin 32), 2) := by decide
theorem pv_at_ef2 : fetchRel p384VerifyPrehashCode 0xEF2 = some (.load .lw (25 : Fin 32) sp 0x20, 2) := by decide
theorem pv_at_ef4 : fetchRel p384VerifyPrehashCode 0xEF4 = some (.alu .add a3 a1 a0, 4) := by decide
theorem pv_at_ef8 : fetchRel p384VerifyPrehashCode 0xEF8 = some (.load .lw (23 : Fin 32) sp 0x2C, 2) := by decide
theorem pv_at_efa : fetchRel p384VerifyPrehashCode 0xEFA = some (.load .lw (24 : Fin 32) sp 0x38, 2) := by decide
theorem pv_at_efc : fetchRel p384VerifyPrehashCode 0xEFC = some (.load .lw (26 : Fin 32) sp 0x34, 2) := by decide
theorem pv_at_efe : fetchRel p384VerifyPrehashCode 0xEFE = some (.branch .bne a4 x0 0xFFFFFE38, 4) := by decide
theorem pv_at_f02 : fetchRel p384VerifyPrehashCode 0xF02 = some (.alu .add (19 : Fin 32) x0 (8 : Fin 32), 2) := by decide
theorem pv_at_f04 : fetchRel p384VerifyPrehashCode 0xF04 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_f06 : fetchRel p384VerifyPrehashCode 0xF06 = some (.aluImm .add a0 a0 0x744, 4) := by decide
theorem pv_at_f0a : fetchRel p384VerifyPrehashCode 0xF0A = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_f0c : fetchRel p384VerifyPrehashCode 0xF0C = some (.store .sw a0 (23 : Fin 32) 0x524, 4) := by decide
theorem pv_at_f10 : fetchRel p384VerifyPrehashCode 0xF10 = some (.store .sw a0 (26 : Fin 32) 0x528, 4) := by decide
theorem pv_at_f14 : fetchRel p384VerifyPrehashCode 0xF14 = some (.store .sw a0 (20 : Fin 32) 0x52C, 4) := by decide
theorem pv_at_f18 : fetchRel p384VerifyPrehashCode 0xF18 = some (.store .sw a0 (25 : Fin 32) 0x530, 4) := by decide
theorem pv_at_f1c : fetchRel p384VerifyPrehashCode 0xF1C = some (.load .lw a1 sp 0x54, 2) := by decide
theorem pv_at_f1e : fetchRel p384VerifyPrehashCode 0xF1E = some (.store .sw a0 a1 0x534, 4) := by decide
theorem pv_at_f22 : fetchRel p384VerifyPrehashCode 0xF22 = some (.store .sw a0 (18 : Fin 32) 0x538, 4) := by decide
theorem pv_at_f26 : fetchRel p384VerifyPrehashCode 0xF26 = some (.store .sw a0 (22 : Fin 32) 0x53C, 4) := by decide
theorem pv_at_f2a : fetchRel p384VerifyPrehashCode 0xF2A = some (.store .sw a0 a3 0x540, 4) := by decide
theorem pv_at_f2e : fetchRel p384VerifyPrehashCode 0xF2E = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_f30 : fetchRel p384VerifyPrehashCode 0xF30 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_f34 : fetchRel p384VerifyPrehashCode 0xF34 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_f36 : fetchRel p384VerifyPrehashCode 0xF36 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_f38 : fetchRel p384VerifyPrehashCode 0xF38 = some (.aluImm .add a1 a1 0x714, 4) := by decide
theorem pv_at_f3c : fetchRel p384VerifyPrehashCode 0xF3C = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_f3e : fetchRel p384VerifyPrehashCode 0xF3E = some (.aluImm .add a2 sp 0x7FF, 4) := by decide
theorem pv_at_f42 : fetchRel p384VerifyPrehashCode 0xF42 = some (.aluImm .add a2 a2 0x551, 4) := by decide
theorem pv_at_f46 : fetchRel p384VerifyPrehashCode 0xF46 = some (.lui a3 0x2000, 2) := by decide
theorem pv_at_f48 : fetchRel p384VerifyPrehashCode 0xF48 = some (.aluImm .add a3 a3 0xFFFFFC68, 4) := by decide
theorem pv_at_f4c : fetchRel p384VerifyPrehashCode 0xF4C = some (.alu .add a3 a3 sp, 2) := by decide
theorem pv_at_f4e : fetchRel p384VerifyPrehashCode 0xF4E = some (.load .lw (8 : Fin 32) sp 0x14, 2) := by decide
theorem pv_at_f50 : fetchRel p384VerifyPrehashCode 0xF50 = some (.alu .add a4 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_f52 : fetchRel p384VerifyPrehashCode 0xF52 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_f56 : fetchRel p384VerifyPrehashCode 0xF56 = some (.jalr ra ra 0xFFFFFA7A, 4) := by decide
theorem pv_at_f5a : fetchRel p384VerifyPrehashCode 0xF5A = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_f5c : fetchRel p384VerifyPrehashCode 0xF5C = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_f60 : fetchRel p384VerifyPrehashCode 0xF60 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_f62 : fetchRel p384VerifyPrehashCode 0xF62 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_f64 : fetchRel p384VerifyPrehashCode 0xF64 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_f68 : fetchRel p384VerifyPrehashCode 0xF68 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_f6a : fetchRel p384VerifyPrehashCode 0xF6A = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_f6e : fetchRel p384VerifyPrehashCode 0xF6E = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_f72 : fetchRel p384VerifyPrehashCode 0xF72 = some (.jalr ra ra 0x6C2, 4) := by decide
theorem pv_at_f76 : fetchRel p384VerifyPrehashCode 0xF76 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_f7a : fetchRel p384VerifyPrehashCode 0xF7A = some (.aluImm .add a0 a0 0x551, 4) := by decide
theorem pv_at_f7e : fetchRel p384VerifyPrehashCode 0xF7E = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_f82 : fetchRel p384VerifyPrehashCode 0xF82 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_f84 : fetchRel p384VerifyPrehashCode 0xF84 = some (.aluImm .add a1 a1 0x2C8, 4) := by decide
theorem pv_at_f88 : fetchRel p384VerifyPrehashCode 0xF88 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_f8a : fetchRel p384VerifyPrehashCode 0xF8A = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_f8e : fetchRel p384VerifyPrehashCode 0xF8E = some (.jalr ra ra 0x6A6, 4) := by decide
theorem pv_at_f92 : fetchRel p384VerifyPrehashCode 0xF92 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_f94 : fetchRel p384VerifyPrehashCode 0xF94 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_f98 : fetchRel p384VerifyPrehashCode 0xF98 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_f9a : fetchRel p384VerifyPrehashCode 0xF9A = some (.aluImm .add a1 sp 0x270, 2) := by decide
theorem pv_at_f9c : fetchRel p384VerifyPrehashCode 0xF9C = some (.lui a2 0x1000, 2) := by decide
theorem pv_at_f9e : fetchRel p384VerifyPrehashCode 0xF9E = some (.aluImm .add a2 a2 0x7A4, 4) := by decide
theorem pv_at_fa2 : fetchRel p384VerifyPrehashCode 0xFA2 = some (.alu .add a2 a2 sp, 2) := by decide
theorem pv_at_fa4 : fetchRel p384VerifyPrehashCode 0xFA4 = some (.aluImm .add a3 sp 0x7FF, 4) := by decide
theorem pv_at_fa8 : fetchRel p384VerifyPrehashCode 0xFA8 = some (.aluImm .add a3 a3 0x611, 4) := by decide
theorem pv_at_fac : fetchRel p384VerifyPrehashCode 0xFAC = some (.aluImm .add a4 x0 0xFFFFFFFF, 2) := by decide
theorem pv_at_fae : fetchRel p384VerifyPrehashCode 0xFAE = some (.aluImm .add a5 x0 0xFFFFFFFE, 2) := by decide
theorem pv_at_fb0 : fetchRel p384VerifyPrehashCode 0xFB0 = some (.lui a6 0x2000, 2) := by decide
theorem pv_at_fb2 : fetchRel p384VerifyPrehashCode 0xFB2 = some (.aluImm .add a6 a6 0xFFFFFC68, 4) := by decide
theorem pv_at_fb6 : fetchRel p384VerifyPrehashCode 0xFB6 = some (.alu .add a6 a6 sp, 2) := by decide
theorem pv_at_fb8 : fetchRel p384VerifyPrehashCode 0xFB8 = some (.alu .add (17 : Fin 32) x0 (8 : Fin 32), 2) := by decide
theorem pv_at_fba : fetchRel p384VerifyPrehashCode 0xFBA = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_fbe : fetchRel p384VerifyPrehashCode 0xFBE = some (.jalr ra ra 0xFFFFFA9C, 4) := by decide
theorem pv_at_fc2 : fetchRel p384VerifyPrehashCode 0xFC2 = some (.aluImm .add a0 sp 0x270, 2) := by decide
theorem pv_at_fc4 : fetchRel p384VerifyPrehashCode 0xFC4 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_fc6 : fetchRel p384VerifyPrehashCode 0xFC6 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_fca : fetchRel p384VerifyPrehashCode 0xFCA = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_fcc : fetchRel p384VerifyPrehashCode 0xFCC = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_fd0 : fetchRel p384VerifyPrehashCode 0xFD0 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_fd4 : fetchRel p384VerifyPrehashCode 0xFD4 = some (.jalr ra ra 0x660, 4) := by decide
theorem pv_at_fd8 : fetchRel p384VerifyPrehashCode 0xFD8 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_fda : fetchRel p384VerifyPrehashCode 0xFDA = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_fde : fetchRel p384VerifyPrehashCode 0xFDE = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_fe0 : fetchRel p384VerifyPrehashCode 0xFE0 = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem pv_at_fe4 : fetchRel p384VerifyPrehashCode 0xFE4 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_fe6 : fetchRel p384VerifyPrehashCode 0xFE6 = some (.aluImm .add a1 a1 0x2C8, 4) := by decide
theorem pv_at_fea : fetchRel p384VerifyPrehashCode 0xFEA = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_fec : fetchRel p384VerifyPrehashCode 0xFEC = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_ff0 : fetchRel p384VerifyPrehashCode 0xFF0 = some (.jalr ra ra 0x644, 4) := by decide
theorem pv_at_ff4 : fetchRel p384VerifyPrehashCode 0xFF4 = some (.load .lw a0 sp 0x18, 2) := by decide
theorem pv_at_ff6 : fetchRel p384VerifyPrehashCode 0xFF6 = some (.alu .sub a0 a0 (8 : Fin 32), 2) := by decide
theorem pv_at_ff8 : fetchRel p384VerifyPrehashCode 0xFF8 = some (.branch .bne a0 x0 0xFFFFFCF0, 4) := by decide
theorem pv_at_ffc : fetchRel p384VerifyPrehashCode 0xFFC = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_ffe : fetchRel p384VerifyPrehashCode 0xFFE = some (.aluImm .add a0 a0 0x744, 4) := by decide
theorem pv_at_1002 : fetchRel p384VerifyPrehashCode 0x1002 = some (.alu .add (9 : Fin 32) sp a0, 4) := by decide
theorem pv_at_1006 : fetchRel p384VerifyPrehashCode 0x1006 = some (.load .lbu a2 (9 : Fin 32) 0x0, 4) := by decide
theorem pv_at_100a : fetchRel p384VerifyPrehashCode 0x100A = some (.lui a0 0x2000, 2) := by decide
theorem pv_at_100c : fetchRel p384VerifyPrehashCode 0x100C = some (.aluImm .add a0 a0 0xFFFFFC34, 4) := by decide
theorem pv_at_1010 : fetchRel p384VerifyPrehashCode 0x1010 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_1012 : fetchRel p384VerifyPrehashCode 0x1012 = some (.aluImm .add a1 sp 0x270, 2) := by decide
theorem pv_at_1014 : fetchRel p384VerifyPrehashCode 0x1014 = some (.aluImm .add a3 sp 0x7FF, 4) := by decide
theorem pv_at_1018 : fetchRel p384VerifyPrehashCode 0x1018 = some (.aluImm .add a3 a3 0x611, 4) := by decide
theorem pv_at_101c : fetchRel p384VerifyPrehashCode 0x101C = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_1020 : fetchRel p384VerifyPrehashCode 0x1020 = some (.jalr ra ra 0xFFFFF8F6, 4) := by decide
theorem pv_at_1024 : fetchRel p384VerifyPrehashCode 0x1024 = some (.lui a1 0x3FCC5000, 4) := by decide
theorem pv_at_1028 : fetchRel p384VerifyPrehashCode 0x1028 = some (.aluImm .add a1 a1 0xFFFFFCC4, 4) := by decide
theorem pv_at_102c : fetchRel p384VerifyPrehashCode 0x102C = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_102e : fetchRel p384VerifyPrehashCode 0x102E = some (.aluImm .add a0 a0 0x714, 4) := by decide
theorem pv_at_1032 : fetchRel p384VerifyPrehashCode 0x1032 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_1034 : fetchRel p384VerifyPrehashCode 0x1034 = some (.auipc ra 0xC000, 4) := by decide
theorem pv_at_1038 : fetchRel p384VerifyPrehashCode 0x1038 = some (.jalr ra ra 0x710, 4) := by decide
theorem pv_at_103c : fetchRel p384VerifyPrehashCode 0x103C = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem pv_at_1040 : fetchRel p384VerifyPrehashCode 0x1040 = some (.load .lw a1 sp 0x10, 2) := by decide
theorem pv_at_1042 : fetchRel p384VerifyPrehashCode 0x1042 = some (.alu .and a0 a0 a1, 2) := by decide
theorem pv_at_1044 : fetchRel p384VerifyPrehashCode 0x1044 = some (.auipc ra 0x6000, 4) := by decide
theorem pv_at_1048 : fetchRel p384VerifyPrehashCode 0x1048 = some (.jalr ra ra 0x4E2, 4) := by decide
theorem pv_at_104c : fetchRel p384VerifyPrehashCode 0x104C = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem pv_at_104e : fetchRel p384VerifyPrehashCode 0x104E = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_1050 : fetchRel p384VerifyPrehashCode 0x1050 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_1054 : fetchRel p384VerifyPrehashCode 0x1054 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_1056 : fetchRel p384VerifyPrehashCode 0x1056 = some (.lui a1 0x2000, 2) := by decide
theorem pv_at_1058 : fetchRel p384VerifyPrehashCode 0x1058 = some (.aluImm .add a1 a1 0xFFFFFC34, 4) := by decide
theorem pv_at_105c : fetchRel p384VerifyPrehashCode 0x105C = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_105e : fetchRel p384VerifyPrehashCode 0x105E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_1062 : fetchRel p384VerifyPrehashCode 0x1062 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_1066 : fetchRel p384VerifyPrehashCode 0x1066 = some (.jalr ra ra 0x5CE, 4) := by decide
theorem pv_at_106a : fetchRel p384VerifyPrehashCode 0x106A = some (.store .sb (19 : Fin 32) (8 : Fin 32) 0x544, 4) := by decide
theorem pv_at_106e : fetchRel p384VerifyPrehashCode 0x106E = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_1070 : fetchRel p384VerifyPrehashCode 0x1070 = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_1074 : fetchRel p384VerifyPrehashCode 0x1074 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_1076 : fetchRel p384VerifyPrehashCode 0x1076 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_107a : fetchRel p384VerifyPrehashCode 0x107A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pv_at_107c : fetchRel p384VerifyPrehashCode 0x107C = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_1080 : fetchRel p384VerifyPrehashCode 0x1080 = some (.jalr ra ra 0x54C, 4) := by decide
theorem pv_at_1084 : fetchRel p384VerifyPrehashCode 0x1084 = some (.aluImm .and a3 (8 : Fin 32) 0xFF, 4) := by decide
theorem pv_at_1088 : fetchRel p384VerifyPrehashCode 0x1088 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_108c : fetchRel p384VerifyPrehashCode 0x108C = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_1090 : fetchRel p384VerifyPrehashCode 0x1090 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_1092 : fetchRel p384VerifyPrehashCode 0x1092 = some (.aluImm .add a1 a1 0x7A4, 4) := by decide
theorem pv_at_1096 : fetchRel p384VerifyPrehashCode 0x1096 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_1098 : fetchRel p384VerifyPrehashCode 0x1098 = some (.lui a2 0x1000, 2) := by decide
theorem pv_at_109a : fetchRel p384VerifyPrehashCode 0x109A = some (.aluImm .add a2 a2 0x294, 4) := by decide
theorem pv_at_109e : fetchRel p384VerifyPrehashCode 0x109E = some (.alu .add a2 a2 sp, 2) := by decide
theorem pv_at_10a0 : fetchRel p384VerifyPrehashCode 0x10A0 = some (.auipc ra 0xC000, 4) := by decide
theorem pv_at_10a4 : fetchRel p384VerifyPrehashCode 0x10A4 = some (.jalr ra ra 0x576, 4) := by decide
theorem pv_at_10a8 : fetchRel p384VerifyPrehashCode 0x10A8 = some (.store .sb (19 : Fin 32) (8 : Fin 32) 0xC0, 4) := by decide
theorem pv_at_10ac : fetchRel p384VerifyPrehashCode 0x10AC = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_10ae : fetchRel p384VerifyPrehashCode 0x10AE = some (.aluImm .add a0 a0 0x7A4, 4) := by decide
theorem pv_at_10b2 : fetchRel p384VerifyPrehashCode 0x10B2 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_10b4 : fetchRel p384VerifyPrehashCode 0x10B4 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_10b8 : fetchRel p384VerifyPrehashCode 0x10B8 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_10bc : fetchRel p384VerifyPrehashCode 0x10BC = some (.auipc ra 0xC000, 4) := by decide
theorem pv_at_10c0 : fetchRel p384VerifyPrehashCode 0x10C0 = some (.jalr ra ra 0x646, 4) := by decide
theorem pv_at_10c4 : fetchRel p384VerifyPrehashCode 0x10C4 = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_10c8 : fetchRel p384VerifyPrehashCode 0x10C8 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_10cc : fetchRel p384VerifyPrehashCode 0x10CC = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_10d0 : fetchRel p384VerifyPrehashCode 0x10D0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem pv_at_10d2 : fetchRel p384VerifyPrehashCode 0x10D2 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_10d6 : fetchRel p384VerifyPrehashCode 0x10D6 = some (.jalr ra ra 0x4F6, 4) := by decide
theorem pv_at_10da : fetchRel p384VerifyPrehashCode 0x10DA = some (.load .lbu (8 : Fin 32) (9 : Fin 32) 0x90, 4) := by decide
theorem pv_at_10de : fetchRel p384VerifyPrehashCode 0x10DE = some (.aluImm .add a0 sp 0x270, 2) := by decide
theorem pv_at_10e0 : fetchRel p384VerifyPrehashCode 0x10E0 = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_10e4 : fetchRel p384VerifyPrehashCode 0x10E4 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_10e8 : fetchRel p384VerifyPrehashCode 0x10E8 = some (.lui a2 0x1000, 2) := by decide
theorem pv_at_10ea : fetchRel p384VerifyPrehashCode 0x10EA = some (.aluImm .add a2 a2 0x7A4, 4) := by decide
theorem pv_at_10ee : fetchRel p384VerifyPrehashCode 0x10EE = some (.alu .add a2 a2 sp, 2) := by decide
theorem pv_at_10f0 : fetchRel p384VerifyPrehashCode 0x10F0 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem pv_at_10f2 : fetchRel p384VerifyPrehashCode 0x10F2 = some (.auipc ra 0xC000, 4) := by decide
theorem pv_at_10f6 : fetchRel p384VerifyPrehashCode 0x10F6 = some (.jalr ra ra 0x524, 4) := by decide
theorem pv_at_10fa : fetchRel p384VerifyPrehashCode 0x10FA = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_10fc : fetchRel p384VerifyPrehashCode 0x10FC = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_1100 : fetchRel p384VerifyPrehashCode 0x1100 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_1102 : fetchRel p384VerifyPrehashCode 0x1102 = some (.lui a1 0x2000, 2) := by decide
theorem pv_at_1104 : fetchRel p384VerifyPrehashCode 0x1104 = some (.aluImm .add a1 a1 0xFFFFFC88, 4) := by decide
theorem pv_at_1108 : fetchRel p384VerifyPrehashCode 0x1108 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_110a : fetchRel p384VerifyPrehashCode 0x110A = some (.aluImm .add a2 sp 0x270, 2) := by decide
theorem pv_at_110c : fetchRel p384VerifyPrehashCode 0x110C = some (.auipc ra 0xC000, 4) := by decide
theorem pv_at_1110 : fetchRel p384VerifyPrehashCode 0x1110 = some (.jalr ra ra 0x552, 4) := by decide
theorem pv_at_1114 : fetchRel p384VerifyPrehashCode 0x1114 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_1116 : fetchRel p384VerifyPrehashCode 0x1116 = some (.aluImm .add a0 a0 0x2C4, 4) := by decide
theorem pv_at_111a : fetchRel p384VerifyPrehashCode 0x111A = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_111c : fetchRel p384VerifyPrehashCode 0x111C = some (.aluImm .add a2 sp 0x270, 2) := by decide
theorem pv_at_111e : fetchRel p384VerifyPrehashCode 0x111E = some (.lui a1 0x2000, 2) := by decide
theorem pv_at_1120 : fetchRel p384VerifyPrehashCode 0x1120 = some (.aluImm .add a1 a1 0xFFFFFCB8, 4) := by decide
theorem pv_at_1124 : fetchRel p384VerifyPrehashCode 0x1124 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_1126 : fetchRel p384VerifyPrehashCode 0x1126 = some (.auipc ra 0xC000, 4) := by decide
theorem pv_at_112a : fetchRel p384VerifyPrehashCode 0x112A = some (.jalr ra ra 0x538, 4) := by decide
theorem pv_at_112e : fetchRel p384VerifyPrehashCode 0x112E = some (.store .sb (19 : Fin 32) x0 0x574, 4) := by decide
theorem pv_at_1132 : fetchRel p384VerifyPrehashCode 0x1132 = some (.store .sb (19 : Fin 32) (8 : Fin 32) 0x578, 4) := by decide
theorem pv_at_1136 : fetchRel p384VerifyPrehashCode 0x1136 = some (.lui a2 0x3FCC4000, 4) := by decide
theorem pv_at_113a : fetchRel p384VerifyPrehashCode 0x113A = some (.aluImm .add a2 a2 0x238, 4) := by decide
theorem pv_at_113e : fetchRel p384VerifyPrehashCode 0x113E = some (.aluImm .add a0 sp 0x7FF, 4) := by decide
theorem pv_at_1142 : fetchRel p384VerifyPrehashCode 0x1142 = some (.aluImm .add a0 a0 0x611, 4) := by decide
theorem pv_at_1146 : fetchRel p384VerifyPrehashCode 0x1146 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_1148 : fetchRel p384VerifyPrehashCode 0x1148 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_114c : fetchRel p384VerifyPrehashCode 0x114C = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_114e : fetchRel p384VerifyPrehashCode 0x114E = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem pv_at_1152 : fetchRel p384VerifyPrehashCode 0x1152 = some (.jalr ra ra 0xFFFFFFAC, 4) := by decide
theorem pv_at_1156 : fetchRel p384VerifyPrehashCode 0x1156 = some (.lui a0 0x2000, 2) := by decide
theorem pv_at_1158 : fetchRel p384VerifyPrehashCode 0x1158 = some (.aluImm .add a0 a0 0xFFFFFD18, 4) := by decide
theorem pv_at_115c : fetchRel p384VerifyPrehashCode 0x115C = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_115e : fetchRel p384VerifyPrehashCode 0x115E = some (.auipc ra 0x6000, 4) := by decide
theorem pv_at_1162 : fetchRel p384VerifyPrehashCode 0x1162 = some (.jalr ra ra 0x374, 4) := by decide
theorem pv_at_1166 : fetchRel p384VerifyPrehashCode 0x1166 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_1168 : fetchRel p384VerifyPrehashCode 0x1168 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_116c : fetchRel p384VerifyPrehashCode 0x116C = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_116e : fetchRel p384VerifyPrehashCode 0x116E = some (.aluImm .add a1 sp 0x7FF, 4) := by decide
theorem pv_at_1172 : fetchRel p384VerifyPrehashCode 0x1172 = some (.aluImm .add a1 a1 0x611, 4) := by decide
theorem pv_at_1176 : fetchRel p384VerifyPrehashCode 0x1176 = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_117a : fetchRel p384VerifyPrehashCode 0x117A = some (.jalr ra ra 0xFFFFFAFE, 4) := by decide
theorem pv_at_117e : fetchRel p384VerifyPrehashCode 0x117E = some (.lui a0 0x2000, 2) := by decide
theorem pv_at_1180 : fetchRel p384VerifyPrehashCode 0x1180 = some (.aluImm .add a0 a0 0xFFFFFD18, 4) := by decide
theorem pv_at_1184 : fetchRel p384VerifyPrehashCode 0x1184 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_1186 : fetchRel p384VerifyPrehashCode 0x1186 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_1188 : fetchRel p384VerifyPrehashCode 0x1188 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_118c : fetchRel p384VerifyPrehashCode 0x118C = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_118e : fetchRel p384VerifyPrehashCode 0x118E = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_1192 : fetchRel p384VerifyPrehashCode 0x1192 = some (.jalr ra ra 0xFFFFFB46, 4) := by decide
theorem pv_at_1196 : fetchRel p384VerifyPrehashCode 0x1196 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_1198 : fetchRel p384VerifyPrehashCode 0x1198 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_119c : fetchRel p384VerifyPrehashCode 0x119C = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_119e : fetchRel p384VerifyPrehashCode 0x119E = some (.lui a1 0x2000, 2) := by decide
theorem pv_at_11a0 : fetchRel p384VerifyPrehashCode 0x11A0 = some (.aluImm .add a1 a1 0xFFFFFD18, 4) := by decide
theorem pv_at_11a4 : fetchRel p384VerifyPrehashCode 0x11A4 = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_11a6 : fetchRel p384VerifyPrehashCode 0x11A6 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem pv_at_11aa : fetchRel p384VerifyPrehashCode 0x11AA = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem pv_at_11ae : fetchRel p384VerifyPrehashCode 0x11AE = some (.jalr ra ra 0xFFFFFD18, 4) := by decide
theorem pv_at_11b2 : fetchRel p384VerifyPrehashCode 0x11B2 = some (.aluImm .add a0 sp 0x1B0, 2) := by decide
theorem pv_at_11b4 : fetchRel p384VerifyPrehashCode 0x11B4 = some (.lui a1 0x1000, 2) := by decide
theorem pv_at_11b6 : fetchRel p384VerifyPrehashCode 0x11B6 = some (.aluImm .add a1 a1 0x294, 4) := by decide
theorem pv_at_11ba : fetchRel p384VerifyPrehashCode 0x11BA = some (.alu .add a1 a1 sp, 2) := by decide
theorem pv_at_11bc : fetchRel p384VerifyPrehashCode 0x11BC = some (.auipc ra 0xD000, 4) := by decide
theorem pv_at_11c0 : fetchRel p384VerifyPrehashCode 0x11C0 = some (.jalr ra ra 0xFFFFF9C0, 4) := by decide
theorem pv_at_11c4 : fetchRel p384VerifyPrehashCode 0x11C4 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem pv_at_11c8 : fetchRel p384VerifyPrehashCode 0x11C8 = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem pv_at_11cc : fetchRel p384VerifyPrehashCode 0x11CC = some (.jal x0 0xFFFFEF64, 4) := by decide
theorem pv_at_11d0 : fetchRel p384VerifyPrehashCode 0x11D0 = some (.lui a0 0x1000, 2) := by decide
theorem pv_at_11d2 : fetchRel p384VerifyPrehashCode 0x11D2 = some (.aluImm .add a0 a0 0x294, 4) := by decide
theorem pv_at_11d6 : fetchRel p384VerifyPrehashCode 0x11D6 = some (.alu .add a0 a0 sp, 2) := by decide
theorem pv_at_11d8 : fetchRel p384VerifyPrehashCode 0x11D8 = some (.auipc ra 0xC000, 4) := by decide
theorem pv_at_11dc : fetchRel p384VerifyPrehashCode 0x11DC = some (.jalr ra ra 0x434, 4) := by decide
theorem pv_at_11e0 : fetchRel p384VerifyPrehashCode 0x11E0 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem pv_at_11e2 : fetchRel p384VerifyPrehashCode 0x11E2 = some (.auipc ra 0x6000, 4) := by decide
theorem pv_at_11e6 : fetchRel p384VerifyPrehashCode 0x11E6 = some (.jalr ra ra 0xFFFFFEA8, 4) := by decide

end C3.RV32.Pv
