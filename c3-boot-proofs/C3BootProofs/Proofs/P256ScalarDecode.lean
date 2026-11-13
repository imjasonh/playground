import C3BootProofs.Proofs.P256ScalarFacts

/-!
# Decoded instructions of P-256's `Scalar::mul`

`scripts/decode-lemmas.py` writes these lemmas from `llvm-objdump` output,
and `decide` checks each one against the extracted bytes.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000

theorem psm_at_0 : fetchRel p256ScalarMulCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF60, 2) := by decide
theorem psm_at_2 : fetchRel p256ScalarMulCode 0x2 = some (.store .sw sp ra 0x9C, 2) := by decide
theorem psm_at_4 : fetchRel p256ScalarMulCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x98, 2) := by decide
theorem psm_at_6 : fetchRel p256ScalarMulCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x94, 2) := by decide
theorem psm_at_8 : fetchRel p256ScalarMulCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x90, 2) := by decide
theorem psm_at_a : fetchRel p256ScalarMulCode 0xA = some (.store .sw sp (19 : Fin 32) 0x8C, 2) := by decide
theorem psm_at_c : fetchRel p256ScalarMulCode 0xC = some (.store .sw sp (20 : Fin 32) 0x88, 2) := by decide
theorem psm_at_e : fetchRel p256ScalarMulCode 0xE = some (.store .sw sp (21 : Fin 32) 0x84, 2) := by decide
theorem psm_at_10 : fetchRel p256ScalarMulCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x80, 2) := by decide
theorem psm_at_12 : fetchRel p256ScalarMulCode 0x12 = some (.store .sw sp (23 : Fin 32) 0x7C, 2) := by decide
theorem psm_at_14 : fetchRel p256ScalarMulCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x78, 2) := by decide
theorem psm_at_16 : fetchRel p256ScalarMulCode 0x16 = some (.store .sw sp (25 : Fin 32) 0x74, 2) := by decide
theorem psm_at_18 : fetchRel p256ScalarMulCode 0x18 = some (.store .sw sp (26 : Fin 32) 0x70, 2) := by decide
theorem psm_at_1a : fetchRel p256ScalarMulCode 0x1A = some (.store .sw sp (27 : Fin 32) 0x6C, 2) := by decide
theorem psm_at_1c : fetchRel p256ScalarMulCode 0x1C = some (.store .sw sp a0 0x28, 2) := by decide
theorem psm_at_1e : fetchRel p256ScalarMulCode 0x1E = some (.aluImm .add a0 sp 0x2C, 2) := by decide
theorem psm_at_20 : fetchRel p256ScalarMulCode 0x20 = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem psm_at_24 : fetchRel p256ScalarMulCode 0x24 = some (.jalr ra ra 0x22E, 4) := by decide
theorem psm_at_28 : fetchRel p256ScalarMulCode 0x28 = some (.load .lw a3 sp 0x48, 2) := by decide
theorem psm_at_2a : fetchRel p256ScalarMulCode 0x2A = some (.lui a0 0xEEDFA000, 4) := by decide
theorem psm_at_2e : fetchRel p256ScalarMulCode 0x2E = some (.lui a1 0x1300000, 4) := by decide
theorem psm_at_32 : fetchRel p256ScalarMulCode 0x32 = some (.aluImm .add (5 : Fin 32) a0 0xFFFFFBFE, 4) := by decide
theorem psm_at_36 : fetchRel p256ScalarMulCode 0x36 = some (.aluImm .add (29 : Fin 32) a1 0xFFFFFD85, 4) := by decide
theorem psm_at_3a : fetchRel p256ScalarMulCode 0x3A = some (.alu .mulhu a1 a3 (5 : Fin 32), 4) := by decide
theorem psm_at_3e : fetchRel p256ScalarMulCode 0x3E = some (.alu .mul a2 a3 (29 : Fin 32), 4) := by decide
theorem psm_at_42 : fetchRel p256ScalarMulCode 0x42 = some (.load .lw a4 sp 0x4C, 2) := by decide
theorem psm_at_44 : fetchRel p256ScalarMulCode 0x44 = some (.load .lw (27 : Fin 32) sp 0x50, 2) := by decide
theorem psm_at_46 : fetchRel p256ScalarMulCode 0x46 = some (.load .lw (26 : Fin 32) sp 0x54, 2) := by decide
theorem psm_at_48 : fetchRel p256ScalarMulCode 0x48 = some (.load .lw (19 : Fin 32) sp 0x58, 2) := by decide
theorem psm_at_4a : fetchRel p256ScalarMulCode 0x4A = some (.lui (6 : Fin 32) 0xDF1A7000, 4) := by decide
theorem psm_at_4e : fetchRel p256ScalarMulCode 0x4E = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0xFFFFFC21, 4) := by decide
theorem psm_at_52 : fetchRel p256ScalarMulCode 0x52 = some (.alu .add a0 x0 a3, 2) := by decide
theorem psm_at_54 : fetchRel p256ScalarMulCode 0x54 = some (.alu .mulhu (7 : Fin 32) a3 (29 : Fin 32), 4) := by decide
theorem psm_at_58 : fetchRel p256ScalarMulCode 0x58 = some (.lui a5 0x43190000, 4) := by decide
theorem psm_at_5c : fetchRel p256ScalarMulCode 0x5C = some (.alu .mul (9 : Fin 32) a3 (6 : Fin 32), 4) := by decide
theorem psm_at_60 : fetchRel p256ScalarMulCode 0x60 = some (.aluImm .add (17 : Fin 32) x0 0xFFFFFFFF, 2) := by decide
theorem psm_at_62 : fetchRel p256ScalarMulCode 0x62 = some (.aluImm .add a6 x0 0xFFFFFFFE, 2) := by decide
theorem psm_at_64 : fetchRel p256ScalarMulCode 0x64 = some (.aluImm .add (30 : Fin 32) a5 0x552, 4) := by decide
theorem psm_at_68 : fetchRel p256ScalarMulCode 0x68 = some (.alu .mulhu a5 a3 (6 : Fin 32), 4) := by decide
theorem psm_at_6c : fetchRel p256ScalarMulCode 0x6C = some (.alu .mul (8 : Fin 32) a3 (30 : Fin 32), 4) := by decide
theorem psm_at_70 : fetchRel p256ScalarMulCode 0x70 = some (.alu .add a2 a2 a1, 2) := by decide
theorem psm_at_72 : fetchRel p256ScalarMulCode 0x72 = some (.alu .mulhu a3 a3 (30 : Fin 32), 4) := by decide
theorem psm_at_76 : fetchRel p256ScalarMulCode 0x76 = some (.alu .sltu a1 a2 a1, 4) := by decide
theorem psm_at_7a : fetchRel p256ScalarMulCode 0x7A = some (.alu .mulhu (28 : Fin 32) a0 (17 : Fin 32), 4) := by decide
theorem psm_at_7e : fetchRel p256ScalarMulCode 0x7E = some (.alu .add a1 a1 (7 : Fin 32), 2) := by decide
theorem psm_at_80 : fetchRel p256ScalarMulCode 0x80 = some (.alu .mulhu (7 : Fin 32) a0 a6, 4) := by decide
theorem psm_at_84 : fetchRel p256ScalarMulCode 0x84 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a1, 2) := by decide
theorem psm_at_86 : fetchRel p256ScalarMulCode 0x86 = some (.alu .add (31 : Fin 32) a0 a0, 4) := by decide
theorem psm_at_8a : fetchRel p256ScalarMulCode 0x8A = some (.alu .sltu a1 (9 : Fin 32) a1, 4) := by decide
theorem psm_at_8e : fetchRel p256ScalarMulCode 0x8E = some (.alu .mulhu (18 : Fin 32) a4 (5 : Fin 32), 4) := by decide
theorem psm_at_92 : fetchRel p256ScalarMulCode 0x92 = some (.alu .add a1 a1 a5, 2) := by decide
theorem psm_at_94 : fetchRel p256ScalarMulCode 0x94 = some (.alu .mul (21 : Fin 32) a4 (5 : Fin 32), 4) := by decide
theorem psm_at_98 : fetchRel p256ScalarMulCode 0x98 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a1, 2) := by decide
theorem psm_at_9a : fetchRel p256ScalarMulCode 0x9A = some (.alu .mulhu (20 : Fin 32) a4 (29 : Fin 32), 4) := by decide
theorem psm_at_9e : fetchRel p256ScalarMulCode 0x9E = some (.alu .sltu a1 (8 : Fin 32) a1, 4) := by decide
theorem psm_at_a2 : fetchRel p256ScalarMulCode 0xA2 = some (.alu .mul (23 : Fin 32) a4 (29 : Fin 32), 4) := by decide
theorem psm_at_a6 : fetchRel p256ScalarMulCode 0xA6 = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_a8 : fetchRel p256ScalarMulCode 0xA8 = some (.alu .mulhu (22 : Fin 32) a4 (6 : Fin 32), 4) := by decide
theorem psm_at_ac : fetchRel p256ScalarMulCode 0xAC = some (.alu .sub a3 a1 a0, 4) := by decide
theorem psm_at_b0 : fetchRel p256ScalarMulCode 0xB0 = some (.alu .mul (25 : Fin 32) a4 (6 : Fin 32), 4) := by decide
theorem psm_at_b4 : fetchRel p256ScalarMulCode 0xB4 = some (.alu .sltu a1 a3 a1, 4) := by decide
theorem psm_at_b8 : fetchRel p256ScalarMulCode 0xB8 = some (.alu .mul (24 : Fin 32) a4 (30 : Fin 32), 4) := by decide
theorem psm_at_bc : fetchRel p256ScalarMulCode 0xBC = some (.alu .add a1 a1 (28 : Fin 32), 2) := by decide
theorem psm_at_be : fetchRel p256ScalarMulCode 0xBE = some (.aluImm .and a2 a2 0xFFFFFFFE, 2) := by decide
theorem psm_at_c0 : fetchRel p256ScalarMulCode 0xC0 = some (.alu .sub a5 a1 (31 : Fin 32), 4) := by decide
theorem psm_at_c4 : fetchRel p256ScalarMulCode 0xC4 = some (.alu .add (21 : Fin 32) (21 : Fin 32) a2, 2) := by decide
theorem psm_at_c6 : fetchRel p256ScalarMulCode 0xC6 = some (.alu .sltu a1 a5 a1, 4) := by decide
theorem psm_at_ca : fetchRel p256ScalarMulCode 0xCA = some (.alu .sltu a2 (21 : Fin 32) a2, 4) := by decide
theorem psm_at_ce : fetchRel p256ScalarMulCode 0xCE = some (.alu .add a1 a1 (7 : Fin 32), 2) := by decide
theorem psm_at_d0 : fetchRel p256ScalarMulCode 0xD0 = some (.alu .add a2 a2 (18 : Fin 32), 2) := by decide
theorem psm_at_d2 : fetchRel p256ScalarMulCode 0xD2 = some (.alu .sub (21 : Fin 32) a1 a0, 4) := by decide
theorem psm_at_d6 : fetchRel p256ScalarMulCode 0xD6 = some (.alu .add ra x0 a0, 2) := by decide
theorem psm_at_d8 : fetchRel p256ScalarMulCode 0xD8 = some (.store .sw sp a0 0x24, 2) := by decide
theorem psm_at_da : fetchRel p256ScalarMulCode 0xDA = some (.alu .add (23 : Fin 32) (23 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_dc : fetchRel p256ScalarMulCode 0xDC = some (.alu .sltu a1 (21 : Fin 32) a1, 4) := by decide
theorem psm_at_e0 : fetchRel p256ScalarMulCode 0xE0 = some (.alu .sltu (9 : Fin 32) (23 : Fin 32) (9 : Fin 32), 4) := by decide
theorem psm_at_e4 : fetchRel p256ScalarMulCode 0xE4 = some (.alu .add (7 : Fin 32) (28 : Fin 32) a1, 4) := by decide
theorem psm_at_e8 : fetchRel p256ScalarMulCode 0xE8 = some (.alu .add (9 : Fin 32) (9 : Fin 32) (20 : Fin 32), 2) := by decide
theorem psm_at_ea : fetchRel p256ScalarMulCode 0xEA = some (.alu .add (28 : Fin 32) (23 : Fin 32) a2, 4) := by decide
theorem psm_at_ee : fetchRel p256ScalarMulCode 0xEE = some (.alu .add (25 : Fin 32) (25 : Fin 32) (8 : Fin 32), 2) := by decide
theorem psm_at_f0 : fetchRel p256ScalarMulCode 0xF0 = some (.alu .mulhu a2 a4 (30 : Fin 32), 4) := by decide
theorem psm_at_f4 : fetchRel p256ScalarMulCode 0xF4 = some (.alu .sltu a1 (28 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_f8 : fetchRel p256ScalarMulCode 0xF8 = some (.alu .sltu (8 : Fin 32) (25 : Fin 32) (8 : Fin 32), 4) := by decide
theorem psm_at_fc : fetchRel p256ScalarMulCode 0xFC = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem psm_at_fe : fetchRel p256ScalarMulCode 0xFE = some (.alu .add (8 : Fin 32) (8 : Fin 32) (22 : Fin 32), 2) := by decide
theorem psm_at_100 : fetchRel p256ScalarMulCode 0x100 = some (.alu .add (31 : Fin 32) (25 : Fin 32) a1, 4) := by decide
theorem psm_at_104 : fetchRel p256ScalarMulCode 0x104 = some (.alu .add a0 x0 a4, 2) := by decide
theorem psm_at_106 : fetchRel p256ScalarMulCode 0x106 = some (.alu .mulhu a1 a4 (17 : Fin 32), 4) := by decide
theorem psm_at_10a : fetchRel p256ScalarMulCode 0x10A = some (.alu .sltu (9 : Fin 32) (31 : Fin 32) (25 : Fin 32), 4) := by decide
theorem psm_at_10e : fetchRel p256ScalarMulCode 0x10E = some (.alu .add (24 : Fin 32) (24 : Fin 32) a3, 2) := by decide
theorem psm_at_110 : fetchRel p256ScalarMulCode 0x110 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_112 : fetchRel p256ScalarMulCode 0x112 = some (.alu .sltu a3 (24 : Fin 32) a3, 4) := by decide
theorem psm_at_116 : fetchRel p256ScalarMulCode 0x116 = some (.alu .add a2 a2 a3, 2) := by decide
theorem psm_at_118 : fetchRel p256ScalarMulCode 0x118 = some (.alu .add (18 : Fin 32) (24 : Fin 32) (8 : Fin 32), 4) := by decide
theorem psm_at_11c : fetchRel p256ScalarMulCode 0x11C = some (.alu .sub (8 : Fin 32) a5 a4, 4) := by decide
theorem psm_at_120 : fetchRel p256ScalarMulCode 0x120 = some (.alu .mulhu (9 : Fin 32) a4 a6, 4) := by decide
theorem psm_at_124 : fetchRel p256ScalarMulCode 0x124 = some (.alu .sltu a3 (18 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_128 : fetchRel p256ScalarMulCode 0x128 = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem psm_at_12c : fetchRel p256ScalarMulCode 0x12C = some (.alu .add a2 a2 a3, 2) := by decide
theorem psm_at_12e : fetchRel p256ScalarMulCode 0x12E = some (.alu .add a3 a1 a5, 4) := by decide
theorem psm_at_132 : fetchRel p256ScalarMulCode 0x132 = some (.alu .add (23 : Fin 32) (8 : Fin 32) a2, 4) := by decide
theorem psm_at_136 : fetchRel p256ScalarMulCode 0x136 = some (.alu .add a2 a4 a4, 4) := by decide
theorem psm_at_13a : fetchRel p256ScalarMulCode 0x13A = some (.alu .sltu (8 : Fin 32) (23 : Fin 32) (8 : Fin 32), 4) := by decide
theorem psm_at_13e : fetchRel p256ScalarMulCode 0x13E = some (.alu .sub a2 (21 : Fin 32) a2, 4) := by decide
theorem psm_at_142 : fetchRel p256ScalarMulCode 0x142 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem psm_at_144 : fetchRel p256ScalarMulCode 0x144 = some (.alu .sltu a4 a2 (21 : Fin 32), 4) := by decide
theorem psm_at_148 : fetchRel p256ScalarMulCode 0x148 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a4, 2) := by decide
theorem psm_at_14a : fetchRel p256ScalarMulCode 0x14A = some (.alu .add (22 : Fin 32) a2 a3, 4) := by decide
theorem psm_at_14e : fetchRel p256ScalarMulCode 0x14E = some (.alu .sltu a2 (22 : Fin 32) a2, 4) := by decide
theorem psm_at_152 : fetchRel p256ScalarMulCode 0x152 = some (.alu .sub a3 (7 : Fin 32) a0, 4) := by decide
theorem psm_at_156 : fetchRel p256ScalarMulCode 0x156 = some (.store .sw sp a0 0x20, 2) := by decide
theorem psm_at_158 : fetchRel p256ScalarMulCode 0x158 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem psm_at_15a : fetchRel p256ScalarMulCode 0x15A = some (.alu .sltu (9 : Fin 32) a3 (7 : Fin 32), 4) := by decide
theorem psm_at_15e : fetchRel p256ScalarMulCode 0x15E = some (.alu .add (21 : Fin 32) a3 a2, 4) := by decide
theorem psm_at_162 : fetchRel p256ScalarMulCode 0x162 = some (.alu .mul a2 (27 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_166 : fetchRel p256ScalarMulCode 0x166 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem psm_at_168 : fetchRel p256ScalarMulCode 0x168 = some (.alu .sltu a3 (21 : Fin 32) a3, 4) := by decide
theorem psm_at_16c : fetchRel p256ScalarMulCode 0x16C = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_16e : fetchRel p256ScalarMulCode 0x16E = some (.alu .mul a3 (27 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_172 : fetchRel p256ScalarMulCode 0x172 = some (.alu .add (8 : Fin 32) a1 ra, 4) := by decide
theorem psm_at_176 : fetchRel p256ScalarMulCode 0x176 = some (.alu .mulhu (9 : Fin 32) (27 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_17a : fetchRel p256ScalarMulCode 0x17A = some (.alu .sltu (7 : Fin 32) (8 : Fin 32) a1, 4) := by decide
theorem psm_at_17e : fetchRel p256ScalarMulCode 0x17E = some (.aluImm .and a1 (28 : Fin 32) 0xFFFFFFFE, 4) := by decide
theorem psm_at_182 : fetchRel p256ScalarMulCode 0x182 = some (.alu .mulhu a4 (27 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_186 : fetchRel p256ScalarMulCode 0x186 = some (.alu .add a2 a2 a1, 2) := by decide
theorem psm_at_188 : fetchRel p256ScalarMulCode 0x188 = some (.alu .mul a5 (27 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_18c : fetchRel p256ScalarMulCode 0x18C = some (.alu .add (20 : Fin 32) (7 : Fin 32) a0, 4) := by decide
theorem psm_at_190 : fetchRel p256ScalarMulCode 0x190 = some (.alu .sltu a1 a2 a1, 4) := by decide
theorem psm_at_194 : fetchRel p256ScalarMulCode 0x194 = some (.alu .add a3 a3 (31 : Fin 32), 2) := by decide
theorem psm_at_196 : fetchRel p256ScalarMulCode 0x196 = some (.alu .mulhu a2 (27 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_19a : fetchRel p256ScalarMulCode 0x19A = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem psm_at_19c : fetchRel p256ScalarMulCode 0x19C = some (.alu .sltu (9 : Fin 32) a3 (31 : Fin 32), 4) := by decide
theorem psm_at_1a0 : fetchRel p256ScalarMulCode 0x1A0 = some (.alu .add (31 : Fin 32) a3 a1, 4) := by decide
theorem psm_at_1a4 : fetchRel p256ScalarMulCode 0x1A4 = some (.alu .mul a1 (27 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_1a8 : fetchRel p256ScalarMulCode 0x1A8 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem psm_at_1aa : fetchRel p256ScalarMulCode 0x1AA = some (.alu .sltu a3 (31 : Fin 32) a3, 4) := by decide
theorem psm_at_1ae : fetchRel p256ScalarMulCode 0x1AE = some (.alu .add a5 a5 (18 : Fin 32), 2) := by decide
theorem psm_at_1b0 : fetchRel p256ScalarMulCode 0x1B0 = some (.alu .mulhu (9 : Fin 32) (27 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_1b4 : fetchRel p256ScalarMulCode 0x1B4 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_1b6 : fetchRel p256ScalarMulCode 0x1B6 = some (.alu .sltu a4 a5 (18 : Fin 32), 4) := by decide
theorem psm_at_1ba : fetchRel p256ScalarMulCode 0x1BA = some (.alu .add a2 a2 a4, 2) := by decide
theorem psm_at_1bc : fetchRel p256ScalarMulCode 0x1BC = some (.alu .add ra a5 a3, 4) := by decide
theorem psm_at_1c0 : fetchRel p256ScalarMulCode 0x1C0 = some (.alu .sltu a4 ra a5, 4) := by decide
theorem psm_at_1c4 : fetchRel p256ScalarMulCode 0x1C4 = some (.alu .mulhu a5 (27 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_1c8 : fetchRel p256ScalarMulCode 0x1C8 = some (.alu .add a2 a2 a4, 2) := by decide
theorem psm_at_1ca : fetchRel p256ScalarMulCode 0x1CA = some (.alu .add a1 a1 (23 : Fin 32), 2) := by decide
theorem psm_at_1cc : fetchRel p256ScalarMulCode 0x1CC = some (.alu .sltu a4 a1 (23 : Fin 32), 4) := by decide
theorem psm_at_1d0 : fetchRel p256ScalarMulCode 0x1D0 = some (.alu .add (24 : Fin 32) a1 a2, 4) := by decide
theorem psm_at_1d4 : fetchRel p256ScalarMulCode 0x1D4 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem psm_at_1d6 : fetchRel p256ScalarMulCode 0x1D6 = some (.alu .sltu a1 (24 : Fin 32) a1, 4) := by decide
theorem psm_at_1da : fetchRel p256ScalarMulCode 0x1DA = some (.alu .sub a2 (22 : Fin 32) (27 : Fin 32), 4) := by decide
theorem psm_at_1de : fetchRel p256ScalarMulCode 0x1DE = some (.alu .mulhu (9 : Fin 32) (27 : Fin 32) a6, 4) := by decide
theorem psm_at_1e2 : fetchRel p256ScalarMulCode 0x1E2 = some (.alu .add a1 a1 a4, 2) := by decide
theorem psm_at_1e4 : fetchRel p256ScalarMulCode 0x1E4 = some (.alu .sltu a4 a2 (22 : Fin 32), 4) := by decide
theorem psm_at_1e8 : fetchRel p256ScalarMulCode 0x1E8 = some (.alu .add a4 a4 a5, 2) := by decide
theorem psm_at_1ea : fetchRel p256ScalarMulCode 0x1EA = some (.alu .add (25 : Fin 32) a2 a1, 4) := by decide
theorem psm_at_1ee : fetchRel p256ScalarMulCode 0x1EE = some (.alu .sltu a2 (25 : Fin 32) a2, 4) := by decide
theorem psm_at_1f2 : fetchRel p256ScalarMulCode 0x1F2 = some (.alu .add a0 (27 : Fin 32) (27 : Fin 32), 4) := by decide
theorem psm_at_1f6 : fetchRel p256ScalarMulCode 0x1F6 = some (.alu .add a2 a2 a4, 2) := by decide
theorem psm_at_1f8 : fetchRel p256ScalarMulCode 0x1F8 = some (.alu .sub a0 (21 : Fin 32) a0, 4) := by decide
theorem psm_at_1fc : fetchRel p256ScalarMulCode 0x1FC = some (.alu .sltu a4 a0 (21 : Fin 32), 4) := by decide
theorem psm_at_200 : fetchRel p256ScalarMulCode 0x200 = some (.alu .add (23 : Fin 32) a0 a2, 4) := by decide
theorem psm_at_204 : fetchRel p256ScalarMulCode 0x204 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem psm_at_206 : fetchRel p256ScalarMulCode 0x206 = some (.alu .sltu a0 (23 : Fin 32) a0, 4) := by decide
theorem psm_at_20a : fetchRel p256ScalarMulCode 0x20A = some (.alu .add a0 a0 a4, 2) := by decide
theorem psm_at_20c : fetchRel p256ScalarMulCode 0x20C = some (.alu .sub a2 (8 : Fin 32) (27 : Fin 32), 4) := by decide
theorem psm_at_210 : fetchRel p256ScalarMulCode 0x210 = some (.alu .sltu a4 a2 (8 : Fin 32), 4) := by decide
theorem psm_at_214 : fetchRel p256ScalarMulCode 0x214 = some (.alu .add (22 : Fin 32) a2 a0, 4) := by decide
theorem psm_at_218 : fetchRel p256ScalarMulCode 0x218 = some (.alu .add a4 a4 a5, 2) := by decide
theorem psm_at_21a : fetchRel p256ScalarMulCode 0x21A = some (.alu .sltu a0 (22 : Fin 32) a2, 4) := by decide
theorem psm_at_21e : fetchRel p256ScalarMulCode 0x21E = some (.alu .sltu a2 (20 : Fin 32) (7 : Fin 32), 4) := by decide
theorem psm_at_222 : fetchRel p256ScalarMulCode 0x222 = some (.alu .add a0 a0 a4, 2) := by decide
theorem psm_at_224 : fetchRel p256ScalarMulCode 0x224 = some (.alu .add (20 : Fin 32) (20 : Fin 32) a0, 2) := by decide
theorem psm_at_226 : fetchRel p256ScalarMulCode 0x226 = some (.alu .mul a4 (26 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_22a : fetchRel p256ScalarMulCode 0x22A = some (.alu .sltu (28 : Fin 32) (20 : Fin 32) a0, 4) := by decide
theorem psm_at_22e : fetchRel p256ScalarMulCode 0x22E = some (.alu .add (27 : Fin 32) (27 : Fin 32) a2, 2) := by decide
theorem psm_at_230 : fetchRel p256ScalarMulCode 0x230 = some (.alu .add (28 : Fin 32) (28 : Fin 32) (27 : Fin 32), 2) := by decide
theorem psm_at_232 : fetchRel p256ScalarMulCode 0x232 = some (.alu .sltu (7 : Fin 32) (27 : Fin 32) a2, 4) := by decide
theorem psm_at_236 : fetchRel p256ScalarMulCode 0x236 = some (.alu .sltu a0 (28 : Fin 32) (27 : Fin 32), 4) := by decide
theorem psm_at_23a : fetchRel p256ScalarMulCode 0x23A = some (.alu .add (7 : Fin 32) (7 : Fin 32) a0, 2) := by decide
theorem psm_at_23c : fetchRel p256ScalarMulCode 0x23C = some (.alu .mul a5 (26 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_240 : fetchRel p256ScalarMulCode 0x240 = some (.aluImm .and (8 : Fin 32) (31 : Fin 32) 0xFFFFFFFE, 4) := by decide
theorem psm_at_244 : fetchRel p256ScalarMulCode 0x244 = some (.alu .mulhu (9 : Fin 32) (26 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_248 : fetchRel p256ScalarMulCode 0x248 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem psm_at_24a : fetchRel p256ScalarMulCode 0x24A = some (.alu .mulhu a1 (26 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_24e : fetchRel p256ScalarMulCode 0x24E = some (.alu .mul a3 (26 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_252 : fetchRel p256ScalarMulCode 0x252 = some (.load .lw a2 sp 0x5C, 2) := by decide
theorem psm_at_254 : fetchRel p256ScalarMulCode 0x254 = some (.load .lw (27 : Fin 32) sp 0x60, 2) := by decide
theorem psm_at_256 : fetchRel p256ScalarMulCode 0x256 = some (.load .lw (18 : Fin 32) sp 0x64, 2) := by decide
theorem psm_at_258 : fetchRel p256ScalarMulCode 0x258 = some (.load .lw (31 : Fin 32) sp 0x68, 2) := by decide
theorem psm_at_25a : fetchRel p256ScalarMulCode 0x25A = some (.alu .sltu a4 a4 (8 : Fin 32), 4) := by decide
theorem psm_at_25e : fetchRel p256ScalarMulCode 0x25E = some (.alu .add a5 a5 ra, 2) := by decide
theorem psm_at_260 : fetchRel p256ScalarMulCode 0x260 = some (.alu .mulhu (8 : Fin 32) (26 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_264 : fetchRel p256ScalarMulCode 0x264 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem psm_at_266 : fetchRel p256ScalarMulCode 0x266 = some (.alu .sltu (9 : Fin 32) a5 ra, 4) := by decide
theorem psm_at_26a : fetchRel p256ScalarMulCode 0x26A = some (.alu .add (21 : Fin 32) a5 a4, 4) := by decide
theorem psm_at_26e : fetchRel p256ScalarMulCode 0x26E = some (.alu .mul a4 (26 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_272 : fetchRel p256ScalarMulCode 0x272 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem psm_at_274 : fetchRel p256ScalarMulCode 0x274 = some (.alu .sltu a5 (21 : Fin 32) a5, 4) := by decide
theorem psm_at_278 : fetchRel p256ScalarMulCode 0x278 = some (.alu .add a3 a3 (24 : Fin 32), 2) := by decide
theorem psm_at_27a : fetchRel p256ScalarMulCode 0x27A = some (.alu .mulhu a0 (26 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_27e : fetchRel p256ScalarMulCode 0x27E = some (.alu .add a1 a1 a5, 2) := by decide
theorem psm_at_280 : fetchRel p256ScalarMulCode 0x280 = some (.alu .sltu a5 a3 (24 : Fin 32), 4) := by decide
theorem psm_at_284 : fetchRel p256ScalarMulCode 0x284 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_286 : fetchRel p256ScalarMulCode 0x286 = some (.alu .add (9 : Fin 32) a3 a1, 4) := by decide
theorem psm_at_28a : fetchRel p256ScalarMulCode 0x28A = some (.alu .sltu a1 (9 : Fin 32) a3, 4) := by decide
theorem psm_at_28e : fetchRel p256ScalarMulCode 0x28E = some (.alu .mulhu (8 : Fin 32) (26 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_292 : fetchRel p256ScalarMulCode 0x292 = some (.alu .add a1 a1 a5, 2) := by decide
theorem psm_at_294 : fetchRel p256ScalarMulCode 0x294 = some (.alu .add a4 a4 (25 : Fin 32), 2) := by decide
theorem psm_at_296 : fetchRel p256ScalarMulCode 0x296 = some (.alu .sltu a5 a4 (25 : Fin 32), 4) := by decide
theorem psm_at_29a : fetchRel p256ScalarMulCode 0x29A = some (.alu .add ra a4 a1, 4) := by decide
theorem psm_at_29e : fetchRel p256ScalarMulCode 0x29E = some (.alu .add a0 a0 a5, 2) := by decide
theorem psm_at_2a0 : fetchRel p256ScalarMulCode 0x2A0 = some (.alu .sltu a1 ra a4, 4) := by decide
theorem psm_at_2a4 : fetchRel p256ScalarMulCode 0x2A4 = some (.alu .sub a4 (23 : Fin 32) (26 : Fin 32), 4) := by decide
theorem psm_at_2a8 : fetchRel p256ScalarMulCode 0x2A8 = some (.alu .mulhu a5 (26 : Fin 32) a6, 4) := by decide
theorem psm_at_2ac : fetchRel p256ScalarMulCode 0x2AC = some (.alu .add a0 a0 a1, 2) := by decide
theorem psm_at_2ae : fetchRel p256ScalarMulCode 0x2AE = some (.alu .sltu a1 a4 (23 : Fin 32), 4) := by decide
theorem psm_at_2b2 : fetchRel p256ScalarMulCode 0x2B2 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem psm_at_2b4 : fetchRel p256ScalarMulCode 0x2B4 = some (.alu .add (23 : Fin 32) a4 a0, 4) := by decide
theorem psm_at_2b8 : fetchRel p256ScalarMulCode 0x2B8 = some (.alu .sltu a4 (23 : Fin 32) a4, 4) := by decide
theorem psm_at_2bc : fetchRel p256ScalarMulCode 0x2BC = some (.alu .add a0 (26 : Fin 32) (26 : Fin 32), 4) := by decide
theorem psm_at_2c0 : fetchRel p256ScalarMulCode 0x2C0 = some (.alu .add a1 a1 a4, 2) := by decide
theorem psm_at_2c2 : fetchRel p256ScalarMulCode 0x2C2 = some (.alu .sub a0 (22 : Fin 32) a0, 4) := by decide
theorem psm_at_2c6 : fetchRel p256ScalarMulCode 0x2C6 = some (.alu .sltu a4 a0 (22 : Fin 32), 4) := by decide
theorem psm_at_2ca : fetchRel p256ScalarMulCode 0x2CA = some (.alu .add (25 : Fin 32) a0 a1, 4) := by decide
theorem psm_at_2ce : fetchRel p256ScalarMulCode 0x2CE = some (.alu .add a4 a4 a5, 2) := by decide
theorem psm_at_2d0 : fetchRel p256ScalarMulCode 0x2D0 = some (.alu .sltu a0 (25 : Fin 32) a0, 4) := by decide
theorem psm_at_2d4 : fetchRel p256ScalarMulCode 0x2D4 = some (.alu .add a0 a0 a4, 2) := by decide
theorem psm_at_2d6 : fetchRel p256ScalarMulCode 0x2D6 = some (.alu .sub a4 (20 : Fin 32) (26 : Fin 32), 4) := by decide
theorem psm_at_2da : fetchRel p256ScalarMulCode 0x2DA = some (.alu .sltu a5 a4 (20 : Fin 32), 4) := by decide
theorem psm_at_2de : fetchRel p256ScalarMulCode 0x2DE = some (.alu .add (24 : Fin 32) a4 a0, 4) := by decide
theorem psm_at_2e2 : fetchRel p256ScalarMulCode 0x2E2 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_2e4 : fetchRel p256ScalarMulCode 0x2E4 = some (.alu .sltu a4 (24 : Fin 32) a4, 4) := by decide
theorem psm_at_2e8 : fetchRel p256ScalarMulCode 0x2E8 = some (.alu .add a4 a4 a5, 2) := by decide
theorem psm_at_2ea : fetchRel p256ScalarMulCode 0x2EA = some (.alu .mul a5 (19 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_2ee : fetchRel p256ScalarMulCode 0x2EE = some (.alu .add (28 : Fin 32) (28 : Fin 32) a4, 2) := by decide
theorem psm_at_2f0 : fetchRel p256ScalarMulCode 0x2F0 = some (.alu .add (26 : Fin 32) (26 : Fin 32) (7 : Fin 32), 2) := by decide
theorem psm_at_2f2 : fetchRel p256ScalarMulCode 0x2F2 = some (.alu .mulhu (8 : Fin 32) (19 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_2f6 : fetchRel p256ScalarMulCode 0x2F6 = some (.alu .mul a0 (19 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_2fa : fetchRel p256ScalarMulCode 0x2FA = some (.alu .sltu (20 : Fin 32) (28 : Fin 32) a4, 4) := by decide
theorem psm_at_2fe : fetchRel p256ScalarMulCode 0x2FE = some (.alu .sltu (7 : Fin 32) (26 : Fin 32) (7 : Fin 32), 4) := by decide
theorem psm_at_302 : fetchRel p256ScalarMulCode 0x302 = some (.alu .add (20 : Fin 32) (20 : Fin 32) (26 : Fin 32), 2) := by decide
theorem psm_at_304 : fetchRel p256ScalarMulCode 0x304 = some (.alu .mulhu a4 (19 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_308 : fetchRel p256ScalarMulCode 0x308 = some (.aluImm .and a1 (21 : Fin 32) 0xFFFFFFFE, 4) := by decide
theorem psm_at_30c : fetchRel p256ScalarMulCode 0x30C = some (.alu .mul a3 (19 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_310 : fetchRel p256ScalarMulCode 0x310 = some (.alu .sltu (21 : Fin 32) (20 : Fin 32) (26 : Fin 32), 4) := by decide
theorem psm_at_314 : fetchRel p256ScalarMulCode 0x314 = some (.alu .add a5 a5 a1, 2) := by decide
theorem psm_at_316 : fetchRel p256ScalarMulCode 0x316 = some (.alu .sltu a1 a5 a1, 4) := by decide
theorem psm_at_31a : fetchRel p256ScalarMulCode 0x31A = some (.alu .mulhu a5 (19 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_31e : fetchRel p256ScalarMulCode 0x31E = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem psm_at_320 : fetchRel p256ScalarMulCode 0x320 = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem psm_at_322 : fetchRel p256ScalarMulCode 0x322 = some (.alu .sltu (8 : Fin 32) a0 (9 : Fin 32), 4) := by decide
theorem psm_at_326 : fetchRel p256ScalarMulCode 0x326 = some (.alu .mul (9 : Fin 32) (19 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_32a : fetchRel p256ScalarMulCode 0x32A = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem psm_at_32c : fetchRel p256ScalarMulCode 0x32C = some (.alu .add (22 : Fin 32) a0 a1, 4) := by decide
theorem psm_at_330 : fetchRel p256ScalarMulCode 0x330 = some (.alu .add a3 a3 ra, 2) := by decide
theorem psm_at_332 : fetchRel p256ScalarMulCode 0x332 = some (.alu .mulhu a1 (19 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_336 : fetchRel p256ScalarMulCode 0x336 = some (.alu .sltu a0 (22 : Fin 32) a0, 4) := by decide
theorem psm_at_33a : fetchRel p256ScalarMulCode 0x33A = some (.alu .sltu (8 : Fin 32) a3 ra, 4) := by decide
theorem psm_at_33e : fetchRel p256ScalarMulCode 0x33E = some (.alu .add a0 a0 a4, 2) := by decide
theorem psm_at_340 : fetchRel p256ScalarMulCode 0x340 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_342 : fetchRel p256ScalarMulCode 0x342 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_344 : fetchRel p256ScalarMulCode 0x344 = some (.alu .mulhu a4 (19 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_348 : fetchRel p256ScalarMulCode 0x348 = some (.alu .sltu a3 a0 a3, 4) := by decide
theorem psm_at_34c : fetchRel p256ScalarMulCode 0x34C = some (.alu .add (9 : Fin 32) (9 : Fin 32) (23 : Fin 32), 2) := by decide
theorem psm_at_34e : fetchRel p256ScalarMulCode 0x34E = some (.alu .add a3 a3 a5, 2) := by decide
theorem psm_at_350 : fetchRel p256ScalarMulCode 0x350 = some (.alu .sltu a5 (9 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_354 : fetchRel p256ScalarMulCode 0x354 = some (.alu .add a1 a1 a5, 2) := by decide
theorem psm_at_356 : fetchRel p256ScalarMulCode 0x356 = some (.alu .add (23 : Fin 32) (9 : Fin 32) a3, 4) := by decide
theorem psm_at_35a : fetchRel p256ScalarMulCode 0x35A = some (.alu .sub a5 (25 : Fin 32) (19 : Fin 32), 4) := by decide
theorem psm_at_35e : fetchRel p256ScalarMulCode 0x35E = some (.alu .mulhu (8 : Fin 32) (19 : Fin 32) a6, 4) := by decide
theorem psm_at_362 : fetchRel p256ScalarMulCode 0x362 = some (.alu .sltu (9 : Fin 32) (23 : Fin 32) (9 : Fin 32), 4) := by decide
theorem psm_at_366 : fetchRel p256ScalarMulCode 0x366 = some (.alu .sltu a3 a5 (25 : Fin 32), 4) := by decide
theorem psm_at_36a : fetchRel p256ScalarMulCode 0x36A = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem psm_at_36c : fetchRel p256ScalarMulCode 0x36C = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_36e : fetchRel p256ScalarMulCode 0x36E = some (.alu .add (26 : Fin 32) a5 a1, 4) := by decide
theorem psm_at_372 : fetchRel p256ScalarMulCode 0x372 = some (.alu .add a1 (19 : Fin 32) (19 : Fin 32), 4) := by decide
theorem psm_at_376 : fetchRel p256ScalarMulCode 0x376 = some (.alu .sltu a5 (26 : Fin 32) a5, 4) := by decide
theorem psm_at_37a : fetchRel p256ScalarMulCode 0x37A = some (.alu .sub a1 (24 : Fin 32) a1, 4) := by decide
theorem psm_at_37e : fetchRel p256ScalarMulCode 0x37E = some (.alu .add a3 a3 a5, 2) := by decide
theorem psm_at_380 : fetchRel p256ScalarMulCode 0x380 = some (.alu .sltu a5 a1 (24 : Fin 32), 4) := by decide
theorem psm_at_384 : fetchRel p256ScalarMulCode 0x384 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_386 : fetchRel p256ScalarMulCode 0x386 = some (.alu .add (24 : Fin 32) a1 a3, 4) := by decide
theorem psm_at_38a : fetchRel p256ScalarMulCode 0x38A = some (.alu .sltu a1 (24 : Fin 32) a1, 4) := by decide
theorem psm_at_38e : fetchRel p256ScalarMulCode 0x38E = some (.alu .sub (8 : Fin 32) (28 : Fin 32) (19 : Fin 32), 4) := by decide
theorem psm_at_392 : fetchRel p256ScalarMulCode 0x392 = some (.alu .add a1 a1 a5, 2) := by decide
theorem psm_at_394 : fetchRel p256ScalarMulCode 0x394 = some (.alu .sltu a5 (8 : Fin 32) (28 : Fin 32), 4) := by decide
theorem psm_at_398 : fetchRel p256ScalarMulCode 0x398 = some (.alu .add a5 a5 a4, 2) := by decide
theorem psm_at_39a : fetchRel p256ScalarMulCode 0x39A = some (.alu .add (25 : Fin 32) (8 : Fin 32) a1, 4) := by decide
theorem psm_at_39e : fetchRel p256ScalarMulCode 0x39E = some (.alu .sltu a1 (25 : Fin 32) (8 : Fin 32), 4) := by decide
theorem psm_at_3a2 : fetchRel p256ScalarMulCode 0x3A2 = some (.alu .mul (8 : Fin 32) a2 (5 : Fin 32), 4) := by decide
theorem psm_at_3a6 : fetchRel p256ScalarMulCode 0x3A6 = some (.alu .add (7 : Fin 32) (7 : Fin 32) (21 : Fin 32), 2) := by decide
theorem psm_at_3a8 : fetchRel p256ScalarMulCode 0x3A8 = some (.alu .add a1 a1 a5, 2) := by decide
theorem psm_at_3aa : fetchRel p256ScalarMulCode 0x3AA = some (.alu .add (20 : Fin 32) (20 : Fin 32) a1, 2) := by decide
theorem psm_at_3ac : fetchRel p256ScalarMulCode 0x3AC = some (.alu .mul a5 a2 (29 : Fin 32), 4) := by decide
theorem psm_at_3b0 : fetchRel p256ScalarMulCode 0x3B0 = some (.alu .add (19 : Fin 32) (19 : Fin 32) (7 : Fin 32), 2) := by decide
theorem psm_at_3b2 : fetchRel p256ScalarMulCode 0x3B2 = some (.alu .mulhu a3 a2 (5 : Fin 32), 4) := by decide
theorem psm_at_3b6 : fetchRel p256ScalarMulCode 0x3B6 = some (.alu .sltu (21 : Fin 32) (20 : Fin 32) a1, 4) := by decide
theorem psm_at_3ba : fetchRel p256ScalarMulCode 0x3BA = some (.alu .sltu (7 : Fin 32) (19 : Fin 32) (7 : Fin 32), 4) := by decide
theorem psm_at_3be : fetchRel p256ScalarMulCode 0x3BE = some (.aluImm .and a1 (22 : Fin 32) 0xFFFFFFFE, 4) := by decide
theorem psm_at_3c2 : fetchRel p256ScalarMulCode 0x3C2 = some (.alu .mulhu a4 a2 (29 : Fin 32), 4) := by decide
theorem psm_at_3c6 : fetchRel p256ScalarMulCode 0x3C6 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a1, 2) := by decide
theorem psm_at_3c8 : fetchRel p256ScalarMulCode 0x3C8 = some (.alu .mul (9 : Fin 32) a2 (6 : Fin 32), 4) := by decide
theorem psm_at_3cc : fetchRel p256ScalarMulCode 0x3CC = some (.alu .add (21 : Fin 32) (21 : Fin 32) (19 : Fin 32), 2) := by decide
theorem psm_at_3ce : fetchRel p256ScalarMulCode 0x3CE = some (.alu .sltu a1 (8 : Fin 32) a1, 4) := by decide
theorem psm_at_3d2 : fetchRel p256ScalarMulCode 0x3D2 = some (.alu .add a5 a5 a0, 2) := by decide
theorem psm_at_3d4 : fetchRel p256ScalarMulCode 0x3D4 = some (.alu .mulhu (8 : Fin 32) a2 (6 : Fin 32), 4) := by decide
theorem psm_at_3d8 : fetchRel p256ScalarMulCode 0x3D8 = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_3da : fetchRel p256ScalarMulCode 0x3DA = some (.alu .sltu a0 a5 a0, 4) := by decide
theorem psm_at_3de : fetchRel p256ScalarMulCode 0x3DE = some (.alu .add (28 : Fin 32) a5 a1, 4) := by decide
theorem psm_at_3e2 : fetchRel p256ScalarMulCode 0x3E2 = some (.alu .mul a1 a2 (30 : Fin 32), 4) := by decide
theorem psm_at_3e6 : fetchRel p256ScalarMulCode 0x3E6 = some (.alu .add a0 a0 a4, 2) := by decide
theorem psm_at_3e8 : fetchRel p256ScalarMulCode 0x3E8 = some (.alu .sltu a3 (28 : Fin 32) a5, 4) := by decide
theorem psm_at_3ec : fetchRel p256ScalarMulCode 0x3EC = some (.alu .add (9 : Fin 32) (9 : Fin 32) (23 : Fin 32), 2) := by decide
theorem psm_at_3ee : fetchRel p256ScalarMulCode 0x3EE = some (.alu .mulhu a4 a2 (30 : Fin 32), 4) := by decide
theorem psm_at_3f2 : fetchRel p256ScalarMulCode 0x3F2 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_3f4 : fetchRel p256ScalarMulCode 0x3F4 = some (.alu .sltu a3 (9 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_3f8 : fetchRel p256ScalarMulCode 0x3F8 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem psm_at_3fa : fetchRel p256ScalarMulCode 0x3FA = some (.alu .add ra (9 : Fin 32) a0, 4) := by decide
theorem psm_at_3fe : fetchRel p256ScalarMulCode 0x3FE = some (.alu .sltu a0 ra (9 : Fin 32), 4) := by decide
theorem psm_at_402 : fetchRel p256ScalarMulCode 0x402 = some (.alu .mulhu (8 : Fin 32) a2 (17 : Fin 32), 4) := by decide
theorem psm_at_406 : fetchRel p256ScalarMulCode 0x406 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_408 : fetchRel p256ScalarMulCode 0x408 = some (.alu .add a1 a1 (26 : Fin 32), 2) := by decide
theorem psm_at_40a : fetchRel p256ScalarMulCode 0x40A = some (.alu .sltu a3 a1 (26 : Fin 32), 4) := by decide
theorem psm_at_40e : fetchRel p256ScalarMulCode 0x40E = some (.alu .add (26 : Fin 32) a1 a0, 4) := by decide
theorem psm_at_412 : fetchRel p256ScalarMulCode 0x412 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_414 : fetchRel p256ScalarMulCode 0x414 = some (.alu .sltu a0 (26 : Fin 32) a1, 4) := by decide
theorem psm_at_418 : fetchRel p256ScalarMulCode 0x418 = some (.alu .sub a1 (24 : Fin 32) a2, 4) := by decide
theorem psm_at_41c : fetchRel p256ScalarMulCode 0x41C = some (.alu .mulhu a4 a2 a6, 4) := by decide
theorem psm_at_420 : fetchRel p256ScalarMulCode 0x420 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_422 : fetchRel p256ScalarMulCode 0x422 = some (.alu .sltu a3 a1 (24 : Fin 32), 4) := by decide
theorem psm_at_426 : fetchRel p256ScalarMulCode 0x426 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem psm_at_428 : fetchRel p256ScalarMulCode 0x428 = some (.alu .add (22 : Fin 32) a1 a0, 4) := by decide
theorem psm_at_42c : fetchRel p256ScalarMulCode 0x42C = some (.alu .sltu a1 (22 : Fin 32) a1, 4) := by decide
theorem psm_at_430 : fetchRel p256ScalarMulCode 0x430 = some (.alu .add a0 a2 a2, 4) := by decide
theorem psm_at_434 : fetchRel p256ScalarMulCode 0x434 = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_436 : fetchRel p256ScalarMulCode 0x436 = some (.alu .sub a0 (25 : Fin 32) a0, 4) := by decide
theorem psm_at_43a : fetchRel p256ScalarMulCode 0x43A = some (.alu .sltu a3 a0 (25 : Fin 32), 4) := by decide
theorem psm_at_43e : fetchRel p256ScalarMulCode 0x43E = some (.alu .add (23 : Fin 32) a0 a1, 4) := by decide
theorem psm_at_442 : fetchRel p256ScalarMulCode 0x442 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_444 : fetchRel p256ScalarMulCode 0x444 = some (.alu .sltu a0 (23 : Fin 32) a0, 4) := by decide
theorem psm_at_448 : fetchRel p256ScalarMulCode 0x448 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_44a : fetchRel p256ScalarMulCode 0x44A = some (.alu .sub a3 (20 : Fin 32) a2, 4) := by decide
theorem psm_at_44e : fetchRel p256ScalarMulCode 0x44E = some (.alu .sltu a1 a3 (20 : Fin 32), 4) := by decide
theorem psm_at_452 : fetchRel p256ScalarMulCode 0x452 = some (.alu .add (20 : Fin 32) a3 a0, 4) := by decide
theorem psm_at_456 : fetchRel p256ScalarMulCode 0x456 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem psm_at_458 : fetchRel p256ScalarMulCode 0x458 = some (.alu .sltu a0 (20 : Fin 32) a3, 4) := by decide
theorem psm_at_45c : fetchRel p256ScalarMulCode 0x45C = some (.alu .sltu a3 (21 : Fin 32) (19 : Fin 32), 4) := by decide
theorem psm_at_460 : fetchRel p256ScalarMulCode 0x460 = some (.alu .add a0 a0 a1, 2) := by decide
theorem psm_at_462 : fetchRel p256ScalarMulCode 0x462 = some (.alu .add (21 : Fin 32) (21 : Fin 32) a0, 2) := by decide
theorem psm_at_464 : fetchRel p256ScalarMulCode 0x464 = some (.alu .mul a1 (27 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_468 : fetchRel p256ScalarMulCode 0x468 = some (.alu .add a3 a3 (7 : Fin 32), 2) := by decide
theorem psm_at_46a : fetchRel p256ScalarMulCode 0x46A = some (.alu .sltu (7 : Fin 32) (21 : Fin 32) a0, 4) := by decide
theorem psm_at_46e : fetchRel p256ScalarMulCode 0x46E = some (.alu .add a2 a2 a3, 2) := by decide
theorem psm_at_470 : fetchRel p256ScalarMulCode 0x470 = some (.alu .mul a0 (27 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_474 : fetchRel p256ScalarMulCode 0x474 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a2, 2) := by decide
theorem psm_at_476 : fetchRel p256ScalarMulCode 0x476 = some (.alu .mulhu (8 : Fin 32) (27 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_47a : fetchRel p256ScalarMulCode 0x47A = some (.alu .sltu a3 a2 a3, 4) := by decide
theorem psm_at_47e : fetchRel p256ScalarMulCode 0x47E = some (.alu .sltu a2 (7 : Fin 32) a2, 4) := by decide
theorem psm_at_482 : fetchRel p256ScalarMulCode 0x482 = some (.aluImm .and a4 (28 : Fin 32) 0xFFFFFFFE, 4) := by decide
theorem psm_at_486 : fetchRel p256ScalarMulCode 0x486 = some (.alu .mulhu (9 : Fin 32) (27 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_48a : fetchRel p256ScalarMulCode 0x48A = some (.alu .add a1 a1 a4, 2) := by decide
theorem psm_at_48c : fetchRel p256ScalarMulCode 0x48C = some (.alu .mul a5 (27 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_490 : fetchRel p256ScalarMulCode 0x490 = some (.alu .add (28 : Fin 32) a3 a2, 4) := by decide
theorem psm_at_494 : fetchRel p256ScalarMulCode 0x494 = some (.alu .sltu a1 a1 a4, 4) := by decide
theorem psm_at_498 : fetchRel p256ScalarMulCode 0x498 = some (.alu .add a0 a0 ra, 2) := by decide
theorem psm_at_49a : fetchRel p256ScalarMulCode 0x49A = some (.alu .mulhu a2 (27 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_49e : fetchRel p256ScalarMulCode 0x49E = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem psm_at_4a0 : fetchRel p256ScalarMulCode 0x4A0 = some (.alu .sltu a3 a0 ra, 4) := by decide
theorem psm_at_4a4 : fetchRel p256ScalarMulCode 0x4A4 = some (.alu .add (19 : Fin 32) a0 a1, 4) := by decide
theorem psm_at_4a8 : fetchRel p256ScalarMulCode 0x4A8 = some (.alu .mul a1 (27 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_4ac : fetchRel p256ScalarMulCode 0x4AC = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem psm_at_4ae : fetchRel p256ScalarMulCode 0x4AE = some (.alu .sltu a0 (19 : Fin 32) a0, 4) := by decide
theorem psm_at_4b2 : fetchRel p256ScalarMulCode 0x4B2 = some (.alu .add a5 a5 (26 : Fin 32), 2) := by decide
theorem psm_at_4b4 : fetchRel p256ScalarMulCode 0x4B4 = some (.alu .mulhu a4 (27 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_4b8 : fetchRel p256ScalarMulCode 0x4B8 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_4ba : fetchRel p256ScalarMulCode 0x4BA = some (.alu .sltu a3 a5 (26 : Fin 32), 4) := by decide
theorem psm_at_4be : fetchRel p256ScalarMulCode 0x4BE = some (.alu .add a3 a3 a2, 2) := by decide
theorem psm_at_4c0 : fetchRel p256ScalarMulCode 0x4C0 = some (.alu .add a2 a5 a0, 4) := by decide
theorem psm_at_4c4 : fetchRel p256ScalarMulCode 0x4C4 = some (.alu .sltu a0 a2 a5, 4) := by decide
theorem psm_at_4c8 : fetchRel p256ScalarMulCode 0x4C8 = some (.alu .mulhu (8 : Fin 32) (27 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_4cc : fetchRel p256ScalarMulCode 0x4CC = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_4ce : fetchRel p256ScalarMulCode 0x4CE = some (.alu .add a1 a1 (22 : Fin 32), 2) := by decide
theorem psm_at_4d0 : fetchRel p256ScalarMulCode 0x4D0 = some (.alu .sltu a3 a1 (22 : Fin 32), 4) := by decide
theorem psm_at_4d4 : fetchRel p256ScalarMulCode 0x4D4 = some (.alu .add a5 a1 a0, 4) := by decide
theorem psm_at_4d8 : fetchRel p256ScalarMulCode 0x4D8 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_4da : fetchRel p256ScalarMulCode 0x4DA = some (.alu .sltu a0 a5 a1, 4) := by decide
theorem psm_at_4de : fetchRel p256ScalarMulCode 0x4DE = some (.alu .sub a1 (23 : Fin 32) (27 : Fin 32), 4) := by decide
theorem psm_at_4e2 : fetchRel p256ScalarMulCode 0x4E2 = some (.alu .mulhu a4 (27 : Fin 32) a6, 4) := by decide
theorem psm_at_4e6 : fetchRel p256ScalarMulCode 0x4E6 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_4e8 : fetchRel p256ScalarMulCode 0x4E8 = some (.alu .sltu a3 a1 (23 : Fin 32), 4) := by decide
theorem psm_at_4ec : fetchRel p256ScalarMulCode 0x4EC = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem psm_at_4ee : fetchRel p256ScalarMulCode 0x4EE = some (.alu .add (23 : Fin 32) a1 a0, 4) := by decide
theorem psm_at_4f2 : fetchRel p256ScalarMulCode 0x4F2 = some (.alu .sltu a0 (23 : Fin 32) a1, 4) := by decide
theorem psm_at_4f6 : fetchRel p256ScalarMulCode 0x4F6 = some (.alu .add a1 (27 : Fin 32) (27 : Fin 32), 4) := by decide
theorem psm_at_4fa : fetchRel p256ScalarMulCode 0x4FA = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_4fc : fetchRel p256ScalarMulCode 0x4FC = some (.alu .sub a1 (20 : Fin 32) a1, 4) := by decide
theorem psm_at_500 : fetchRel p256ScalarMulCode 0x500 = some (.alu .sltu a3 a1 (20 : Fin 32), 4) := by decide
theorem psm_at_504 : fetchRel p256ScalarMulCode 0x504 = some (.alu .add (22 : Fin 32) a1 a0, 4) := by decide
theorem psm_at_508 : fetchRel p256ScalarMulCode 0x508 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_50a : fetchRel p256ScalarMulCode 0x50A = some (.alu .sltu a1 (22 : Fin 32) a1, 4) := by decide
theorem psm_at_50e : fetchRel p256ScalarMulCode 0x50E = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_510 : fetchRel p256ScalarMulCode 0x510 = some (.alu .sub a3 (21 : Fin 32) (27 : Fin 32), 4) := by decide
theorem psm_at_514 : fetchRel p256ScalarMulCode 0x514 = some (.alu .sltu a4 a3 (21 : Fin 32), 4) := by decide
theorem psm_at_518 : fetchRel p256ScalarMulCode 0x518 = some (.alu .add (21 : Fin 32) a3 a1, 4) := by decide
theorem psm_at_51c : fetchRel p256ScalarMulCode 0x51C = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem psm_at_51e : fetchRel p256ScalarMulCode 0x51E = some (.alu .sltu a3 (21 : Fin 32) a3, 4) := by decide
theorem psm_at_522 : fetchRel p256ScalarMulCode 0x522 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_524 : fetchRel p256ScalarMulCode 0x524 = some (.alu .mul a4 (18 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_528 : fetchRel p256ScalarMulCode 0x528 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a3, 2) := by decide
theorem psm_at_52a : fetchRel p256ScalarMulCode 0x52A = some (.alu .add (27 : Fin 32) (27 : Fin 32) (28 : Fin 32), 2) := by decide
theorem psm_at_52c : fetchRel p256ScalarMulCode 0x52C = some (.alu .mulhu (8 : Fin 32) (18 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_530 : fetchRel p256ScalarMulCode 0x530 = some (.alu .mul a1 (18 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_534 : fetchRel p256ScalarMulCode 0x534 = some (.alu .sltu (20 : Fin 32) (7 : Fin 32) a3, 4) := by decide
theorem psm_at_538 : fetchRel p256ScalarMulCode 0x538 = some (.alu .sltu (28 : Fin 32) (27 : Fin 32) (28 : Fin 32), 4) := by decide
theorem psm_at_53c : fetchRel p256ScalarMulCode 0x53C = some (.alu .add (20 : Fin 32) (20 : Fin 32) (27 : Fin 32), 2) := by decide
theorem psm_at_53e : fetchRel p256ScalarMulCode 0x53E = some (.alu .mulhu a3 (18 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_542 : fetchRel p256ScalarMulCode 0x542 = some (.aluImm .and a0 (19 : Fin 32) 0xFFFFFFFE, 4) := by decide
theorem psm_at_546 : fetchRel p256ScalarMulCode 0x546 = some (.alu .mul (9 : Fin 32) (18 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_54a : fetchRel p256ScalarMulCode 0x54A = some (.alu .sltu (19 : Fin 32) (20 : Fin 32) (27 : Fin 32), 4) := by decide
theorem psm_at_54e : fetchRel p256ScalarMulCode 0x54E = some (.alu .add a4 a4 a0, 2) := by decide
theorem psm_at_550 : fetchRel p256ScalarMulCode 0x550 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem psm_at_554 : fetchRel p256ScalarMulCode 0x554 = some (.alu .mulhu a4 (18 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_558 : fetchRel p256ScalarMulCode 0x558 = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem psm_at_55a : fetchRel p256ScalarMulCode 0x55A = some (.alu .add a1 a1 a2, 2) := by decide
theorem psm_at_55c : fetchRel p256ScalarMulCode 0x55C = some (.alu .sltu a2 a1 a2, 4) := by decide
theorem psm_at_560 : fetchRel p256ScalarMulCode 0x560 = some (.alu .mul (8 : Fin 32) (18 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_564 : fetchRel p256ScalarMulCode 0x564 = some (.alu .add a2 a2 a3, 2) := by decide
theorem psm_at_566 : fetchRel p256ScalarMulCode 0x566 = some (.alu .add (24 : Fin 32) a1 a0, 4) := by decide
theorem psm_at_56a : fetchRel p256ScalarMulCode 0x56A = some (.alu .add (9 : Fin 32) (9 : Fin 32) a5, 2) := by decide
theorem psm_at_56c : fetchRel p256ScalarMulCode 0x56C = some (.alu .mulhu a3 (18 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_570 : fetchRel p256ScalarMulCode 0x570 = some (.alu .sltu a1 (24 : Fin 32) a1, 4) := by decide
theorem psm_at_574 : fetchRel p256ScalarMulCode 0x574 = some (.alu .sltu a5 (9 : Fin 32) a5, 4) := by decide
theorem psm_at_578 : fetchRel p256ScalarMulCode 0x578 = some (.alu .add a1 a1 a2, 2) := by decide
theorem psm_at_57a : fetchRel p256ScalarMulCode 0x57A = some (.alu .add a4 a4 a5, 2) := by decide
theorem psm_at_57c : fetchRel p256ScalarMulCode 0x57C = some (.alu .add a2 (9 : Fin 32) a1, 4) := by decide
theorem psm_at_580 : fetchRel p256ScalarMulCode 0x580 = some (.alu .mulhu a0 (18 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_584 : fetchRel p256ScalarMulCode 0x584 = some (.alu .sltu a1 a2 (9 : Fin 32), 4) := by decide
theorem psm_at_588 : fetchRel p256ScalarMulCode 0x588 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (23 : Fin 32), 2) := by decide
theorem psm_at_58a : fetchRel p256ScalarMulCode 0x58A = some (.alu .add a1 a1 a4, 2) := by decide
theorem psm_at_58c : fetchRel p256ScalarMulCode 0x58C = some (.alu .sltu a4 (8 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_590 : fetchRel p256ScalarMulCode 0x590 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_592 : fetchRel p256ScalarMulCode 0x592 = some (.alu .add (25 : Fin 32) (8 : Fin 32) a1, 4) := by decide
theorem psm_at_596 : fetchRel p256ScalarMulCode 0x596 = some (.alu .sub a1 (22 : Fin 32) (18 : Fin 32), 4) := by decide
theorem psm_at_59a : fetchRel p256ScalarMulCode 0x59A = some (.alu .mulhu (9 : Fin 32) (18 : Fin 32) a6, 4) := by decide
theorem psm_at_59e : fetchRel p256ScalarMulCode 0x59E = some (.alu .sltu a4 (25 : Fin 32) (8 : Fin 32), 4) := by decide
theorem psm_at_5a2 : fetchRel p256ScalarMulCode 0x5A2 = some (.alu .sltu (8 : Fin 32) a1 (22 : Fin 32), 4) := by decide
theorem psm_at_5a6 : fetchRel p256ScalarMulCode 0x5A6 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_5a8 : fetchRel p256ScalarMulCode 0x5A8 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a0, 2) := by decide
theorem psm_at_5aa : fetchRel p256ScalarMulCode 0x5AA = some (.alu .add (23 : Fin 32) a1 a3, 4) := by decide
theorem psm_at_5ae : fetchRel p256ScalarMulCode 0x5AE = some (.alu .add a3 (18 : Fin 32) (18 : Fin 32), 4) := by decide
theorem psm_at_5b2 : fetchRel p256ScalarMulCode 0x5B2 = some (.alu .sltu a1 (23 : Fin 32) a1, 4) := by decide
theorem psm_at_5b6 : fetchRel p256ScalarMulCode 0x5B6 = some (.alu .sub a3 (21 : Fin 32) a3, 4) := by decide
theorem psm_at_5ba : fetchRel p256ScalarMulCode 0x5BA = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem psm_at_5bc : fetchRel p256ScalarMulCode 0x5BC = some (.alu .sltu (8 : Fin 32) a3 (21 : Fin 32), 4) := by decide
theorem psm_at_5c0 : fetchRel p256ScalarMulCode 0x5C0 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_5c2 : fetchRel p256ScalarMulCode 0x5C2 = some (.alu .add (21 : Fin 32) a3 a1, 4) := by decide
theorem psm_at_5c6 : fetchRel p256ScalarMulCode 0x5C6 = some (.alu .sltu a3 (21 : Fin 32) a3, 4) := by decide
theorem psm_at_5ca : fetchRel p256ScalarMulCode 0x5CA = some (.alu .sub (9 : Fin 32) (7 : Fin 32) (18 : Fin 32), 4) := by decide
theorem psm_at_5ce : fetchRel p256ScalarMulCode 0x5CE = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem psm_at_5d0 : fetchRel p256ScalarMulCode 0x5D0 = some (.alu .sltu (8 : Fin 32) (9 : Fin 32) (7 : Fin 32), 4) := by decide
theorem psm_at_5d4 : fetchRel p256ScalarMulCode 0x5D4 = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem psm_at_5d6 : fetchRel p256ScalarMulCode 0x5D6 = some (.alu .add (22 : Fin 32) (9 : Fin 32) a3, 4) := by decide
theorem psm_at_5da : fetchRel p256ScalarMulCode 0x5DA = some (.alu .sltu (9 : Fin 32) (22 : Fin 32) (9 : Fin 32), 4) := by decide
theorem psm_at_5de : fetchRel p256ScalarMulCode 0x5DE = some (.alu .mul (8 : Fin 32) (31 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_5e2 : fetchRel p256ScalarMulCode 0x5E2 = some (.alu .add (28 : Fin 32) (28 : Fin 32) (19 : Fin 32), 2) := by decide
theorem psm_at_5e4 : fetchRel p256ScalarMulCode 0x5E4 = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem psm_at_5e6 : fetchRel p256ScalarMulCode 0x5E6 = some (.alu .add (9 : Fin 32) a0 (20 : Fin 32), 4) := by decide
theorem psm_at_5ea : fetchRel p256ScalarMulCode 0x5EA = some (.alu .mul a1 (31 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_5ee : fetchRel p256ScalarMulCode 0x5EE = some (.alu .add (18 : Fin 32) (18 : Fin 32) (28 : Fin 32), 2) := by decide
theorem psm_at_5f0 : fetchRel p256ScalarMulCode 0x5F0 = some (.alu .mulhu a3 (31 : Fin 32) (5 : Fin 32), 4) := by decide
theorem psm_at_5f4 : fetchRel p256ScalarMulCode 0x5F4 = some (.alu .sltu (7 : Fin 32) (9 : Fin 32) a0, 4) := by decide
theorem psm_at_5f8 : fetchRel p256ScalarMulCode 0x5F8 = some (.alu .sltu (5 : Fin 32) (18 : Fin 32) (28 : Fin 32), 4) := by decide
theorem psm_at_5fc : fetchRel p256ScalarMulCode 0x5FC = some (.aluImm .and a0 (24 : Fin 32) 0xFFFFFFFE, 4) := by decide
theorem psm_at_600 : fetchRel p256ScalarMulCode 0x600 = some (.alu .mulhu a4 (31 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_604 : fetchRel p256ScalarMulCode 0x604 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a0, 2) := by decide
theorem psm_at_606 : fetchRel p256ScalarMulCode 0x606 = some (.alu .mul a5 (31 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_60a : fetchRel p256ScalarMulCode 0x60A = some (.alu .add (7 : Fin 32) (7 : Fin 32) (18 : Fin 32), 2) := by decide
theorem psm_at_60c : fetchRel p256ScalarMulCode 0x60C = some (.alu .sltu a0 (8 : Fin 32) a0, 4) := by decide
theorem psm_at_610 : fetchRel p256ScalarMulCode 0x610 = some (.alu .add a1 a1 a2, 2) := by decide
theorem psm_at_612 : fetchRel p256ScalarMulCode 0x612 = some (.alu .mulhu (8 : Fin 32) (31 : Fin 32) (6 : Fin 32), 4) := by decide
theorem psm_at_616 : fetchRel p256ScalarMulCode 0x616 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_618 : fetchRel p256ScalarMulCode 0x618 = some (.alu .sltu a3 a1 a2, 4) := by decide
theorem psm_at_61c : fetchRel p256ScalarMulCode 0x61C = some (.alu .add (19 : Fin 32) a1 a0, 4) := by decide
theorem psm_at_620 : fetchRel p256ScalarMulCode 0x620 = some (.alu .mul a2 (31 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_624 : fetchRel p256ScalarMulCode 0x624 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_626 : fetchRel p256ScalarMulCode 0x626 = some (.alu .sltu a0 (19 : Fin 32) a1, 4) := by decide
theorem psm_at_62a : fetchRel p256ScalarMulCode 0x62A = some (.alu .add a5 a5 (25 : Fin 32), 2) := by decide
theorem psm_at_62c : fetchRel p256ScalarMulCode 0x62C = some (.alu .mulhu a1 (31 : Fin 32) (30 : Fin 32), 4) := by decide
theorem psm_at_630 : fetchRel p256ScalarMulCode 0x630 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_632 : fetchRel p256ScalarMulCode 0x632 = some (.alu .sltu a3 a5 (25 : Fin 32), 4) := by decide
theorem psm_at_636 : fetchRel p256ScalarMulCode 0x636 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem psm_at_638 : fetchRel p256ScalarMulCode 0x638 = some (.alu .add a0 a0 a5, 2) := by decide
theorem psm_at_63a : fetchRel p256ScalarMulCode 0x63A = some (.alu .sltu a4 a0 a5, 4) := by decide
theorem psm_at_63e : fetchRel p256ScalarMulCode 0x63E = some (.alu .mulhu a5 (31 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_642 : fetchRel p256ScalarMulCode 0x642 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_644 : fetchRel p256ScalarMulCode 0x644 = some (.alu .add a2 a2 (23 : Fin 32), 2) := by decide
theorem psm_at_646 : fetchRel p256ScalarMulCode 0x646 = some (.alu .sltu a4 a2 (23 : Fin 32), 4) := by decide
theorem psm_at_64a : fetchRel p256ScalarMulCode 0x64A = some (.alu .add (25 : Fin 32) a2 a3, 4) := by decide
theorem psm_at_64e : fetchRel p256ScalarMulCode 0x64E = some (.alu .add a1 a1 a4, 2) := by decide
theorem psm_at_650 : fetchRel p256ScalarMulCode 0x650 = some (.alu .sltu a2 (25 : Fin 32) a2, 4) := by decide
theorem psm_at_654 : fetchRel p256ScalarMulCode 0x654 = some (.alu .sub a3 (21 : Fin 32) (31 : Fin 32), 4) := by decide
theorem psm_at_658 : fetchRel p256ScalarMulCode 0x658 = some (.alu .mulhu a4 (31 : Fin 32) a6, 4) := by decide
theorem psm_at_65c : fetchRel p256ScalarMulCode 0x65C = some (.alu .add a1 a1 a2, 2) := by decide
theorem psm_at_65e : fetchRel p256ScalarMulCode 0x65E = some (.alu .sltu a2 a3 (21 : Fin 32), 4) := by decide
theorem psm_at_662 : fetchRel p256ScalarMulCode 0x662 = some (.alu .add a2 a2 a5, 2) := by decide
theorem psm_at_664 : fetchRel p256ScalarMulCode 0x664 = some (.alu .add (20 : Fin 32) a3 a1, 4) := by decide
theorem psm_at_668 : fetchRel p256ScalarMulCode 0x668 = some (.alu .sltu a3 (20 : Fin 32) a3, 4) := by decide
theorem psm_at_66c : fetchRel p256ScalarMulCode 0x66C = some (.alu .add a1 (31 : Fin 32) (31 : Fin 32), 4) := by decide
theorem psm_at_670 : fetchRel p256ScalarMulCode 0x670 = some (.alu .add a2 a2 a3, 2) := by decide
theorem psm_at_672 : fetchRel p256ScalarMulCode 0x672 = some (.alu .sub a1 (22 : Fin 32) a1, 4) := by decide
theorem psm_at_676 : fetchRel p256ScalarMulCode 0x676 = some (.alu .sltu a3 a1 (22 : Fin 32), 4) := by decide
theorem psm_at_67a : fetchRel p256ScalarMulCode 0x67A = some (.alu .add (29 : Fin 32) a1 a2, 4) := by decide
theorem psm_at_67e : fetchRel p256ScalarMulCode 0x67E = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_680 : fetchRel p256ScalarMulCode 0x680 = some (.alu .sltu a1 (29 : Fin 32) a1, 4) := by decide
theorem psm_at_684 : fetchRel p256ScalarMulCode 0x684 = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_686 : fetchRel p256ScalarMulCode 0x686 = some (.alu .sub a2 (9 : Fin 32) (31 : Fin 32), 4) := by decide
theorem psm_at_68a : fetchRel p256ScalarMulCode 0x68A = some (.alu .sltu a3 a2 (9 : Fin 32), 4) := by decide
theorem psm_at_68e : fetchRel p256ScalarMulCode 0x68E = some (.alu .add (28 : Fin 32) a2 a1, 4) := by decide
theorem psm_at_692 : fetchRel p256ScalarMulCode 0x692 = some (.alu .add a3 a3 a5, 2) := by decide
theorem psm_at_694 : fetchRel p256ScalarMulCode 0x694 = some (.alu .sltu a1 (28 : Fin 32) a2, 4) := by decide
theorem psm_at_698 : fetchRel p256ScalarMulCode 0x698 = some (.alu .sltu a2 (7 : Fin 32) (18 : Fin 32), 4) := by decide
theorem psm_at_69c : fetchRel p256ScalarMulCode 0x69C = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_69e : fetchRel p256ScalarMulCode 0x69E = some (.alu .add a2 a2 (5 : Fin 32), 2) := by decide
theorem psm_at_6a0 : fetchRel p256ScalarMulCode 0x6A0 = some (.alu .add (7 : Fin 32) (7 : Fin 32) a1, 2) := by decide
theorem psm_at_6a2 : fetchRel p256ScalarMulCode 0x6A2 = some (.lui a3 0xFC632000, 4) := by decide
theorem psm_at_6a6 : fetchRel p256ScalarMulCode 0x6A6 = some (.lui a4 0xF3B9D000, 4) := by decide
theorem psm_at_6aa : fetchRel p256ScalarMulCode 0x6AA = some (.aluImm .add (24 : Fin 32) a3 0x551, 4) := by decide
theorem psm_at_6ae : fetchRel p256ScalarMulCode 0x6AE = some (.aluImm .add (23 : Fin 32) a4 0xFFFFFAC2, 4) := by decide
theorem psm_at_6b2 : fetchRel p256ScalarMulCode 0x6B2 = some (.alu .mulhu a3 (19 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_6b6 : fetchRel p256ScalarMulCode 0x6B6 = some (.alu .mul a4 (19 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_6ba : fetchRel p256ScalarMulCode 0x6BA = some (.alu .sltu (6 : Fin 32) (7 : Fin 32) a1, 4) := by decide
theorem psm_at_6be : fetchRel p256ScalarMulCode 0x6BE = some (.lui a1 0xA717A000, 4) := by decide
theorem psm_at_6c2 : fetchRel p256ScalarMulCode 0x6C2 = some (.alu .mulhu a5 (19 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_6c6 : fetchRel p256ScalarMulCode 0x6C6 = some (.aluImm .add (21 : Fin 32) a1 0xFFFFFE84, 4) := by decide
theorem psm_at_6ca : fetchRel p256ScalarMulCode 0x6CA = some (.alu .add (31 : Fin 32) (31 : Fin 32) a2, 2) := by decide
theorem psm_at_6cc : fetchRel p256ScalarMulCode 0x6CC = some (.alu .mul a1 (19 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_6d0 : fetchRel p256ScalarMulCode 0x6D0 = some (.alu .sltu a6 (31 : Fin 32) a2, 4) := by decide
theorem psm_at_6d4 : fetchRel p256ScalarMulCode 0x6D4 = some (.lui a2 0xBCE70000, 4) := by decide
theorem psm_at_6d8 : fetchRel p256ScalarMulCode 0x6D8 = some (.alu .mulhu (9 : Fin 32) (19 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_6dc : fetchRel p256ScalarMulCode 0x6DC = some (.aluImm .add (22 : Fin 32) a2 0xFFFFFAAD, 4) := by decide
theorem psm_at_6e0 : fetchRel p256ScalarMulCode 0x6E0 = some (.alu .add a4 a4 a3, 2) := by decide
theorem psm_at_6e2 : fetchRel p256ScalarMulCode 0x6E2 = some (.alu .mul a2 (19 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_6e6 : fetchRel p256ScalarMulCode 0x6E6 = some (.alu .add (6 : Fin 32) (6 : Fin 32) (31 : Fin 32), 2) := by decide
theorem psm_at_6e8 : fetchRel p256ScalarMulCode 0x6E8 = some (.alu .sltu a3 a4 a3, 4) := by decide
theorem psm_at_6ec : fetchRel p256ScalarMulCode 0x6EC = some (.alu .add a3 a3 a5, 2) := by decide
theorem psm_at_6ee : fetchRel p256ScalarMulCode 0x6EE = some (.alu .mulhu (30 : Fin 32) (19 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_6f2 : fetchRel p256ScalarMulCode 0x6F2 = some (.alu .sltu (5 : Fin 32) (6 : Fin 32) (31 : Fin 32), 4) := by decide
theorem psm_at_6f6 : fetchRel p256ScalarMulCode 0x6F6 = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_6f8 : fetchRel p256ScalarMulCode 0x6F8 = some (.alu .sltu a3 a1 a3, 4) := by decide
theorem psm_at_6fc : fetchRel p256ScalarMulCode 0x6FC = some (.alu .mul a5 a0 (24 : Fin 32), 4) := by decide
theorem psm_at_700 : fetchRel p256ScalarMulCode 0x700 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem psm_at_702 : fetchRel p256ScalarMulCode 0x702 = some (.alu .mulhu (31 : Fin 32) (19 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_706 : fetchRel p256ScalarMulCode 0x706 = some (.alu .add a2 a2 a3, 2) := by decide
theorem psm_at_708 : fetchRel p256ScalarMulCode 0x708 = some (.alu .mul (9 : Fin 32) a0 (23 : Fin 32), 4) := by decide
theorem psm_at_70c : fetchRel p256ScalarMulCode 0x70C = some (.alu .sltu a3 a2 a3, 4) := by decide
theorem psm_at_710 : fetchRel p256ScalarMulCode 0x710 = some (.alu .mulhu (18 : Fin 32) a0 (24 : Fin 32), 4) := by decide
theorem psm_at_714 : fetchRel p256ScalarMulCode 0x714 = some (.alu .add a3 a3 (30 : Fin 32), 2) := by decide
theorem psm_at_716 : fetchRel p256ScalarMulCode 0x716 = some (.alu .mulhu (30 : Fin 32) a0 (23 : Fin 32), 4) := by decide
theorem psm_at_71a : fetchRel p256ScalarMulCode 0x71A = some (.alu .add a6 a6 (5 : Fin 32), 2) := by decide
theorem psm_at_71c : fetchRel p256ScalarMulCode 0x71C = some (.alu .sub (8 : Fin 32) a3 (19 : Fin 32), 4) := by decide
theorem psm_at_720 : fetchRel p256ScalarMulCode 0x720 = some (.alu .sltu a3 (8 : Fin 32) a3, 4) := by decide
theorem psm_at_724 : fetchRel p256ScalarMulCode 0x724 = some (.alu .add a5 a5 a4, 2) := by decide
theorem psm_at_726 : fetchRel p256ScalarMulCode 0x726 = some (.store .sw sp a5 0x1C, 2) := by decide
theorem psm_at_728 : fetchRel p256ScalarMulCode 0x728 = some (.alu .add a3 a3 (31 : Fin 32), 2) := by decide
theorem psm_at_72a : fetchRel p256ScalarMulCode 0x72A = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem psm_at_72e : fetchRel p256ScalarMulCode 0x72E = some (.alu .add (9 : Fin 32) (9 : Fin 32) a1, 2) := by decide
theorem psm_at_730 : fetchRel p256ScalarMulCode 0x730 = some (.alu .mul (26 : Fin 32) a0 (21 : Fin 32), 4) := by decide
theorem psm_at_734 : fetchRel p256ScalarMulCode 0x734 = some (.alu .add a4 a4 (18 : Fin 32), 2) := by decide
theorem psm_at_736 : fetchRel p256ScalarMulCode 0x736 = some (.alu .sltu a1 (9 : Fin 32) a1, 4) := by decide
theorem psm_at_73a : fetchRel p256ScalarMulCode 0x73A = some (.alu .add (30 : Fin 32) (30 : Fin 32) a1, 2) := by decide
theorem psm_at_73c : fetchRel p256ScalarMulCode 0x73C = some (.alu .mulhu a1 a0 (21 : Fin 32), 4) := by decide
theorem psm_at_740 : fetchRel p256ScalarMulCode 0x740 = some (.alu .add (5 : Fin 32) (9 : Fin 32) a4, 4) := by decide
theorem psm_at_744 : fetchRel p256ScalarMulCode 0x744 = some (.alu .mul a4 a0 (22 : Fin 32), 4) := by decide
theorem psm_at_748 : fetchRel p256ScalarMulCode 0x748 = some (.alu .sub a5 a3 (19 : Fin 32), 4) := by decide
theorem psm_at_74c : fetchRel p256ScalarMulCode 0x74C = some (.alu .sltu (9 : Fin 32) (5 : Fin 32) (9 : Fin 32), 4) := by decide
theorem psm_at_750 : fetchRel p256ScalarMulCode 0x750 = some (.alu .add (30 : Fin 32) (30 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_752 : fetchRel p256ScalarMulCode 0x752 = some (.alu .mulhu (9 : Fin 32) a0 (22 : Fin 32), 4) := by decide
theorem psm_at_756 : fetchRel p256ScalarMulCode 0x756 = some (.alu .sltu a3 a5 a3, 4) := by decide
theorem psm_at_75a : fetchRel p256ScalarMulCode 0x75A = some (.alu .add (26 : Fin 32) (26 : Fin 32) a2, 2) := by decide
theorem psm_at_75c : fetchRel p256ScalarMulCode 0x75C = some (.alu .add (18 : Fin 32) (31 : Fin 32) a3, 4) := by decide
theorem psm_at_760 : fetchRel p256ScalarMulCode 0x760 = some (.alu .sltu a2 (26 : Fin 32) a2, 4) := by decide
theorem psm_at_764 : fetchRel p256ScalarMulCode 0x764 = some (.alu .add a1 a1 a2, 2) := by decide
theorem psm_at_766 : fetchRel p256ScalarMulCode 0x766 = some (.alu .mulhu a2 a0 (17 : Fin 32), 4) := by decide
theorem psm_at_76a : fetchRel p256ScalarMulCode 0x76A = some (.alu .add (30 : Fin 32) (30 : Fin 32) (26 : Fin 32), 2) := by decide
theorem psm_at_76c : fetchRel p256ScalarMulCode 0x76C = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem psm_at_76e : fetchRel p256ScalarMulCode 0x76E = some (.alu .sltu a3 (30 : Fin 32) (26 : Fin 32), 4) := by decide
theorem psm_at_772 : fetchRel p256ScalarMulCode 0x772 = some (.alu .sltu (8 : Fin 32) a4 (8 : Fin 32), 4) := by decide
theorem psm_at_776 : fetchRel p256ScalarMulCode 0x776 = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_778 : fetchRel p256ScalarMulCode 0x778 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_77a : fetchRel p256ScalarMulCode 0x77A = some (.alu .add ra a4 a1, 4) := by decide
theorem psm_at_77e : fetchRel p256ScalarMulCode 0x77E = some (.alu .sub (9 : Fin 32) a5 a0, 4) := by decide
theorem psm_at_782 : fetchRel p256ScalarMulCode 0x782 = some (.alu .sltu a1 ra a4, 4) := by decide
theorem psm_at_786 : fetchRel p256ScalarMulCode 0x786 = some (.alu .sltu a4 (9 : Fin 32) a5, 4) := by decide
theorem psm_at_78a : fetchRel p256ScalarMulCode 0x78A = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem psm_at_78c : fetchRel p256ScalarMulCode 0x78C = some (.alu .add a4 a4 a2, 2) := by decide
theorem psm_at_78e : fetchRel p256ScalarMulCode 0x78E = some (.alu .add (26 : Fin 32) (9 : Fin 32) a1, 4) := by decide
theorem psm_at_792 : fetchRel p256ScalarMulCode 0x792 = some (.alu .mul a5 (25 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_796 : fetchRel p256ScalarMulCode 0x796 = some (.alu .sltu (8 : Fin 32) (26 : Fin 32) (9 : Fin 32), 4) := by decide
theorem psm_at_79a : fetchRel p256ScalarMulCode 0x79A = some (.alu .sub (9 : Fin 32) (18 : Fin 32) a0, 4) := by decide
theorem psm_at_79e : fetchRel p256ScalarMulCode 0x79E = some (.alu .mulhu (27 : Fin 32) (25 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_7a2 : fetchRel p256ScalarMulCode 0x7A2 = some (.alu .mul a1 (25 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_7a6 : fetchRel p256ScalarMulCode 0x7A6 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem psm_at_7a8 : fetchRel p256ScalarMulCode 0x7A8 = some (.alu .sltu (8 : Fin 32) (9 : Fin 32) (18 : Fin 32), 4) := by decide
theorem psm_at_7ac : fetchRel p256ScalarMulCode 0x7AC = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem psm_at_7ae : fetchRel p256ScalarMulCode 0x7AE = some (.alu .mulhu a3 (25 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_7b2 : fetchRel p256ScalarMulCode 0x7B2 = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem psm_at_7b4 : fetchRel p256ScalarMulCode 0x7B4 = some (.alu .sltu (8 : Fin 32) a4 (9 : Fin 32), 4) := by decide
theorem psm_at_7b8 : fetchRel p256ScalarMulCode 0x7B8 = some (.alu .add (18 : Fin 32) a2 (8 : Fin 32), 4) := by decide
theorem psm_at_7bc : fetchRel p256ScalarMulCode 0x7BC = some (.alu .add a5 a5 (5 : Fin 32), 2) := by decide
theorem psm_at_7be : fetchRel p256ScalarMulCode 0x7BE = some (.store .sw sp a5 0x18, 2) := by decide
theorem psm_at_7c0 : fetchRel p256ScalarMulCode 0x7C0 = some (.alu .sltu a5 a5 (5 : Fin 32), 4) := by decide
theorem psm_at_7c4 : fetchRel p256ScalarMulCode 0x7C4 = some (.alu .mul (8 : Fin 32) (25 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_7c8 : fetchRel p256ScalarMulCode 0x7C8 = some (.alu .add a5 a5 (27 : Fin 32), 2) := by decide
theorem psm_at_7ca : fetchRel p256ScalarMulCode 0x7CA = some (.alu .add a1 a1 (30 : Fin 32), 2) := by decide
theorem psm_at_7cc : fetchRel p256ScalarMulCode 0x7CC = some (.alu .sltu (9 : Fin 32) a1 (30 : Fin 32), 4) := by decide
theorem psm_at_7d0 : fetchRel p256ScalarMulCode 0x7D0 = some (.alu .mulhu a2 (25 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_7d4 : fetchRel p256ScalarMulCode 0x7D4 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem psm_at_7d6 : fetchRel p256ScalarMulCode 0x7D6 = some (.alu .add (27 : Fin 32) a1 a5, 4) := by decide
theorem psm_at_7da : fetchRel p256ScalarMulCode 0x7DA = some (.alu .sltu a1 (27 : Fin 32) a1, 4) := by decide
theorem psm_at_7de : fetchRel p256ScalarMulCode 0x7DE = some (.alu .mul a5 (25 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_7e2 : fetchRel p256ScalarMulCode 0x7E2 = some (.alu .sub (5 : Fin 32) (31 : Fin 32) a0, 4) := by decide
theorem psm_at_7e6 : fetchRel p256ScalarMulCode 0x7E6 = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_7e8 : fetchRel p256ScalarMulCode 0x7E8 = some (.alu .add (8 : Fin 32) (8 : Fin 32) ra, 2) := by decide
theorem psm_at_7ea : fetchRel p256ScalarMulCode 0x7EA = some (.alu .mulhu a0 (25 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_7ee : fetchRel p256ScalarMulCode 0x7EE = some (.alu .sltu a3 (8 : Fin 32) ra, 4) := by decide
theorem psm_at_7f2 : fetchRel p256ScalarMulCode 0x7F2 = some (.alu .add (31 : Fin 32) (8 : Fin 32) a1, 4) := by decide
theorem psm_at_7f6 : fetchRel p256ScalarMulCode 0x7F6 = some (.alu .add a2 a2 a3, 2) := by decide
theorem psm_at_7f8 : fetchRel p256ScalarMulCode 0x7F8 = some (.alu .sltu a1 (31 : Fin 32) (8 : Fin 32), 4) := by decide
theorem psm_at_7fc : fetchRel p256ScalarMulCode 0x7FC = some (.alu .sub (9 : Fin 32) (18 : Fin 32) (19 : Fin 32), 4) := by decide
theorem psm_at_800 : fetchRel p256ScalarMulCode 0x800 = some (.alu .add a1 a1 a2, 2) := by decide
theorem psm_at_802 : fetchRel p256ScalarMulCode 0x802 = some (.alu .add a5 a5 (26 : Fin 32), 2) := by decide
theorem psm_at_804 : fetchRel p256ScalarMulCode 0x804 = some (.alu .mulhu a2 (25 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_808 : fetchRel p256ScalarMulCode 0x808 = some (.alu .sltu (30 : Fin 32) (9 : Fin 32) (18 : Fin 32), 4) := by decide
theorem psm_at_80c : fetchRel p256ScalarMulCode 0x80C = some (.alu .sltu (8 : Fin 32) a5 (26 : Fin 32), 4) := by decide
theorem psm_at_810 : fetchRel p256ScalarMulCode 0x810 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a0, 2) := by decide
theorem psm_at_812 : fetchRel p256ScalarMulCode 0x812 = some (.alu .add a1 a1 a5, 2) := by decide
theorem psm_at_814 : fetchRel p256ScalarMulCode 0x814 = some (.alu .sltu a5 a1 a5, 4) := by decide
theorem psm_at_818 : fetchRel p256ScalarMulCode 0x818 = some (.alu .sub a0 a4 (25 : Fin 32), 4) := by decide
theorem psm_at_81c : fetchRel p256ScalarMulCode 0x81C = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_81e : fetchRel p256ScalarMulCode 0x81E = some (.alu .sltu (8 : Fin 32) a0 a4, 4) := by decide
theorem psm_at_822 : fetchRel p256ScalarMulCode 0x822 = some (.alu .add a4 a0 a5, 4) := by decide
theorem psm_at_826 : fetchRel p256ScalarMulCode 0x826 = some (.alu .mul a5 (20 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_82a : fetchRel p256ScalarMulCode 0x82A = some (.alu .add (8 : Fin 32) (8 : Fin 32) a2, 2) := by decide
theorem psm_at_82c : fetchRel p256ScalarMulCode 0x82C = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem psm_at_830 : fetchRel p256ScalarMulCode 0x830 = some (.alu .sub a3 (9 : Fin 32) (25 : Fin 32), 4) := by decide
theorem psm_at_834 : fetchRel p256ScalarMulCode 0x834 = some (.alu .mulhu (18 : Fin 32) (20 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_838 : fetchRel p256ScalarMulCode 0x838 = some (.alu .sltu (9 : Fin 32) a3 (9 : Fin 32), 4) := by decide
theorem psm_at_83c : fetchRel p256ScalarMulCode 0x83C = some (.alu .mul (25 : Fin 32) (20 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_840 : fetchRel p256ScalarMulCode 0x840 = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem psm_at_842 : fetchRel p256ScalarMulCode 0x842 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem psm_at_844 : fetchRel p256ScalarMulCode 0x844 = some (.alu .add a0 a0 a3, 2) := by decide
theorem psm_at_846 : fetchRel p256ScalarMulCode 0x846 = some (.alu .mulhu (26 : Fin 32) (20 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_84a : fetchRel p256ScalarMulCode 0x84A = some (.alu .sltu (8 : Fin 32) a0 a3, 4) := by decide
theorem psm_at_84e : fetchRel p256ScalarMulCode 0x84E = some (.alu .add a5 a5 (27 : Fin 32), 2) := by decide
theorem psm_at_850 : fetchRel p256ScalarMulCode 0x850 = some (.store .sw sp a5 0x14, 2) := by decide
theorem psm_at_852 : fetchRel p256ScalarMulCode 0x852 = some (.alu .sltu a3 a5 (27 : Fin 32), 4) := by decide
theorem psm_at_856 : fetchRel p256ScalarMulCode 0x856 = some (.alu .mul (27 : Fin 32) (20 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_85a : fetchRel p256ScalarMulCode 0x85A = some (.alu .add ra a2 (8 : Fin 32), 4) := by decide
theorem psm_at_85e : fetchRel p256ScalarMulCode 0x85E = some (.alu .add a3 a3 (18 : Fin 32), 2) := by decide
theorem psm_at_860 : fetchRel p256ScalarMulCode 0x860 = some (.alu .add (25 : Fin 32) (25 : Fin 32) (31 : Fin 32), 2) := by decide
theorem psm_at_862 : fetchRel p256ScalarMulCode 0x862 = some (.alu .mulhu (18 : Fin 32) (20 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_866 : fetchRel p256ScalarMulCode 0x866 = some (.alu .sltu (8 : Fin 32) (25 : Fin 32) (31 : Fin 32), 4) := by decide
theorem psm_at_86a : fetchRel p256ScalarMulCode 0x86A = some (.alu .mul (9 : Fin 32) (20 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_86e : fetchRel p256ScalarMulCode 0x86E = some (.alu .add (8 : Fin 32) (8 : Fin 32) (26 : Fin 32), 2) := by decide
theorem psm_at_870 : fetchRel p256ScalarMulCode 0x870 = some (.alu .add a3 a3 (25 : Fin 32), 2) := by decide
theorem psm_at_872 : fetchRel p256ScalarMulCode 0x872 = some (.alu .sltu a5 a3 (25 : Fin 32), 4) := by decide
theorem psm_at_876 : fetchRel p256ScalarMulCode 0x876 = some (.alu .mulhu a2 (20 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_87a : fetchRel p256ScalarMulCode 0x87A = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_87c : fetchRel p256ScalarMulCode 0x87C = some (.alu .add (27 : Fin 32) (27 : Fin 32) a1, 2) := by decide
theorem psm_at_87e : fetchRel p256ScalarMulCode 0x87E = some (.alu .sltu a1 (27 : Fin 32) a1, 4) := by decide
theorem psm_at_882 : fetchRel p256ScalarMulCode 0x882 = some (.alu .add a5 a5 (27 : Fin 32), 2) := by decide
theorem psm_at_884 : fetchRel p256ScalarMulCode 0x884 = some (.alu .add a1 a1 (18 : Fin 32), 2) := by decide
theorem psm_at_886 : fetchRel p256ScalarMulCode 0x886 = some (.alu .sltu (8 : Fin 32) a5 (27 : Fin 32), 4) := by decide
theorem psm_at_88a : fetchRel p256ScalarMulCode 0x88A = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem psm_at_88c : fetchRel p256ScalarMulCode 0x88C = some (.alu .add (9 : Fin 32) (9 : Fin 32) a4, 2) := by decide
theorem psm_at_88e : fetchRel p256ScalarMulCode 0x88E = some (.alu .sltu a4 (9 : Fin 32) a4, 4) := by decide
theorem psm_at_892 : fetchRel p256ScalarMulCode 0x892 = some (.alu .mulhu (17 : Fin 32) (20 : Fin 32) (17 : Fin 32), 4) := by decide
theorem psm_at_896 : fetchRel p256ScalarMulCode 0x896 = some (.alu .add (31 : Fin 32) a2 a4, 4) := by decide
theorem psm_at_89a : fetchRel p256ScalarMulCode 0x89A = some (.alu .mul (18 : Fin 32) (29 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_89e : fetchRel p256ScalarMulCode 0x89E = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem psm_at_8a0 : fetchRel p256ScalarMulCode 0x8A0 = some (.alu .mul (25 : Fin 32) (29 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_8a4 : fetchRel p256ScalarMulCode 0x8A4 = some (.alu .sltu (9 : Fin 32) a1 (9 : Fin 32), 4) := by decide
theorem psm_at_8a8 : fetchRel p256ScalarMulCode 0x8A8 = some (.alu .mulhu (26 : Fin 32) (29 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_8ac : fetchRel p256ScalarMulCode 0x8AC = some (.alu .sub a4 a0 (20 : Fin 32), 4) := by decide
theorem psm_at_8b0 : fetchRel p256ScalarMulCode 0x8B0 = some (.alu .mulhu (8 : Fin 32) (29 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_8b4 : fetchRel p256ScalarMulCode 0x8B4 = some (.alu .sltu a0 a4 a0, 4) := by decide
theorem psm_at_8b8 : fetchRel p256ScalarMulCode 0x8B8 = some (.alu .mul a2 (29 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_8bc : fetchRel p256ScalarMulCode 0x8BC = some (.alu .add (31 : Fin 32) (31 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_8be : fetchRel p256ScalarMulCode 0x8BE = some (.alu .add (17 : Fin 32) (17 : Fin 32) a0, 2) := by decide
theorem psm_at_8c0 : fetchRel p256ScalarMulCode 0x8C0 = some (.alu .add (18 : Fin 32) (18 : Fin 32) a3, 2) := by decide
theorem psm_at_8c2 : fetchRel p256ScalarMulCode 0x8C2 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem psm_at_8c4 : fetchRel p256ScalarMulCode 0x8C4 = some (.alu .mulhu (9 : Fin 32) (29 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_8c8 : fetchRel p256ScalarMulCode 0x8C8 = some (.alu .sltu a3 (18 : Fin 32) a3, 4) := by decide
theorem psm_at_8cc : fetchRel p256ScalarMulCode 0x8CC = some (.alu .add (25 : Fin 32) (25 : Fin 32) a5, 2) := by decide
theorem psm_at_8ce : fetchRel p256ScalarMulCode 0x8CE = some (.alu .add a3 a3 (26 : Fin 32), 2) := by decide
theorem psm_at_8d0 : fetchRel p256ScalarMulCode 0x8D0 = some (.alu .sltu a5 (25 : Fin 32) a5, 4) := by decide
theorem psm_at_8d4 : fetchRel p256ScalarMulCode 0x8D4 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_8d6 : fetchRel p256ScalarMulCode 0x8D6 = some (.alu .add a3 a3 (25 : Fin 32), 2) := by decide
theorem psm_at_8d8 : fetchRel p256ScalarMulCode 0x8D8 = some (.alu .sltu (8 : Fin 32) a3 (25 : Fin 32), 4) := by decide
theorem psm_at_8dc : fetchRel p256ScalarMulCode 0x8DC = some (.alu .add a2 a2 a1, 2) := by decide
theorem psm_at_8de : fetchRel p256ScalarMulCode 0x8DE = some (.alu .sltu a1 a2 a1, 4) := by decide
theorem psm_at_8e2 : fetchRel p256ScalarMulCode 0x8E2 = some (.alu .mul a0 (29 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_8e6 : fetchRel p256ScalarMulCode 0x8E6 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_8e8 : fetchRel p256ScalarMulCode 0x8E8 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem psm_at_8ea : fetchRel p256ScalarMulCode 0x8EA = some (.alu .add (31 : Fin 32) (31 : Fin 32) a4, 2) := by decide
theorem psm_at_8ec : fetchRel p256ScalarMulCode 0x8EC = some (.alu .mulhu (8 : Fin 32) (29 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_8f0 : fetchRel p256ScalarMulCode 0x8F0 = some (.alu .sltu (9 : Fin 32) (31 : Fin 32) a4, 4) := by decide
theorem psm_at_8f4 : fetchRel p256ScalarMulCode 0x8F4 = some (.alu .add a5 a5 a2, 2) := by decide
theorem psm_at_8f6 : fetchRel p256ScalarMulCode 0x8F6 = some (.alu .sltu a2 a5 a2, 4) := by decide
theorem psm_at_8fa : fetchRel p256ScalarMulCode 0x8FA = some (.alu .mul (18 : Fin 32) (28 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_8fe : fetchRel p256ScalarMulCode 0x8FE = some (.alu .add (17 : Fin 32) (17 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_900 : fetchRel p256ScalarMulCode 0x900 = some (.alu .add a1 a1 a2, 2) := by decide
theorem psm_at_902 : fetchRel p256ScalarMulCode 0x902 = some (.alu .add a0 a0 (31 : Fin 32), 2) := by decide
theorem psm_at_904 : fetchRel p256ScalarMulCode 0x904 = some (.alu .mul (25 : Fin 32) (28 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_908 : fetchRel p256ScalarMulCode 0x908 = some (.alu .sltu (9 : Fin 32) a0 (31 : Fin 32), 4) := by decide
theorem psm_at_90c : fetchRel p256ScalarMulCode 0x90C = some (.alu .mulhu a4 (28 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_910 : fetchRel p256ScalarMulCode 0x910 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_912 : fetchRel p256ScalarMulCode 0x912 = some (.alu .mulhu (9 : Fin 32) (28 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_916 : fetchRel p256ScalarMulCode 0x916 = some (.alu .add a1 a1 a0, 2) := by decide
theorem psm_at_918 : fetchRel p256ScalarMulCode 0x918 = some (.alu .mul a2 (28 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_91c : fetchRel p256ScalarMulCode 0x91C = some (.alu .sltu a0 a1 a0, 4) := by decide
theorem psm_at_920 : fetchRel p256ScalarMulCode 0x920 = some (.alu .add (18 : Fin 32) (18 : Fin 32) a3, 2) := by decide
theorem psm_at_922 : fetchRel p256ScalarMulCode 0x922 = some (.store .sw sp (18 : Fin 32) 0xC, 2) := by decide
theorem psm_at_924 : fetchRel p256ScalarMulCode 0x924 = some (.alu .add (31 : Fin 32) (8 : Fin 32) a0, 4) := by decide
theorem psm_at_928 : fetchRel p256ScalarMulCode 0x928 = some (.alu .sltu a3 (18 : Fin 32) a3, 4) := by decide
theorem psm_at_92c : fetchRel p256ScalarMulCode 0x92C = some (.alu .add (25 : Fin 32) (25 : Fin 32) a5, 2) := by decide
theorem psm_at_92e : fetchRel p256ScalarMulCode 0x92E = some (.alu .mulhu (8 : Fin 32) (28 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_932 : fetchRel p256ScalarMulCode 0x932 = some (.alu .add a3 a3 a4, 2) := by decide
theorem psm_at_934 : fetchRel p256ScalarMulCode 0x934 = some (.alu .sltu a4 (25 : Fin 32) a5, 4) := by decide
theorem psm_at_938 : fetchRel p256ScalarMulCode 0x938 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem psm_at_93a : fetchRel p256ScalarMulCode 0x93A = some (.alu .add a3 a3 (25 : Fin 32), 2) := by decide
theorem psm_at_93c : fetchRel p256ScalarMulCode 0x93C = some (.alu .sltu a5 a3 (25 : Fin 32), 4) := by decide
theorem psm_at_940 : fetchRel p256ScalarMulCode 0x940 = some (.alu .add a2 a2 a1, 2) := by decide
theorem psm_at_942 : fetchRel p256ScalarMulCode 0x942 = some (.alu .add a4 a4 a5, 2) := by decide
theorem psm_at_944 : fetchRel p256ScalarMulCode 0x944 = some (.alu .sltu a1 a2 a1, 4) := by decide
theorem psm_at_948 : fetchRel p256ScalarMulCode 0x948 = some (.alu .add a4 a4 a2, 2) := by decide
theorem psm_at_94a : fetchRel p256ScalarMulCode 0x94A = some (.alu .mul (18 : Fin 32) (7 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_94e : fetchRel p256ScalarMulCode 0x94E = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem psm_at_950 : fetchRel p256ScalarMulCode 0x950 = some (.alu .sltu a2 a4 a2, 4) := by decide
theorem psm_at_954 : fetchRel p256ScalarMulCode 0x954 = some (.alu .mul (25 : Fin 32) (28 : Fin 32) (22 : Fin 32), 4) := by decide
theorem psm_at_958 : fetchRel p256ScalarMulCode 0x958 = some (.alu .mulhu (26 : Fin 32) (7 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_95c : fetchRel p256ScalarMulCode 0x95C = some (.alu .mul (8 : Fin 32) (7 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_960 : fetchRel p256ScalarMulCode 0x960 = some (.alu .mul a0 (7 : Fin 32) (21 : Fin 32), 4) := by decide
theorem psm_at_964 : fetchRel p256ScalarMulCode 0x964 = some (.alu .add (28 : Fin 32) a1 a2, 4) := by decide
theorem psm_at_968 : fetchRel p256ScalarMulCode 0x968 = some (.alu .mul a1 (6 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_96c : fetchRel p256ScalarMulCode 0x96C = some (.alu .mulhu a2 (7 : Fin 32) (23 : Fin 32), 4) := by decide
theorem psm_at_970 : fetchRel p256ScalarMulCode 0x970 = some (.alu .mul a5 a6 (24 : Fin 32), 4) := by decide
theorem psm_at_974 : fetchRel p256ScalarMulCode 0x974 = some (.alu .sub (9 : Fin 32) (5 : Fin 32) (20 : Fin 32), 4) := by decide
theorem psm_at_978 : fetchRel p256ScalarMulCode 0x978 = some (.alu .add (18 : Fin 32) (18 : Fin 32) a3, 2) := by decide
theorem psm_at_97a : fetchRel p256ScalarMulCode 0x97A = some (.alu .sub (9 : Fin 32) (9 : Fin 32) (29 : Fin 32), 4) := by decide
theorem psm_at_97e : fetchRel p256ScalarMulCode 0x97E = some (.alu .sltu a3 (18 : Fin 32) a3, 4) := by decide
theorem psm_at_982 : fetchRel p256ScalarMulCode 0x982 = some (.alu .add a3 a3 (26 : Fin 32), 2) := by decide
theorem psm_at_984 : fetchRel p256ScalarMulCode 0x984 = some (.alu .add (9 : Fin 32) (9 : Fin 32) (25 : Fin 32), 2) := by decide
theorem psm_at_986 : fetchRel p256ScalarMulCode 0x986 = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem psm_at_988 : fetchRel p256ScalarMulCode 0x988 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a4, 2) := by decide
theorem psm_at_98a : fetchRel p256ScalarMulCode 0x98A = some (.alu .sltu a4 (8 : Fin 32) a4, 4) := by decide
theorem psm_at_98e : fetchRel p256ScalarMulCode 0x98E = some (.alu .add a0 a0 a1, 2) := by decide
theorem psm_at_990 : fetchRel p256ScalarMulCode 0x990 = some (.alu .add a2 a2 a4, 2) := by decide
theorem psm_at_992 : fetchRel p256ScalarMulCode 0x992 = some (.alu .add a0 a0 a5, 2) := by decide
theorem psm_at_994 : fetchRel p256ScalarMulCode 0x994 = some (.load .lw (26 : Fin 32) sp 0x3C, 2) := by decide
theorem psm_at_996 : fetchRel p256ScalarMulCode 0x996 = some (.load .lw (27 : Fin 32) sp 0x40, 2) := by decide
theorem psm_at_998 : fetchRel p256ScalarMulCode 0x998 = some (.load .lw a1 sp 0x44, 2) := by decide
theorem psm_at_99a : fetchRel p256ScalarMulCode 0x99A = some (.store .sw sp a1 0x8, 2) := by decide
theorem psm_at_99c : fetchRel p256ScalarMulCode 0x99C = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem psm_at_99e : fetchRel p256ScalarMulCode 0x99E = some (.alu .add a0 a0 (30 : Fin 32), 2) := by decide
theorem psm_at_9a0 : fetchRel p256ScalarMulCode 0x9A0 = some (.alu .mul (25 : Fin 32) (6 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_9a4 : fetchRel p256ScalarMulCode 0x9A4 = some (.alu .mul a1 (19 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_9a8 : fetchRel p256ScalarMulCode 0x9A8 = some (.alu .sltu a4 a3 (8 : Fin 32), 4) := by decide
theorem psm_at_9ac : fetchRel p256ScalarMulCode 0x9AC = some (.alu .mulhu a5 (6 : Fin 32) (24 : Fin 32), 4) := by decide
theorem psm_at_9b0 : fetchRel p256ScalarMulCode 0x9B0 = some (.alu .add a0 a0 ra, 2) := by decide
theorem psm_at_9b2 : fetchRel p256ScalarMulCode 0x9B2 = some (.alu .add a2 a2 a4, 2) := by decide
theorem psm_at_9b4 : fetchRel p256ScalarMulCode 0x9B4 = some (.alu .add a0 a0 (17 : Fin 32), 2) := by decide
theorem psm_at_9b6 : fetchRel p256ScalarMulCode 0x9B6 = some (.alu .add (31 : Fin 32) (31 : Fin 32) a0, 2) := by decide
theorem psm_at_9b8 : fetchRel p256ScalarMulCode 0x9B8 = some (.load .lw a0 sp 0x2C, 2) := by decide
theorem psm_at_9ba : fetchRel p256ScalarMulCode 0x9BA = some (.load .lw (9 : Fin 32) sp 0x30, 2) := by decide
theorem psm_at_9bc : fetchRel p256ScalarMulCode 0x9BC = some (.load .lw (8 : Fin 32) sp 0x34, 2) := by decide
theorem psm_at_9be : fetchRel p256ScalarMulCode 0x9BE = some (.load .lw (19 : Fin 32) sp 0x38, 2) := by decide
theorem psm_at_9c0 : fetchRel p256ScalarMulCode 0x9C0 = some (.alu .add (25 : Fin 32) (25 : Fin 32) a3, 2) := by decide
theorem psm_at_9c2 : fetchRel p256ScalarMulCode 0x9C2 = some (.alu .add (28 : Fin 32) (28 : Fin 32) (31 : Fin 32), 2) := by decide
theorem psm_at_9c4 : fetchRel p256ScalarMulCode 0x9C4 = some (.alu .sltu a3 (25 : Fin 32) a3, 4) := by decide
theorem psm_at_9c8 : fetchRel p256ScalarMulCode 0x9C8 = some (.alu .add a3 a3 a5, 2) := by decide
theorem psm_at_9ca : fetchRel p256ScalarMulCode 0x9CA = some (.alu .add a2 a2 (28 : Fin 32), 2) := by decide
theorem psm_at_9cc : fetchRel p256ScalarMulCode 0x9CC = some (.alu .add a2 a2 a3, 2) := by decide
theorem psm_at_9ce : fetchRel p256ScalarMulCode 0x9CE = some (.store .sw sp a2 0x4, 2) := by decide
theorem psm_at_9d0 : fetchRel p256ScalarMulCode 0x9D0 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem psm_at_9d2 : fetchRel p256ScalarMulCode 0x9D2 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_9d6 : fetchRel p256ScalarMulCode 0x9D6 = some (.jalr ra ra 0x7FC, 4) := by decide
theorem psm_at_9da : fetchRel p256ScalarMulCode 0x9DA = some (.store .sw sp a0 0x0, 2) := by decide
theorem psm_at_9dc : fetchRel p256ScalarMulCode 0x9DC = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_9de : fetchRel p256ScalarMulCode 0x9DE = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem psm_at_9e0 : fetchRel p256ScalarMulCode 0x9E0 = some (.load .lw a1 sp 0x1C, 2) := by decide
theorem psm_at_9e2 : fetchRel p256ScalarMulCode 0x9E2 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_9e6 : fetchRel p256ScalarMulCode 0x9E6 = some (.jalr ra ra 0x7EC, 4) := by decide
theorem psm_at_9ea : fetchRel p256ScalarMulCode 0x9EA = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_9ec : fetchRel p256ScalarMulCode 0x9EC = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_9ee : fetchRel p256ScalarMulCode 0x9EE = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem psm_at_9f0 : fetchRel p256ScalarMulCode 0x9F0 = some (.load .lw a1 sp 0x18, 2) := by decide
theorem psm_at_9f2 : fetchRel p256ScalarMulCode 0x9F2 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_9f6 : fetchRel p256ScalarMulCode 0x9F6 = some (.jalr ra ra 0x7DC, 4) := by decide
theorem psm_at_9fa : fetchRel p256ScalarMulCode 0x9FA = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_9fc : fetchRel p256ScalarMulCode 0x9FC = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_9fe : fetchRel p256ScalarMulCode 0x9FE = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem psm_at_a00 : fetchRel p256ScalarMulCode 0xA00 = some (.load .lw a1 sp 0x14, 2) := by decide
theorem psm_at_a02 : fetchRel p256ScalarMulCode 0xA02 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a06 : fetchRel p256ScalarMulCode 0xA06 = some (.jalr ra ra 0x7CC, 4) := by decide
theorem psm_at_a0a : fetchRel p256ScalarMulCode 0xA0A = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_a0c : fetchRel p256ScalarMulCode 0xA0C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a0e : fetchRel p256ScalarMulCode 0xA0E = some (.alu .add a0 x0 (26 : Fin 32), 2) := by decide
theorem psm_at_a10 : fetchRel p256ScalarMulCode 0xA10 = some (.load .lw a1 sp 0x10, 2) := by decide
theorem psm_at_a12 : fetchRel p256ScalarMulCode 0xA12 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a16 : fetchRel p256ScalarMulCode 0xA16 = some (.jalr ra ra 0x7BC, 4) := by decide
theorem psm_at_a1a : fetchRel p256ScalarMulCode 0xA1A = some (.alu .add (26 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_a1c : fetchRel p256ScalarMulCode 0xA1C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a1e : fetchRel p256ScalarMulCode 0xA1E = some (.alu .add a0 x0 (27 : Fin 32), 2) := by decide
theorem psm_at_a20 : fetchRel p256ScalarMulCode 0xA20 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem psm_at_a22 : fetchRel p256ScalarMulCode 0xA22 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a26 : fetchRel p256ScalarMulCode 0xA26 = some (.jalr ra ra 0x7AC, 4) := by decide
theorem psm_at_a2a : fetchRel p256ScalarMulCode 0xA2A = some (.store .sw sp a0 0x18, 2) := by decide
theorem psm_at_a2c : fetchRel p256ScalarMulCode 0xA2C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a2e : fetchRel p256ScalarMulCode 0xA2E = some (.load .lw a0 sp 0x8, 2) := by decide
theorem psm_at_a30 : fetchRel p256ScalarMulCode 0xA30 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem psm_at_a32 : fetchRel p256ScalarMulCode 0xA32 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a36 : fetchRel p256ScalarMulCode 0xA36 = some (.jalr ra ra 0x79C, 4) := by decide
theorem psm_at_a3a : fetchRel p256ScalarMulCode 0xA3A = some (.alu .add (27 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_a3c : fetchRel p256ScalarMulCode 0xA3C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a3e : fetchRel p256ScalarMulCode 0xA3E = some (.load .lw a0 sp 0x24, 2) := by decide
theorem psm_at_a40 : fetchRel p256ScalarMulCode 0xA40 = some (.alu .add a1 x0 (25 : Fin 32), 2) := by decide
theorem psm_at_a42 : fetchRel p256ScalarMulCode 0xA42 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a46 : fetchRel p256ScalarMulCode 0xA46 = some (.jalr ra ra 0x78C, 4) := by decide
theorem psm_at_a4a : fetchRel p256ScalarMulCode 0xA4A = some (.store .sw sp a0 0x1C, 2) := by decide
theorem psm_at_a4c : fetchRel p256ScalarMulCode 0xA4C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a4e : fetchRel p256ScalarMulCode 0xA4E = some (.load .lw a0 sp 0x20, 2) := by decide
theorem psm_at_a50 : fetchRel p256ScalarMulCode 0xA50 = some (.load .lw a1 sp 0x4, 2) := by decide
theorem psm_at_a52 : fetchRel p256ScalarMulCode 0xA52 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a56 : fetchRel p256ScalarMulCode 0xA56 = some (.jalr ra ra 0x77C, 4) := by decide
theorem psm_at_a5a : fetchRel p256ScalarMulCode 0xA5A = some (.store .sw sp a0 0x20, 2) := by decide
theorem psm_at_a5c : fetchRel p256ScalarMulCode 0xA5C = some (.load .lw a0 sp 0x0, 2) := by decide
theorem psm_at_a5e : fetchRel p256ScalarMulCode 0xA5E = some (.alu .add a1 x0 (24 : Fin 32), 2) := by decide
theorem psm_at_a60 : fetchRel p256ScalarMulCode 0xA60 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem psm_at_a62 : fetchRel p256ScalarMulCode 0xA62 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a66 : fetchRel p256ScalarMulCode 0xA66 = some (.jalr ra ra 0x76C, 4) := by decide
theorem psm_at_a6a : fetchRel p256ScalarMulCode 0xA6A = some (.store .sw sp a0 0x24, 2) := by decide
theorem psm_at_a6c : fetchRel p256ScalarMulCode 0xA6C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a6e : fetchRel p256ScalarMulCode 0xA6E = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem psm_at_a70 : fetchRel p256ScalarMulCode 0xA70 = some (.alu .add a1 x0 (23 : Fin 32), 2) := by decide
theorem psm_at_a72 : fetchRel p256ScalarMulCode 0xA72 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a76 : fetchRel p256ScalarMulCode 0xA76 = some (.jalr ra ra 0x75C, 4) := by decide
theorem psm_at_a7a : fetchRel p256ScalarMulCode 0xA7A = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_a7c : fetchRel p256ScalarMulCode 0xA7C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a7e : fetchRel p256ScalarMulCode 0xA7E = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem psm_at_a80 : fetchRel p256ScalarMulCode 0xA80 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem psm_at_a82 : fetchRel p256ScalarMulCode 0xA82 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a86 : fetchRel p256ScalarMulCode 0xA86 = some (.jalr ra ra 0x74C, 4) := by decide
theorem psm_at_a8a : fetchRel p256ScalarMulCode 0xA8A = some (.alu .add (25 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_a8c : fetchRel p256ScalarMulCode 0xA8C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a8e : fetchRel p256ScalarMulCode 0xA8E = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem psm_at_a90 : fetchRel p256ScalarMulCode 0xA90 = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem psm_at_a92 : fetchRel p256ScalarMulCode 0xA92 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_a96 : fetchRel p256ScalarMulCode 0xA96 = some (.jalr ra ra 0x73C, 4) := by decide
theorem psm_at_a9a : fetchRel p256ScalarMulCode 0xA9A = some (.store .sw sp a0 0x14, 2) := by decide
theorem psm_at_a9c : fetchRel p256ScalarMulCode 0xA9C = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_a9e : fetchRel p256ScalarMulCode 0xA9E = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) := by decide
theorem psm_at_aa0 : fetchRel p256ScalarMulCode 0xAA0 = some (.alu .add a0 x0 (26 : Fin 32), 2) := by decide
theorem psm_at_aa2 : fetchRel p256ScalarMulCode 0xAA2 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_aa6 : fetchRel p256ScalarMulCode 0xAA6 = some (.jalr ra ra 0x72C, 4) := by decide
theorem psm_at_aaa : fetchRel p256ScalarMulCode 0xAAA = some (.alu .add (26 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_aac : fetchRel p256ScalarMulCode 0xAAC = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_aae : fetchRel p256ScalarMulCode 0xAAE = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) := by decide
theorem psm_at_ab0 : fetchRel p256ScalarMulCode 0xAB0 = some (.load .lw a0 sp 0x18, 2) := by decide
theorem psm_at_ab2 : fetchRel p256ScalarMulCode 0xAB2 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_ab6 : fetchRel p256ScalarMulCode 0xAB6 = some (.jalr ra ra 0x71C, 4) := by decide
theorem psm_at_aba : fetchRel p256ScalarMulCode 0xABA = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_abc : fetchRel p256ScalarMulCode 0xABC = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_abe : fetchRel p256ScalarMulCode 0xABE = some (.alu .add a0 x0 (27 : Fin 32), 2) := by decide
theorem psm_at_ac0 : fetchRel p256ScalarMulCode 0xAC0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem psm_at_ac2 : fetchRel p256ScalarMulCode 0xAC2 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_ac6 : fetchRel p256ScalarMulCode 0xAC6 = some (.jalr ra ra 0x70C, 4) := by decide
theorem psm_at_aca : fetchRel p256ScalarMulCode 0xACA = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_acc : fetchRel p256ScalarMulCode 0xACC = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_ace : fetchRel p256ScalarMulCode 0xACE = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) := by decide
theorem psm_at_ad0 : fetchRel p256ScalarMulCode 0xAD0 = some (.load .lw a0 sp 0x1C, 2) := by decide
theorem psm_at_ad2 : fetchRel p256ScalarMulCode 0xAD2 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_ad6 : fetchRel p256ScalarMulCode 0xAD6 = some (.jalr ra ra 0x6FC, 4) := by decide
theorem psm_at_ada : fetchRel p256ScalarMulCode 0xADA = some (.alu .add (27 : Fin 32) x0 a0, 2) := by decide
theorem psm_at_adc : fetchRel p256ScalarMulCode 0xADC = some (.alu .add a2 x0 a1, 2) := by decide
theorem psm_at_ade : fetchRel p256ScalarMulCode 0xADE = some (.load .lw a0 sp 0x20, 2) := by decide
theorem psm_at_ae0 : fetchRel p256ScalarMulCode 0xAE0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem psm_at_ae2 : fetchRel p256ScalarMulCode 0xAE2 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem psm_at_ae6 : fetchRel p256ScalarMulCode 0xAE6 = some (.jalr ra ra 0x6EC, 4) := by decide
theorem psm_at_aea : fetchRel p256ScalarMulCode 0xAEA = some (.alu .and a0 a1 (24 : Fin 32), 4) := by decide
theorem psm_at_aee : fetchRel p256ScalarMulCode 0xAEE = some (.alu .and a2 a1 (23 : Fin 32), 4) := by decide
theorem psm_at_af2 : fetchRel p256ScalarMulCode 0xAF2 = some (.load .lw a6 sp 0x24, 2) := by decide
theorem psm_at_af4 : fetchRel p256ScalarMulCode 0xAF4 = some (.alu .add a6 a6 a0, 2) := by decide
theorem psm_at_af6 : fetchRel p256ScalarMulCode 0xAF6 = some (.alu .add (19 : Fin 32) (19 : Fin 32) a2, 2) := by decide
theorem psm_at_af8 : fetchRel p256ScalarMulCode 0xAF8 = some (.alu .sltu a0 a6 a0, 4) := by decide
theorem psm_at_afc : fetchRel p256ScalarMulCode 0xAFC = some (.alu .and a4 a1 (21 : Fin 32), 4) := by decide
theorem psm_at_b00 : fetchRel p256ScalarMulCode 0xB00 = some (.alu .add a0 a0 (19 : Fin 32), 2) := by decide
theorem psm_at_b02 : fetchRel p256ScalarMulCode 0xB02 = some (.alu .sltu a2 (19 : Fin 32) a2, 4) := by decide
theorem psm_at_b06 : fetchRel p256ScalarMulCode 0xB06 = some (.alu .sltu a5 a0 (19 : Fin 32), 4) := by decide
theorem psm_at_b0a : fetchRel p256ScalarMulCode 0xB0A = some (.alu .add (25 : Fin 32) (25 : Fin 32) a4, 2) := by decide
theorem psm_at_b0c : fetchRel p256ScalarMulCode 0xB0C = some (.alu .add a2 a2 a5, 2) := by decide
theorem psm_at_b0e : fetchRel p256ScalarMulCode 0xB0E = some (.alu .and (8 : Fin 32) a1 (22 : Fin 32), 4) := by decide
theorem psm_at_b12 : fetchRel p256ScalarMulCode 0xB12 = some (.alu .add a2 a2 (25 : Fin 32), 2) := by decide
theorem psm_at_b14 : fetchRel p256ScalarMulCode 0xB14 = some (.alu .sltu a4 (25 : Fin 32) a4, 4) := by decide
theorem psm_at_b18 : fetchRel p256ScalarMulCode 0xB18 = some (.alu .sltu (9 : Fin 32) a2 (25 : Fin 32), 4) := by decide
theorem psm_at_b1c : fetchRel p256ScalarMulCode 0xB1C = some (.load .lw a5 sp 0x14, 2) := by decide
theorem psm_at_b1e : fetchRel p256ScalarMulCode 0xB1E = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem psm_at_b20 : fetchRel p256ScalarMulCode 0xB20 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem psm_at_b22 : fetchRel p256ScalarMulCode 0xB22 = some (.alu .add a4 a4 a5, 2) := by decide
theorem psm_at_b24 : fetchRel p256ScalarMulCode 0xB24 = some (.alu .sltu (9 : Fin 32) a5 (8 : Fin 32), 4) := by decide
theorem psm_at_b28 : fetchRel p256ScalarMulCode 0xB28 = some (.alu .sltu a5 a4 a5, 4) := by decide
theorem psm_at_b2c : fetchRel p256ScalarMulCode 0xB2C = some (.alu .add (26 : Fin 32) (26 : Fin 32) a1, 2) := by decide
theorem psm_at_b2e : fetchRel p256ScalarMulCode 0xB2E = some (.alu .add a5 a5 (9 : Fin 32), 2) := by decide
theorem psm_at_b30 : fetchRel p256ScalarMulCode 0xB30 = some (.alu .add a5 a5 (26 : Fin 32), 2) := by decide
theorem psm_at_b32 : fetchRel p256ScalarMulCode 0xB32 = some (.alu .sltu (9 : Fin 32) (26 : Fin 32) a1, 4) := by decide
theorem psm_at_b36 : fetchRel p256ScalarMulCode 0xB36 = some (.alu .sltu (8 : Fin 32) a5 (26 : Fin 32), 4) := by decide
theorem psm_at_b3a : fetchRel p256ScalarMulCode 0xB3A = some (.alu .add (20 : Fin 32) (20 : Fin 32) a1, 2) := by decide
theorem psm_at_b3c : fetchRel p256ScalarMulCode 0xB3C = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem psm_at_b3e : fetchRel p256ScalarMulCode 0xB3E = some (.alu .add (8 : Fin 32) (8 : Fin 32) (20 : Fin 32), 2) := by decide
theorem psm_at_b40 : fetchRel p256ScalarMulCode 0xB40 = some (.alu .sltu (9 : Fin 32) (20 : Fin 32) a1, 4) := by decide
theorem psm_at_b44 : fetchRel p256ScalarMulCode 0xB44 = some (.alu .sltu a3 (8 : Fin 32) (20 : Fin 32), 4) := by decide
theorem psm_at_b48 : fetchRel p256ScalarMulCode 0xB48 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem psm_at_b4a : fetchRel p256ScalarMulCode 0xB4A = some (.alu .add a1 a1 (27 : Fin 32), 2) := by decide
theorem psm_at_b4c : fetchRel p256ScalarMulCode 0xB4C = some (.alu .add (18 : Fin 32) (18 : Fin 32) a3, 2) := by decide
theorem psm_at_b4e : fetchRel p256ScalarMulCode 0xB4E = some (.alu .sltu a3 (18 : Fin 32) a3, 4) := by decide
theorem psm_at_b52 : fetchRel p256ScalarMulCode 0xB52 = some (.load .lw (9 : Fin 32) sp 0x28, 2) := by decide
theorem psm_at_b54 : fetchRel p256ScalarMulCode 0xB54 = some (.store .sw (9 : Fin 32) a6 0x0, 4) := by decide
theorem psm_at_b58 : fetchRel p256ScalarMulCode 0xB58 = some (.store .sw (9 : Fin 32) a0 0x4, 2) := by decide
theorem psm_at_b5a : fetchRel p256ScalarMulCode 0xB5A = some (.store .sw (9 : Fin 32) a2 0x8, 2) := by decide
theorem psm_at_b5c : fetchRel p256ScalarMulCode 0xB5C = some (.store .sw (9 : Fin 32) a4 0xC, 2) := by decide
theorem psm_at_b5e : fetchRel p256ScalarMulCode 0xB5E = some (.alu .add a1 a1 a3, 2) := by decide
theorem psm_at_b60 : fetchRel p256ScalarMulCode 0xB60 = some (.store .sw (9 : Fin 32) a5 0x10, 2) := by decide
theorem psm_at_b62 : fetchRel p256ScalarMulCode 0xB62 = some (.store .sw (9 : Fin 32) (8 : Fin 32) 0x14, 2) := by decide
theorem psm_at_b64 : fetchRel p256ScalarMulCode 0xB64 = some (.store .sw (9 : Fin 32) (18 : Fin 32) 0x18, 4) := by decide
theorem psm_at_b68 : fetchRel p256ScalarMulCode 0xB68 = some (.store .sw (9 : Fin 32) a1 0x1C, 2) := by decide
theorem psm_at_b6a : fetchRel p256ScalarMulCode 0xB6A = some (.load .lw ra sp 0x9C, 2) := by decide
theorem psm_at_b6c : fetchRel p256ScalarMulCode 0xB6C = some (.load .lw (8 : Fin 32) sp 0x98, 2) := by decide
theorem psm_at_b6e : fetchRel p256ScalarMulCode 0xB6E = some (.load .lw (9 : Fin 32) sp 0x94, 2) := by decide
theorem psm_at_b70 : fetchRel p256ScalarMulCode 0xB70 = some (.load .lw (18 : Fin 32) sp 0x90, 2) := by decide
theorem psm_at_b72 : fetchRel p256ScalarMulCode 0xB72 = some (.load .lw (19 : Fin 32) sp 0x8C, 2) := by decide
theorem psm_at_b74 : fetchRel p256ScalarMulCode 0xB74 = some (.load .lw (20 : Fin 32) sp 0x88, 2) := by decide
theorem psm_at_b76 : fetchRel p256ScalarMulCode 0xB76 = some (.load .lw (21 : Fin 32) sp 0x84, 2) := by decide
theorem psm_at_b78 : fetchRel p256ScalarMulCode 0xB78 = some (.load .lw (22 : Fin 32) sp 0x80, 2) := by decide
theorem psm_at_b7a : fetchRel p256ScalarMulCode 0xB7A = some (.load .lw (23 : Fin 32) sp 0x7C, 2) := by decide
theorem psm_at_b7c : fetchRel p256ScalarMulCode 0xB7C = some (.load .lw (24 : Fin 32) sp 0x78, 2) := by decide
theorem psm_at_b7e : fetchRel p256ScalarMulCode 0xB7E = some (.load .lw (25 : Fin 32) sp 0x74, 2) := by decide
theorem psm_at_b80 : fetchRel p256ScalarMulCode 0xB80 = some (.load .lw (26 : Fin 32) sp 0x70, 2) := by decide
theorem psm_at_b82 : fetchRel p256ScalarMulCode 0xB82 = some (.load .lw (27 : Fin 32) sp 0x6C, 2) := by decide
theorem psm_at_b84 : fetchRel p256ScalarMulCode 0xB84 = some (.aluImm .add sp sp 0xA0, 2) := by decide
theorem psm_at_b86 : fetchRel p256ScalarMulCode 0xB86 = some (.jalr x0 ra 0x0, 2) := by decide
end

end C3.RV32
