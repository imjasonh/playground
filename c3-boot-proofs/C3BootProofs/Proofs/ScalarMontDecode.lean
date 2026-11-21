import C3BootProofs.Proofs.Scalar29Sub

/-!
# Decoded instructions of `Scalar29::montgomery_mul`

`scripts/decode-lemmas.py` writes these lemmas from `llvm-objdump` output,
and `decide` checks each one against the extracted bytes.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000

theorem smm_at_0 : fetchRel scalar29MontMulCode 0x0 = some (.aluImm .add sp sp 0xFFFFFE70, 2) := by decide
theorem smm_at_2 : fetchRel scalar29MontMulCode 0x2 = some (.aluImm .add a3 sp 0x180, 2) := by decide
theorem smm_at_4 : fetchRel scalar29MontMulCode 0x4 = some (.store .sw a3 ra 0xC, 4) := by decide
theorem smm_at_8 : fetchRel scalar29MontMulCode 0x8 = some (.store .sw a3 (8 : Fin 32) 0x8, 2) := by decide
theorem smm_at_a : fetchRel scalar29MontMulCode 0xA = some (.store .sw a3 (9 : Fin 32) 0x4, 2) := by decide
theorem smm_at_c : fetchRel scalar29MontMulCode 0xC = some (.store .sw a3 (18 : Fin 32) 0x0, 4) := by decide
theorem smm_at_10 : fetchRel scalar29MontMulCode 0x10 = some (.store .sw sp (19 : Fin 32) 0x17C, 4) := by decide
theorem smm_at_14 : fetchRel scalar29MontMulCode 0x14 = some (.store .sw sp (20 : Fin 32) 0x178, 4) := by decide
theorem smm_at_18 : fetchRel scalar29MontMulCode 0x18 = some (.store .sw sp (21 : Fin 32) 0x174, 4) := by decide
theorem smm_at_1c : fetchRel scalar29MontMulCode 0x1C = some (.store .sw sp (22 : Fin 32) 0x170, 4) := by decide
theorem smm_at_20 : fetchRel scalar29MontMulCode 0x20 = some (.store .sw sp (23 : Fin 32) 0x16C, 4) := by decide
theorem smm_at_24 : fetchRel scalar29MontMulCode 0x24 = some (.store .sw sp (24 : Fin 32) 0x168, 4) := by decide
theorem smm_at_28 : fetchRel scalar29MontMulCode 0x28 = some (.store .sw sp (25 : Fin 32) 0x164, 4) := by decide
theorem smm_at_2c : fetchRel scalar29MontMulCode 0x2C = some (.store .sw sp (26 : Fin 32) 0x160, 4) := by decide
theorem smm_at_30 : fetchRel scalar29MontMulCode 0x30 = some (.store .sw sp (27 : Fin 32) 0x15C, 4) := by decide
theorem smm_at_34 : fetchRel scalar29MontMulCode 0x34 = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem smm_at_36 : fetchRel scalar29MontMulCode 0x36 = some (.alu .add (25 : Fin 32) x0 a1, 2) := by decide
theorem smm_at_38 : fetchRel scalar29MontMulCode 0x38 = some (.store .sw sp a0 0xF8, 2) := by decide
theorem smm_at_3a : fetchRel scalar29MontMulCode 0x3A = some (.load .lw (30 : Fin 32) a2 0x4, 4) := by decide
theorem smm_at_3e : fetchRel scalar29MontMulCode 0x3E = some (.load .lw (29 : Fin 32) a1 0x0, 4) := by decide
theorem smm_at_42 : fetchRel scalar29MontMulCode 0x42 = some (.load .lw (22 : Fin 32) a1 0x4, 4) := by decide
theorem smm_at_46 : fetchRel scalar29MontMulCode 0x46 = some (.load .lw (26 : Fin 32) a2 0x0, 4) := by decide
theorem smm_at_4a : fetchRel scalar29MontMulCode 0x4A = some (.load .lw (20 : Fin 32) a2 0x8, 4) := by decide
theorem smm_at_4e : fetchRel scalar29MontMulCode 0x4E = some (.load .lw (28 : Fin 32) a2 0xC, 4) := by decide
theorem smm_at_52 : fetchRel scalar29MontMulCode 0x52 = some (.load .lw (5 : Fin 32) a1 0x8, 4) := by decide
theorem smm_at_56 : fetchRel scalar29MontMulCode 0x56 = some (.load .lw (21 : Fin 32) a1 0xC, 4) := by decide
theorem smm_at_5a : fetchRel scalar29MontMulCode 0x5A = some (.alu .mul a6 (30 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_5e : fetchRel scalar29MontMulCode 0x5E = some (.alu .mulhu a1 (30 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_62 : fetchRel scalar29MontMulCode 0x62 = some (.alu .mul a3 (22 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_66 : fetchRel scalar29MontMulCode 0x66 = some (.alu .mulhu a4 (22 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_6a : fetchRel scalar29MontMulCode 0x6A = some (.alu .mulhu a5 (20 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_6e : fetchRel scalar29MontMulCode 0x6E = some (.alu .mulhu (9 : Fin 32) (22 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_72 : fetchRel scalar29MontMulCode 0x72 = some (.alu .mul (8 : Fin 32) (20 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_76 : fetchRel scalar29MontMulCode 0x76 = some (.alu .mul a0 (22 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_7a : fetchRel scalar29MontMulCode 0x7A = some (.alu .mul (17 : Fin 32) (5 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_7e : fetchRel scalar29MontMulCode 0x7E = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_80 : fetchRel scalar29MontMulCode 0x80 = some (.alu .add a6 a6 a3, 2) := by decide
theorem smm_at_82 : fetchRel scalar29MontMulCode 0x82 = some (.store .sw sp a6 0x10C, 4) := by decide
theorem smm_at_86 : fetchRel scalar29MontMulCode 0x86 = some (.alu .add (31 : Fin 32) a5 (9 : Fin 32), 4) := by decide
theorem smm_at_8a : fetchRel scalar29MontMulCode 0x8A = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem smm_at_8c : fetchRel scalar29MontMulCode 0x8C = some (.alu .mulhu a4 (5 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_90 : fetchRel scalar29MontMulCode 0x90 = some (.alu .sltu a3 a6 a3, 4) := by decide
theorem smm_at_94 : fetchRel scalar29MontMulCode 0x94 = some (.alu .mul a6 (20 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_98 : fetchRel scalar29MontMulCode 0x98 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_9a : fetchRel scalar29MontMulCode 0x9A = some (.store .sw sp a1 0x110, 4) := by decide
theorem smm_at_9e : fetchRel scalar29MontMulCode 0x9E = some (.alu .mul a1 (5 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_a2 : fetchRel scalar29MontMulCode 0xA2 = some (.alu .mulhu a3 (20 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_a6 : fetchRel scalar29MontMulCode 0xA6 = some (.alu .mulhu (9 : Fin 32) (5 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_aa : fetchRel scalar29MontMulCode 0xAA = some (.alu .mulhu (6 : Fin 32) (28 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_ae : fetchRel scalar29MontMulCode 0xAE = some (.alu .mul a5 (28 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_b2 : fetchRel scalar29MontMulCode 0xB2 = some (.alu .sltu (8 : Fin 32) a0 (8 : Fin 32), 4) := by decide
theorem smm_at_b6 : fetchRel scalar29MontMulCode 0xB6 = some (.alu .add (17 : Fin 32) (17 : Fin 32) a0, 2) := by decide
theorem smm_at_b8 : fetchRel scalar29MontMulCode 0xB8 = some (.store .sw sp (17 : Fin 32) 0x11C, 4) := by decide
theorem smm_at_bc : fetchRel scalar29MontMulCode 0xBC = some (.alu .sltu (17 : Fin 32) (17 : Fin 32) a0, 4) := by decide
theorem smm_at_c0 : fetchRel scalar29MontMulCode 0xC0 = some (.alu .add a4 a4 (31 : Fin 32), 2) := by decide
theorem smm_at_c2 : fetchRel scalar29MontMulCode 0xC2 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem smm_at_c4 : fetchRel scalar29MontMulCode 0xC4 = some (.alu .mul a0 (21 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_c8 : fetchRel scalar29MontMulCode 0xC8 = some (.alu .mulhu (31 : Fin 32) (21 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_cc : fetchRel scalar29MontMulCode 0xCC = some (.alu .add a6 a6 a1, 2) := by decide
theorem smm_at_ce : fetchRel scalar29MontMulCode 0xCE = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem smm_at_d0 : fetchRel scalar29MontMulCode 0xD0 = some (.alu .sltu a1 a6 a1, 4) := by decide
theorem smm_at_d4 : fetchRel scalar29MontMulCode 0xD4 = some (.alu .add a5 a5 a6, 2) := by decide
theorem smm_at_d6 : fetchRel scalar29MontMulCode 0xD6 = some (.alu .add a3 a3 (6 : Fin 32), 2) := by decide
theorem smm_at_d8 : fetchRel scalar29MontMulCode 0xD8 = some (.alu .sltu (9 : Fin 32) a5 a6, 4) := by decide
theorem smm_at_dc : fetchRel scalar29MontMulCode 0xDC = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_de : fetchRel scalar29MontMulCode 0xDE = some (.alu .mulhu a3 (28 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_e2 : fetchRel scalar29MontMulCode 0xE2 = some (.alu .mulhu (8 : Fin 32) (5 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_e6 : fetchRel scalar29MontMulCode 0xE6 = some (.alu .add a4 a4 (17 : Fin 32), 2) := by decide
theorem smm_at_e8 : fetchRel scalar29MontMulCode 0xE8 = some (.store .sw sp a4 0x118, 4) := by decide
theorem smm_at_ec : fetchRel scalar29MontMulCode 0xEC = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem smm_at_ee : fetchRel scalar29MontMulCode 0xEE = some (.alu .add a0 a0 a5, 2) := by decide
theorem smm_at_f0 : fetchRel scalar29MontMulCode 0xF0 = some (.store .sw sp a0 0x108, 4) := by decide
theorem smm_at_f4 : fetchRel scalar29MontMulCode 0xF4 = some (.alu .mulhu (18 : Fin 32) (21 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_f8 : fetchRel scalar29MontMulCode 0xF8 = some (.alu .mul a4 (28 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_fc : fetchRel scalar29MontMulCode 0xFC = some (.alu .mul a6 (5 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_100 : fetchRel scalar29MontMulCode 0x100 = some (.load .lw (7 : Fin 32) a2 0x10, 4) := by decide
theorem smm_at_104 : fetchRel scalar29MontMulCode 0x104 = some (.alu .mul (23 : Fin 32) (21 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_108 : fetchRel scalar29MontMulCode 0x108 = some (.alu .add (31 : Fin 32) (31 : Fin 32) a1, 2) := by decide
theorem smm_at_10a : fetchRel scalar29MontMulCode 0x10A = some (.alu .sltu (9 : Fin 32) a0 a5, 4) := by decide
theorem smm_at_10e : fetchRel scalar29MontMulCode 0x10E = some (.alu .add (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem smm_at_110 : fetchRel scalar29MontMulCode 0x110 = some (.load .lw (17 : Fin 32) a2 0x14, 4) := by decide
theorem smm_at_114 : fetchRel scalar29MontMulCode 0x114 = some (.load .lw (6 : Fin 32) a2 0x18, 4) := by decide
theorem smm_at_118 : fetchRel scalar29MontMulCode 0x118 = some (.load .lw a0 a2 0x1C, 2) := by decide
theorem smm_at_11a : fetchRel scalar29MontMulCode 0x11A = some (.store .sw sp a0 0x88, 2) := by decide
theorem smm_at_11c : fetchRel scalar29MontMulCode 0x11C = some (.store .sw sp (29 : Fin 32) 0x100, 4) := by decide
theorem smm_at_120 : fetchRel scalar29MontMulCode 0x120 = some (.alu .mulhu (24 : Fin 32) (7 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_124 : fetchRel scalar29MontMulCode 0x124 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (18 : Fin 32), 2) := by decide
theorem smm_at_126 : fetchRel scalar29MontMulCode 0x126 = some (.alu .add a3 x0 (25 : Fin 32), 2) := by decide
theorem smm_at_128 : fetchRel scalar29MontMulCode 0x128 = some (.load .lw a1 a3 0x10, 2) := by decide
theorem smm_at_12a : fetchRel scalar29MontMulCode 0x12A = some (.alu .add a6 a6 a4, 2) := by decide
theorem smm_at_12c : fetchRel scalar29MontMulCode 0x12C = some (.alu .sltu a4 a6 a4, 4) := by decide
theorem smm_at_130 : fetchRel scalar29MontMulCode 0x130 = some (.alu .add (23 : Fin 32) (23 : Fin 32) a6, 2) := by decide
theorem smm_at_132 : fetchRel scalar29MontMulCode 0x132 = some (.alu .sltu a5 (23 : Fin 32) a6, 4) := by decide
theorem smm_at_136 : fetchRel scalar29MontMulCode 0x136 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem smm_at_138 : fetchRel scalar29MontMulCode 0x138 = some (.alu .mul (18 : Fin 32) (7 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_13c : fetchRel scalar29MontMulCode 0x13C = some (.alu .add a0 a4 a5, 4) := by decide
theorem smm_at_140 : fetchRel scalar29MontMulCode 0x140 = some (.load .lw a6 (25 : Fin 32) 0x14, 4) := by decide
theorem smm_at_144 : fetchRel scalar29MontMulCode 0x144 = some (.load .lw (29 : Fin 32) (25 : Fin 32) 0x18, 4) := by decide
theorem smm_at_148 : fetchRel scalar29MontMulCode 0x148 = some (.load .lw a2 a3 0x1C, 2) := by decide
theorem smm_at_14a : fetchRel scalar29MontMulCode 0x14A = some (.store .sw sp a2 0x84, 2) := by decide
theorem smm_at_14c : fetchRel scalar29MontMulCode 0x14C = some (.alu .add a2 x0 a1, 2) := by decide
theorem smm_at_14e : fetchRel scalar29MontMulCode 0x14E = some (.alu .add a3 x0 (26 : Fin 32), 2) := by decide
theorem smm_at_150 : fetchRel scalar29MontMulCode 0x150 = some (.alu .mulhu ra a1 (26 : Fin 32), 4) := by decide
theorem smm_at_154 : fetchRel scalar29MontMulCode 0x154 = some (.alu .mulhu (26 : Fin 32) (28 : Fin 32) (5 : Fin 32), 4) := by decide
theorem smm_at_158 : fetchRel scalar29MontMulCode 0x158 = some (.alu .mulhu (27 : Fin 32) (21 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_15c : fetchRel scalar29MontMulCode 0x15C = some (.alu .add (31 : Fin 32) (31 : Fin 32) (9 : Fin 32), 2) := by decide
theorem smm_at_15e : fetchRel scalar29MontMulCode 0x15E = some (.store .sw sp (31 : Fin 32) 0x114, 4) := by decide
theorem smm_at_162 : fetchRel scalar29MontMulCode 0x162 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a0, 2) := by decide
theorem smm_at_164 : fetchRel scalar29MontMulCode 0x164 = some (.alu .mul (31 : Fin 32) (28 : Fin 32) (5 : Fin 32), 4) := by decide
theorem smm_at_168 : fetchRel scalar29MontMulCode 0x168 = some (.alu .mul (8 : Fin 32) (21 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_16c : fetchRel scalar29MontMulCode 0x16C = some (.alu .add (18 : Fin 32) (18 : Fin 32) (23 : Fin 32), 2) := by decide
theorem smm_at_16e : fetchRel scalar29MontMulCode 0x16E = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem smm_at_170 : fetchRel scalar29MontMulCode 0x170 = some (.store .sw sp (22 : Fin 32) 0xE0, 2) := by decide
theorem smm_at_172 : fetchRel scalar29MontMulCode 0x172 = some (.alu .mulhu (22 : Fin 32) (7 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_176 : fetchRel scalar29MontMulCode 0x176 = some (.alu .sltu a0 (18 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_17a : fetchRel scalar29MontMulCode 0x17A = some (.alu .mul (23 : Fin 32) (7 : Fin 32) a1, 4) := by decide
theorem smm_at_17e : fetchRel scalar29MontMulCode 0x17E = some (.alu .add a0 a0 ra, 2) := by decide
theorem smm_at_180 : fetchRel scalar29MontMulCode 0x180 = some (.store .sw sp (30 : Fin 32) 0xEC, 2) := by decide
theorem smm_at_182 : fetchRel scalar29MontMulCode 0x182 = some (.alu .mul ra a2 (30 : Fin 32), 4) := by decide
theorem smm_at_186 : fetchRel scalar29MontMulCode 0x186 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a0, 2) := by decide
theorem smm_at_188 : fetchRel scalar29MontMulCode 0x188 = some (.alu .add (26 : Fin 32) (26 : Fin 32) (27 : Fin 32), 2) := by decide
theorem smm_at_18a : fetchRel scalar29MontMulCode 0x18A = some (.alu .mulhu a1 a2 (30 : Fin 32), 4) := by decide
theorem smm_at_18e : fetchRel scalar29MontMulCode 0x18E = some (.alu .mulhu (27 : Fin 32) (17 : Fin 32) a6, 4) := by decide
theorem smm_at_192 : fetchRel scalar29MontMulCode 0x192 = some (.alu .add (31 : Fin 32) (31 : Fin 32) (8 : Fin 32), 2) := by decide
theorem smm_at_194 : fetchRel scalar29MontMulCode 0x194 = some (.alu .mul a0 a2 a3, 4) := by decide
theorem smm_at_198 : fetchRel scalar29MontMulCode 0x198 = some (.alu .add (30 : Fin 32) x0 a3, 2) := by decide
theorem smm_at_19a : fetchRel scalar29MontMulCode 0x19A = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem smm_at_19c : fetchRel scalar29MontMulCode 0x19C = some (.alu .add (22 : Fin 32) (22 : Fin 32) (26 : Fin 32), 2) := by decide
theorem smm_at_19e : fetchRel scalar29MontMulCode 0x19E = some (.alu .sltu (8 : Fin 32) (31 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_1a2 : fetchRel scalar29MontMulCode 0x1A2 = some (.alu .add (22 : Fin 32) (22 : Fin 32) (8 : Fin 32), 2) := by decide
theorem smm_at_1a4 : fetchRel scalar29MontMulCode 0x1A4 = some (.alu .add (23 : Fin 32) (23 : Fin 32) (31 : Fin 32), 2) := by decide
theorem smm_at_1a6 : fetchRel scalar29MontMulCode 0x1A6 = some (.alu .sltu (8 : Fin 32) (23 : Fin 32) (31 : Fin 32), 4) := by decide
theorem smm_at_1aa : fetchRel scalar29MontMulCode 0x1AA = some (.alu .add ra ra (23 : Fin 32), 2) := by decide
theorem smm_at_1ac : fetchRel scalar29MontMulCode 0x1AC = some (.alu .add (8 : Fin 32) (8 : Fin 32) (22 : Fin 32), 2) := by decide
theorem smm_at_1ae : fetchRel scalar29MontMulCode 0x1AE = some (.alu .sltu (31 : Fin 32) ra (23 : Fin 32), 4) := by decide
theorem smm_at_1b2 : fetchRel scalar29MontMulCode 0x1B2 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem smm_at_1b4 : fetchRel scalar29MontMulCode 0x1B4 = some (.alu .sub (8 : Fin 32) (31 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_1b8 : fetchRel scalar29MontMulCode 0x1B8 = some (.alu .add a0 a0 (18 : Fin 32), 2) := by decide
theorem smm_at_1ba : fetchRel scalar29MontMulCode 0x1BA = some (.store .sw sp a0 0x104, 4) := by decide
theorem smm_at_1be : fetchRel scalar29MontMulCode 0x1BE = some (.alu .mul a2 (17 : Fin 32) a6, 4) := by decide
theorem smm_at_1c2 : fetchRel scalar29MontMulCode 0x1C2 = some (.alu .add (31 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem smm_at_1c6 : fetchRel scalar29MontMulCode 0x1C6 = some (.alu .sltu (26 : Fin 32) a0 (18 : Fin 32), 4) := by decide
theorem smm_at_1ca : fetchRel scalar29MontMulCode 0x1CA = some (.alu .mul (18 : Fin 32) (6 : Fin 32) a6, 4) := by decide
theorem smm_at_1ce : fetchRel scalar29MontMulCode 0x1CE = some (.alu .mul a1 (29 : Fin 32) (17 : Fin 32), 4) := by decide
theorem smm_at_1d2 : fetchRel scalar29MontMulCode 0x1D2 = some (.alu .mulhu (22 : Fin 32) (6 : Fin 32) a6, 4) := by decide
theorem smm_at_1d6 : fetchRel scalar29MontMulCode 0x1D6 = some (.alu .mulhu (23 : Fin 32) (29 : Fin 32) (17 : Fin 32), 4) := by decide
theorem smm_at_1da : fetchRel scalar29MontMulCode 0x1DA = some (.store .sw sp (5 : Fin 32) 0xAC, 2) := by decide
theorem smm_at_1dc : fetchRel scalar29MontMulCode 0x1DC = some (.alu .mul (8 : Fin 32) (7 : Fin 32) (5 : Fin 32), 4) := by decide
theorem smm_at_1e0 : fetchRel scalar29MontMulCode 0x1E0 = some (.alu .mulhu (27 : Fin 32) (7 : Fin 32) (5 : Fin 32), 4) := by decide
theorem smm_at_1e4 : fetchRel scalar29MontMulCode 0x1E4 = some (.alu .mul a5 (21 : Fin 32) (28 : Fin 32), 4) := by decide
theorem smm_at_1e8 : fetchRel scalar29MontMulCode 0x1E8 = some (.alu .mulhu a3 (21 : Fin 32) (28 : Fin 32), 4) := by decide
theorem smm_at_1ec : fetchRel scalar29MontMulCode 0x1EC = some (.store .sw sp (20 : Fin 32) 0xE8, 2) := by decide
theorem smm_at_1ee : fetchRel scalar29MontMulCode 0x1EE = some (.alu .mulhu a4 (9 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_1f2 : fetchRel scalar29MontMulCode 0x1F2 = some (.alu .sltu a0 ra a2, 4) := by decide
theorem smm_at_1f6 : fetchRel scalar29MontMulCode 0x1F6 = some (.alu .add (24 : Fin 32) (24 : Fin 32) (26 : Fin 32), 2) := by decide
theorem smm_at_1f8 : fetchRel scalar29MontMulCode 0x1F8 = some (.store .sw sp (24 : Fin 32) 0x120, 4) := by decide
theorem smm_at_1fc : fetchRel scalar29MontMulCode 0x1FC = some (.alu .sub a0 (31 : Fin 32) a0, 4) := by decide
theorem smm_at_200 : fetchRel scalar29MontMulCode 0x200 = some (.store .sw sp a0 0x124, 4) := by decide
theorem smm_at_204 : fetchRel scalar29MontMulCode 0x204 = some (.alu .add (18 : Fin 32) (18 : Fin 32) a1, 2) := by decide
theorem smm_at_206 : fetchRel scalar29MontMulCode 0x206 = some (.alu .mul a0 (9 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_20a : fetchRel scalar29MontMulCode 0x20A = some (.alu .add (22 : Fin 32) (22 : Fin 32) (23 : Fin 32), 2) := by decide
theorem smm_at_20c : fetchRel scalar29MontMulCode 0x20C = some (.alu .sltu a1 (18 : Fin 32) a1, 4) := by decide
theorem smm_at_210 : fetchRel scalar29MontMulCode 0x210 = some (.alu .sub a2 ra a2, 4) := by decide
theorem smm_at_214 : fetchRel scalar29MontMulCode 0x214 = some (.store .sw sp a2 0x134, 4) := by decide
theorem smm_at_218 : fetchRel scalar29MontMulCode 0x218 = some (.alu .add (22 : Fin 32) (22 : Fin 32) a1, 2) := by decide
theorem smm_at_21a : fetchRel scalar29MontMulCode 0x21A = some (.alu .add a3 a3 (27 : Fin 32), 2) := by decide
theorem smm_at_21c : fetchRel scalar29MontMulCode 0x21C = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem smm_at_21e : fetchRel scalar29MontMulCode 0x21E = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_220 : fetchRel scalar29MontMulCode 0x220 = some (.alu .sltu a2 a5 (8 : Fin 32), 4) := by decide
theorem smm_at_224 : fetchRel scalar29MontMulCode 0x224 = some (.alu .mulhu a4 (29 : Fin 32) (6 : Fin 32), 4) := by decide
theorem smm_at_228 : fetchRel scalar29MontMulCode 0x228 = some (.load .lw (5 : Fin 32) sp 0x88, 2) := by decide
theorem smm_at_22a : fetchRel scalar29MontMulCode 0x22A = some (.alu .mulhu (8 : Fin 32) (5 : Fin 32) a6, 4) := by decide
theorem smm_at_22e : fetchRel scalar29MontMulCode 0x22E = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_230 : fetchRel scalar29MontMulCode 0x230 = some (.alu .add a0 a0 a5, 2) := by decide
theorem smm_at_232 : fetchRel scalar29MontMulCode 0x232 = some (.alu .sltu a3 a0 a5, 4) := by decide
theorem smm_at_236 : fetchRel scalar29MontMulCode 0x236 = some (.alu .mul (31 : Fin 32) (29 : Fin 32) (6 : Fin 32), 4) := by decide
theorem smm_at_23a : fetchRel scalar29MontMulCode 0x23A = some (.alu .mul a1 (5 : Fin 32) a6, 4) := by decide
theorem smm_at_23e : fetchRel scalar29MontMulCode 0x23E = some (.load .lw ra sp 0x84, 2) := by decide
theorem smm_at_240 : fetchRel scalar29MontMulCode 0x240 = some (.alu .mulhu (23 : Fin 32) ra (17 : Fin 32), 4) := by decide
theorem smm_at_244 : fetchRel scalar29MontMulCode 0x244 = some (.alu .sltu a5 a0 (18 : Fin 32), 4) := by decide
theorem smm_at_248 : fetchRel scalar29MontMulCode 0x248 = some (.alu .mul (24 : Fin 32) ra (17 : Fin 32), 4) := by decide
theorem smm_at_24c : fetchRel scalar29MontMulCode 0x24C = some (.alu .add (26 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem smm_at_24e : fetchRel scalar29MontMulCode 0x24E = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_250 : fetchRel scalar29MontMulCode 0x250 = some (.alu .add a5 a5 (22 : Fin 32), 2) := by decide
theorem smm_at_252 : fetchRel scalar29MontMulCode 0x252 = some (.alu .sub a2 a2 a5, 2) := by decide
theorem smm_at_254 : fetchRel scalar29MontMulCode 0x254 = some (.store .sw sp a2 0x12C, 4) := by decide
theorem smm_at_258 : fetchRel scalar29MontMulCode 0x258 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem smm_at_25a : fetchRel scalar29MontMulCode 0x25A = some (.store .sw sp (7 : Fin 32) 0xB8, 2) := by decide
theorem smm_at_25c : fetchRel scalar29MontMulCode 0x25C = some (.store .sw sp (21 : Fin 32) 0xC8, 2) := by decide
theorem smm_at_25e : fetchRel scalar29MontMulCode 0x25E = some (.alu .mulhu a2 (7 : Fin 32) (21 : Fin 32), 4) := by decide
theorem smm_at_262 : fetchRel scalar29MontMulCode 0x262 = some (.store .sw sp (9 : Fin 32) 0xC0, 2) := by decide
theorem smm_at_264 : fetchRel scalar29MontMulCode 0x264 = some (.store .sw sp (28 : Fin 32) 0xD4, 2) := by decide
theorem smm_at_266 : fetchRel scalar29MontMulCode 0x266 = some (.alu .mulhu a3 (9 : Fin 32) (28 : Fin 32), 4) := by decide
theorem smm_at_26a : fetchRel scalar29MontMulCode 0x26A = some (.alu .mul (8 : Fin 32) (7 : Fin 32) (21 : Fin 32), 4) := by decide
theorem smm_at_26e : fetchRel scalar29MontMulCode 0x26E = some (.alu .mul a5 (9 : Fin 32) (28 : Fin 32), 4) := by decide
theorem smm_at_272 : fetchRel scalar29MontMulCode 0x272 = some (.alu .add a4 a4 (23 : Fin 32), 2) := by decide
theorem smm_at_274 : fetchRel scalar29MontMulCode 0x274 = some (.alu .add (31 : Fin 32) (31 : Fin 32) a1, 2) := by decide
theorem smm_at_276 : fetchRel scalar29MontMulCode 0x276 = some (.alu .sltu a1 (31 : Fin 32) a1, 4) := by decide
theorem smm_at_27a : fetchRel scalar29MontMulCode 0x27A = some (.alu .add (22 : Fin 32) (31 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_27e : fetchRel scalar29MontMulCode 0x27E = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_280 : fetchRel scalar29MontMulCode 0x280 = some (.alu .sltu a4 (22 : Fin 32) (31 : Fin 32), 4) := by decide
theorem smm_at_284 : fetchRel scalar29MontMulCode 0x284 = some (.alu .sub a0 a0 (18 : Fin 32), 4) := by decide
theorem smm_at_288 : fetchRel scalar29MontMulCode 0x288 = some (.store .sw sp a0 0x128, 4) := by decide
theorem smm_at_28c : fetchRel scalar29MontMulCode 0x28C = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_28e : fetchRel scalar29MontMulCode 0x28E = some (.alu .add a3 a3 a2, 2) := by decide
theorem smm_at_290 : fetchRel scalar29MontMulCode 0x290 = some (.load .lw (20 : Fin 32) (19 : Fin 32) 0x20, 4) := by decide
theorem smm_at_294 : fetchRel scalar29MontMulCode 0x294 = some (.alu .add (27 : Fin 32) a5 (8 : Fin 32), 4) := by decide
theorem smm_at_298 : fetchRel scalar29MontMulCode 0x298 = some (.load .lw (17 : Fin 32) sp 0x100, 4) := by decide
theorem smm_at_29c : fetchRel scalar29MontMulCode 0x29C = some (.alu .mul (9 : Fin 32) (30 : Fin 32) (17 : Fin 32), 4) := by decide
theorem smm_at_2a0 : fetchRel scalar29MontMulCode 0x2A0 = some (.alu .add (28 : Fin 32) x0 (30 : Fin 32), 2) := by decide
theorem smm_at_2a2 : fetchRel scalar29MontMulCode 0x2A2 = some (.store .sw sp (30 : Fin 32) 0x9C, 2) := by decide
theorem smm_at_2a4 : fetchRel scalar29MontMulCode 0x2A4 = some (.alu .mulhu (31 : Fin 32) (5 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_2a8 : fetchRel scalar29MontMulCode 0x2A8 = some (.alu .mulhu (24 : Fin 32) ra (6 : Fin 32), 4) := by decide
theorem smm_at_2ac : fetchRel scalar29MontMulCode 0x2AC = some (.alu .mul (23 : Fin 32) (5 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_2b0 : fetchRel scalar29MontMulCode 0x2B0 = some (.alu .mul a0 ra (6 : Fin 32), 4) := by decide
theorem smm_at_2b4 : fetchRel scalar29MontMulCode 0x2B4 = some (.alu .add (7 : Fin 32) x0 (6 : Fin 32), 2) := by decide
theorem smm_at_2b6 : fetchRel scalar29MontMulCode 0x2B6 = some (.alu .sltu a4 (27 : Fin 32) a5, 4) := by decide
theorem smm_at_2ba : fetchRel scalar29MontMulCode 0x2BA = some (.store .sw sp a6 0xA8, 2) := by decide
theorem smm_at_2bc : fetchRel scalar29MontMulCode 0x2BC = some (.alu .mulhu a2 (20 : Fin 32) a6, 4) := by decide
theorem smm_at_2c0 : fetchRel scalar29MontMulCode 0x2C0 = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_2c2 : fetchRel scalar29MontMulCode 0x2C2 = some (.alu .sltu a4 (27 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_2c6 : fetchRel scalar29MontMulCode 0x2C6 = some (.alu .sub a3 a3 a4, 2) := by decide
theorem smm_at_2c8 : fetchRel scalar29MontMulCode 0x2C8 = some (.alu .mul a5 (20 : Fin 32) a6, 4) := by decide
theorem smm_at_2cc : fetchRel scalar29MontMulCode 0x2CC = some (.alu .sub a3 a3 a1, 2) := by decide
theorem smm_at_2ce : fetchRel scalar29MontMulCode 0x2CE = some (.store .sw sp a3 0xCC, 2) := by decide
theorem smm_at_2d0 : fetchRel scalar29MontMulCode 0x2D0 = some (.lui a1 0x12548000, 4) := by decide
theorem smm_at_2d4 : fetchRel scalar29MontMulCode 0x2D4 = some (.alu .add (31 : Fin 32) (31 : Fin 32) (24 : Fin 32), 2) := by decide
theorem smm_at_2d6 : fetchRel scalar29MontMulCode 0x2D6 = some (.aluImm .add a6 a1 0xFFFFFE1B, 4) := by decide
theorem smm_at_2da : fetchRel scalar29MontMulCode 0x2DA = some (.alu .add a1 a0 (23 : Fin 32), 4) := by decide
theorem smm_at_2de : fetchRel scalar29MontMulCode 0x2DE = some (.alu .mul a4 (9 : Fin 32) a6, 4) := by decide
theorem smm_at_2e2 : fetchRel scalar29MontMulCode 0x2E2 = some (.store .sw sp a4 0xC4, 2) := by decide
theorem smm_at_2e4 : fetchRel scalar29MontMulCode 0x2E4 = some (.alu .add a2 a2 (31 : Fin 32), 2) := by decide
theorem smm_at_2e6 : fetchRel scalar29MontMulCode 0x2E6 = some (.alu .sltu a0 a1 a0, 4) := by decide
theorem smm_at_2ea : fetchRel scalar29MontMulCode 0x2EA = some (.alu .add a3 a2 a0, 4) := by decide
theorem smm_at_2ee : fetchRel scalar29MontMulCode 0x2EE = some (.load .lw (30 : Fin 32) (25 : Fin 32) 0x20, 4) := by decide
theorem smm_at_2f2 : fetchRel scalar29MontMulCode 0x2F2 = some (.alu .add (31 : Fin 32) a1 a5, 4) := by decide
theorem smm_at_2f6 : fetchRel scalar29MontMulCode 0x2F6 = some (.store .sw sp (29 : Fin 32) 0x90, 2) := by decide
theorem smm_at_2f8 : fetchRel scalar29MontMulCode 0x2F8 = some (.alu .mulhu (8 : Fin 32) (20 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_2fc : fetchRel scalar29MontMulCode 0x2FC = some (.alu .add (18 : Fin 32) x0 (5 : Fin 32), 2) := by decide
theorem smm_at_2fe : fetchRel scalar29MontMulCode 0x2FE = some (.alu .mulhu a5 ra (5 : Fin 32), 4) := by decide
theorem smm_at_302 : fetchRel scalar29MontMulCode 0x302 = some (.lui (23 : Fin 32) 0x20000000, 4) := by decide
theorem smm_at_306 : fetchRel scalar29MontMulCode 0x306 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem smm_at_308 : fetchRel scalar29MontMulCode 0x308 = some (.lui a2 0x1CF5D000, 4) := by decide
theorem smm_at_30c : fetchRel scalar29MontMulCode 0x30C = some (.aluImm .add (25 : Fin 32) a2 0x3ED, 4) := by decide
theorem smm_at_310 : fetchRel scalar29MontMulCode 0x310 = some (.alu .and (6 : Fin 32) a4 (23 : Fin 32), 4) := by decide
theorem smm_at_314 : fetchRel scalar29MontMulCode 0x314 = some (.alu .sltu a1 (31 : Fin 32) a1, 4) := by decide
theorem smm_at_318 : fetchRel scalar29MontMulCode 0x318 = some (.alu .mul a4 (6 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_31c : fetchRel scalar29MontMulCode 0x31C = some (.alu .mulhu (21 : Fin 32) (28 : Fin 32) (17 : Fin 32), 4) := by decide
theorem smm_at_320 : fetchRel scalar29MontMulCode 0x320 = some (.alu .mulhu (19 : Fin 32) (6 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_324 : fetchRel scalar29MontMulCode 0x324 = some (.alu .sub a0 (27 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_328 : fetchRel scalar29MontMulCode 0x328 = some (.store .sw sp a0 0xB0, 2) := by decide
theorem smm_at_32a : fetchRel scalar29MontMulCode 0x32A = some (.alu .add (22 : Fin 32) a3 a1, 4) := by decide
theorem smm_at_32e : fetchRel scalar29MontMulCode 0x32E = some (.alu .add (24 : Fin 32) (8 : Fin 32) a5, 4) := by decide
theorem smm_at_332 : fetchRel scalar29MontMulCode 0x332 = some (.lui (5 : Fin 32) 0x932000, 4) := by decide
theorem smm_at_336 : fetchRel scalar29MontMulCode 0x336 = some (.aluImm .add (27 : Fin 32) (5 : Fin 32) 0xFFFFF8D2, 4) := by decide
theorem smm_at_33a : fetchRel scalar29MontMulCode 0x33A = some (.store .sw sp (7 : Fin 32) 0x98, 2) := by decide
theorem smm_at_33c : fetchRel scalar29MontMulCode 0x33C = some (.alu .mulhu a3 (30 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_340 : fetchRel scalar29MontMulCode 0x340 = some (.alu .mul a5 (20 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_344 : fetchRel scalar29MontMulCode 0x344 = some (.alu .mul a1 ra (18 : Fin 32), 4) := by decide
theorem smm_at_348 : fetchRel scalar29MontMulCode 0x348 = some (.alu .add (8 : Fin 32) a4 (9 : Fin 32), 4) := by decide
theorem smm_at_34c : fetchRel scalar29MontMulCode 0x34C = some (.alu .add (29 : Fin 32) x0 (9 : Fin 32), 2) := by decide
theorem smm_at_34e : fetchRel scalar29MontMulCode 0x34E = some (.store .sw sp (9 : Fin 32) 0xA4, 2) := by decide
theorem smm_at_350 : fetchRel scalar29MontMulCode 0x350 = some (.alu .mul (17 : Fin 32) (6 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_354 : fetchRel scalar29MontMulCode 0x354 = some (.alu .add (19 : Fin 32) (19 : Fin 32) (21 : Fin 32), 2) := by decide
theorem smm_at_356 : fetchRel scalar29MontMulCode 0x356 = some (.alu .sltu a4 (8 : Fin 32) a4, 4) := by decide
theorem smm_at_35a : fetchRel scalar29MontMulCode 0x35A = some (.alu .add (28 : Fin 32) (19 : Fin 32) a4, 4) := by decide
theorem smm_at_35e : fetchRel scalar29MontMulCode 0x35E = some (.aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x1D, 2) := by decide
theorem smm_at_360 : fetchRel scalar29MontMulCode 0x360 = some (.store .sw sp (26 : Fin 32) 0x94, 2) := by decide
theorem smm_at_362 : fetchRel scalar29MontMulCode 0x362 = some (.alu .mulhu a4 (30 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_366 : fetchRel scalar29MontMulCode 0x366 = some (.aluImm .sll (19 : Fin 32) (28 : Fin 32) 0x3, 4) := by decide
theorem smm_at_36a : fetchRel scalar29MontMulCode 0x36A = some (.alu .add a3 a3 (24 : Fin 32), 2) := by decide
theorem smm_at_36c : fetchRel scalar29MontMulCode 0x36C = some (.alu .or (8 : Fin 32) (8 : Fin 32) (19 : Fin 32), 4) := by decide
theorem smm_at_370 : fetchRel scalar29MontMulCode 0x370 = some (.alu .mul (19 : Fin 32) (30 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_374 : fetchRel scalar29MontMulCode 0x374 = some (.alu .mul (24 : Fin 32) (30 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_378 : fetchRel scalar29MontMulCode 0x378 = some (.alu .add a1 a1 a5, 2) := by decide
theorem smm_at_37a : fetchRel scalar29MontMulCode 0x37A = some (.load .lw a2 sp 0x10C, 4) := by decide
theorem smm_at_37e : fetchRel scalar29MontMulCode 0x37E = some (.alu .add a2 a2 (17 : Fin 32), 2) := by decide
theorem smm_at_380 : fetchRel scalar29MontMulCode 0x380 = some (.alu .sltu a5 a1 a5, 4) := by decide
theorem smm_at_384 : fetchRel scalar29MontMulCode 0x384 = some (.alu .add a0 a2 (8 : Fin 32), 4) := by decide
theorem smm_at_388 : fetchRel scalar29MontMulCode 0x388 = some (.alu .mulhu (8 : Fin 32) (6 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_38c : fetchRel scalar29MontMulCode 0x38C = some (.alu .add (5 : Fin 32) x0 a6, 2) := by decide
theorem smm_at_38e : fetchRel scalar29MontMulCode 0x38E = some (.alu .mul (9 : Fin 32) a0 a6, 4) := by decide
theorem smm_at_392 : fetchRel scalar29MontMulCode 0x392 = some (.store .sw sp (9 : Fin 32) 0xD0, 2) := by decide
theorem smm_at_394 : fetchRel scalar29MontMulCode 0x394 = some (.alu .add a4 a4 (22 : Fin 32), 2) := by decide
theorem smm_at_396 : fetchRel scalar29MontMulCode 0x396 = some (.alu .add (22 : Fin 32) a3 a5, 4) := by decide
theorem smm_at_39a : fetchRel scalar29MontMulCode 0x39A = some (.alu .mulhu a6 (20 : Fin 32) ra, 4) := by decide
theorem smm_at_39e : fetchRel scalar29MontMulCode 0x39E = some (.alu .mulhu a5 (30 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_3a2 : fetchRel scalar29MontMulCode 0x3A2 = some (.alu .add (19 : Fin 32) (19 : Fin 32) (31 : Fin 32), 2) := by decide
theorem smm_at_3a4 : fetchRel scalar29MontMulCode 0x3A4 = some (.store .sw sp (19 : Fin 32) 0xBC, 2) := by decide
theorem smm_at_3a6 : fetchRel scalar29MontMulCode 0x3A6 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a1, 2) := by decide
theorem smm_at_3a8 : fetchRel scalar29MontMulCode 0x3A8 = some (.store .sw sp (24 : Fin 32) 0xDC, 2) := by decide
theorem smm_at_3aa : fetchRel scalar29MontMulCode 0x3AA = some (.alu .sltu a3 (19 : Fin 32) (31 : Fin 32), 4) := by decide
theorem smm_at_3ae : fetchRel scalar29MontMulCode 0x3AE = some (.alu .sltu a1 (24 : Fin 32) a1, 4) := by decide
theorem smm_at_3b2 : fetchRel scalar29MontMulCode 0x3B2 = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_3b4 : fetchRel scalar29MontMulCode 0x3B4 = some (.store .sw sp a3 0xB4, 2) := by decide
theorem smm_at_3b6 : fetchRel scalar29MontMulCode 0x3B6 = some (.alu .add a1 a1 (22 : Fin 32), 2) := by decide
theorem smm_at_3b8 : fetchRel scalar29MontMulCode 0x3B8 = some (.store .sw sp a1 0xD8, 2) := by decide
theorem smm_at_3ba : fetchRel scalar29MontMulCode 0x3BA = some (.load .lw a1 sp 0x110, 4) := by decide
theorem smm_at_3be : fetchRel scalar29MontMulCode 0x3BE = some (.alu .add (8 : Fin 32) (8 : Fin 32) a1, 2) := by decide
theorem smm_at_3c0 : fetchRel scalar29MontMulCode 0x3C0 = some (.store .sw sp (23 : Fin 32) 0x130, 4) := by decide
theorem smm_at_3c4 : fetchRel scalar29MontMulCode 0x3C4 = some (.alu .and (22 : Fin 32) (9 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_3c8 : fetchRel scalar29MontMulCode 0x3C8 = some (.alu .sltu a1 a2 (17 : Fin 32), 4) := by decide
theorem smm_at_3cc : fetchRel scalar29MontMulCode 0x3CC = some (.alu .mul a3 (22 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_3d0 : fetchRel scalar29MontMulCode 0x3D0 = some (.alu .add a6 a6 a5, 2) := by decide
theorem smm_at_3d2 : fetchRel scalar29MontMulCode 0x3D2 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem smm_at_3d4 : fetchRel scalar29MontMulCode 0x3D4 = some (.alu .mulhu (17 : Fin 32) (22 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_3d8 : fetchRel scalar29MontMulCode 0x3D8 = some (.lui (8 : Fin 32) 0x1DE73000, 4) := by decide
theorem smm_at_3dc : fetchRel scalar29MontMulCode 0x3DC = some (.aluImm .srl a5 (28 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_3e0 : fetchRel scalar29MontMulCode 0x3E0 = some (.aluImm .add (26 : Fin 32) (8 : Fin 32) 0x596, 4) := by decide
theorem smm_at_3e4 : fetchRel scalar29MontMulCode 0x3E4 = some (.alu .add a1 a1 a5, 2) := by decide
theorem smm_at_3e6 : fetchRel scalar29MontMulCode 0x3E6 = some (.alu .mul (31 : Fin 32) (6 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_3ea : fetchRel scalar29MontMulCode 0x3EA = some (.alu .sltu a2 a0 a2, 4) := by decide
theorem smm_at_3ee : fetchRel scalar29MontMulCode 0x3EE = some (.alu .mul (8 : Fin 32) (22 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_3f2 : fetchRel scalar29MontMulCode 0x3F2 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_3f4 : fetchRel scalar29MontMulCode 0x3F4 = some (.alu .add a0 a0 a3, 2) := by decide
theorem smm_at_3f6 : fetchRel scalar29MontMulCode 0x3F6 = some (.alu .mul a2 (20 : Fin 32) ra, 4) := by decide
theorem smm_at_3fa : fetchRel scalar29MontMulCode 0x3FA = some (.alu .mul a4 (30 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_3fe : fetchRel scalar29MontMulCode 0x3FE = some (.alu .add (19 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem smm_at_400 : fetchRel scalar29MontMulCode 0x400 = some (.alu .add a1 a1 (17 : Fin 32), 2) := by decide
theorem smm_at_402 : fetchRel scalar29MontMulCode 0x402 = some (.alu .sltu a3 a0 a3, 4) := by decide
theorem smm_at_406 : fetchRel scalar29MontMulCode 0x406 = some (.alu .add (7 : Fin 32) a1 a3, 4) := by decide
theorem smm_at_40a : fetchRel scalar29MontMulCode 0x40A = some (.aluImm .srl a0 a0 0x1D, 2) := by decide
theorem smm_at_40c : fetchRel scalar29MontMulCode 0x40C = some (.aluImm .sll a3 (7 : Fin 32) 0x3, 4) := by decide
theorem smm_at_410 : fetchRel scalar29MontMulCode 0x410 = some (.load .lw a5 sp 0x11C, 4) := by decide
theorem smm_at_414 : fetchRel scalar29MontMulCode 0x414 = some (.alu .add a5 a5 (31 : Fin 32), 2) := by decide
theorem smm_at_416 : fetchRel scalar29MontMulCode 0x416 = some (.alu .or a0 a0 a3, 2) := by decide
theorem smm_at_418 : fetchRel scalar29MontMulCode 0x418 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem smm_at_41a : fetchRel scalar29MontMulCode 0x41A = some (.alu .add a0 a0 (8 : Fin 32), 2) := by decide
theorem smm_at_41c : fetchRel scalar29MontMulCode 0x41C = some (.alu .mulhu (17 : Fin 32) (6 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_420 : fetchRel scalar29MontMulCode 0x420 = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_422 : fetchRel scalar29MontMulCode 0x422 = some (.store .sw sp a2 0xF4, 2) := by decide
theorem smm_at_424 : fetchRel scalar29MontMulCode 0x424 = some (.alu .mul a1 a0 (5 : Fin 32), 4) := by decide
theorem smm_at_428 : fetchRel scalar29MontMulCode 0x428 = some (.alu .add (28 : Fin 32) x0 (5 : Fin 32), 2) := by decide
theorem smm_at_42a : fetchRel scalar29MontMulCode 0x42A = some (.store .sw sp (5 : Fin 32) 0x8, 2) := by decide
theorem smm_at_42c : fetchRel scalar29MontMulCode 0x42C = some (.store .sw sp a1 0xF0, 2) := by decide
theorem smm_at_42e : fetchRel scalar29MontMulCode 0x42E = some (.alu .sltu a3 a2 a4, 4) := by decide
theorem smm_at_432 : fetchRel scalar29MontMulCode 0x432 = some (.alu .mulhu a4 (22 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_436 : fetchRel scalar29MontMulCode 0x436 = some (.alu .add a3 a3 a6, 2) := by decide
theorem smm_at_438 : fetchRel scalar29MontMulCode 0x438 = some (.store .sw sp a3 0xE4, 2) := by decide
theorem smm_at_43a : fetchRel scalar29MontMulCode 0x43A = some (.load .lw a2 sp 0x134, 4) := by decide
theorem smm_at_43e : fetchRel scalar29MontMulCode 0x43E = some (.alu .sltu a2 a2 (29 : Fin 32), 4) := by decide
theorem smm_at_442 : fetchRel scalar29MontMulCode 0x442 = some (.alu .add a2 a2 (21 : Fin 32), 2) := by decide
theorem smm_at_444 : fetchRel scalar29MontMulCode 0x444 = some (.store .sw sp a2 0x8C, 2) := by decide
theorem smm_at_446 : fetchRel scalar29MontMulCode 0x446 = some (.load .lw (24 : Fin 32) sp 0xA8, 2) := by decide
theorem smm_at_448 : fetchRel scalar29MontMulCode 0x448 = some (.load .lw a2 sp 0x100, 4) := by decide
theorem smm_at_44c : fetchRel scalar29MontMulCode 0x44C = some (.alu .add (24 : Fin 32) (24 : Fin 32) a2, 2) := by decide
theorem smm_at_44e : fetchRel scalar29MontMulCode 0x44E = some (.load .lw (21 : Fin 32) sp 0xE0, 2) := by decide
theorem smm_at_450 : fetchRel scalar29MontMulCode 0x450 = some (.load .lw a2 sp 0x90, 2) := by decide
theorem smm_at_452 : fetchRel scalar29MontMulCode 0x452 = some (.alu .add (21 : Fin 32) (21 : Fin 32) a2, 2) := by decide
theorem smm_at_454 : fetchRel scalar29MontMulCode 0x454 = some (.load .lw a2 sp 0xAC, 2) := by decide
theorem smm_at_456 : fetchRel scalar29MontMulCode 0x456 = some (.alu .add a2 a2 ra, 2) := by decide
theorem smm_at_458 : fetchRel scalar29MontMulCode 0x458 = some (.store .sw sp a2 0xA8, 2) := by decide
theorem smm_at_45a : fetchRel scalar29MontMulCode 0x45A = some (.load .lw a2 sp 0x118, 4) := by decide
theorem smm_at_45e : fetchRel scalar29MontMulCode 0x45E = some (.alu .add a3 (17 : Fin 32) a2, 4) := by decide
theorem smm_at_462 : fetchRel scalar29MontMulCode 0x462 = some (.alu .sltu (9 : Fin 32) a5 (31 : Fin 32), 4) := by decide
theorem smm_at_466 : fetchRel scalar29MontMulCode 0x466 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem smm_at_468 : fetchRel scalar29MontMulCode 0x468 = some (.alu .and (5 : Fin 32) a1 (23 : Fin 32), 4) := by decide
theorem smm_at_46c : fetchRel scalar29MontMulCode 0x46C = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_46e : fetchRel scalar29MontMulCode 0x46E = some (.alu .mulhu a4 (5 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_472 : fetchRel scalar29MontMulCode 0x472 = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem smm_at_476 : fetchRel scalar29MontMulCode 0x476 = some (.alu .mul (9 : Fin 32) (5 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_47a : fetchRel scalar29MontMulCode 0x47A = some (.alu .add a3 a3 a5, 2) := by decide
theorem smm_at_47c : fetchRel scalar29MontMulCode 0x47C = some (.aluImm .srl a1 (7 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_480 : fetchRel scalar29MontMulCode 0x480 = some (.load .lw (29 : Fin 32) sp 0x9C, 2) := by decide
theorem smm_at_482 : fetchRel scalar29MontMulCode 0x482 = some (.load .lw a2 sp 0x94, 2) := by decide
theorem smm_at_484 : fetchRel scalar29MontMulCode 0x484 = some (.alu .add (29 : Fin 32) (29 : Fin 32) a2, 2) := by decide
theorem smm_at_486 : fetchRel scalar29MontMulCode 0x486 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_488 : fetchRel scalar29MontMulCode 0x488 = some (.alu .sltu a3 a0 (8 : Fin 32), 4) := by decide
theorem smm_at_48c : fetchRel scalar29MontMulCode 0x48C = some (.lui a5 0x1DF3C000, 4) := by decide
theorem smm_at_490 : fetchRel scalar29MontMulCode 0x490 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_492 : fetchRel scalar29MontMulCode 0x492 = some (.aluImm .add (18 : Fin 32) a5 0xFFFFFD45, 4) := by decide
theorem smm_at_496 : fetchRel scalar29MontMulCode 0x496 = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_498 : fetchRel scalar29MontMulCode 0x498 = some (.alu .mul a4 (6 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_49c : fetchRel scalar29MontMulCode 0x49C = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem smm_at_49e : fetchRel scalar29MontMulCode 0x49E = some (.alu .mul a5 (22 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_4a2 : fetchRel scalar29MontMulCode 0x4A2 = some (.alu .sltu (9 : Fin 32) a0 (9 : Fin 32), 4) := by decide
theorem smm_at_4a6 : fetchRel scalar29MontMulCode 0x4A6 = some (.alu .mul (8 : Fin 32) (5 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_4aa : fetchRel scalar29MontMulCode 0x4AA = some (.load .lw (7 : Fin 32) sp 0xEC, 2) := by decide
theorem smm_at_4ac : fetchRel scalar29MontMulCode 0x4AC = some (.load .lw a2 sp 0x98, 2) := by decide
theorem smm_at_4ae : fetchRel scalar29MontMulCode 0x4AE = some (.alu .add (7 : Fin 32) (7 : Fin 32) a2, 2) := by decide
theorem smm_at_4b0 : fetchRel scalar29MontMulCode 0x4B0 = some (.alu .add (31 : Fin 32) a1 (9 : Fin 32), 4) := by decide
theorem smm_at_4b4 : fetchRel scalar29MontMulCode 0x4B4 = some (.aluImm .srl a0 a0 0x1D, 2) := by decide
theorem smm_at_4b6 : fetchRel scalar29MontMulCode 0x4B6 = some (.aluImm .sll a1 (31 : Fin 32) 0x3, 4) := by decide
theorem smm_at_4ba : fetchRel scalar29MontMulCode 0x4BA = some (.load .lw ra sp 0xE8, 2) := by decide
theorem smm_at_4bc : fetchRel scalar29MontMulCode 0x4BC = some (.alu .add ra ra (19 : Fin 32), 2) := by decide
theorem smm_at_4be : fetchRel scalar29MontMulCode 0x4BE = some (.alu .or a0 a0 a1, 2) := by decide
theorem smm_at_4c0 : fetchRel scalar29MontMulCode 0x4C0 = some (.load .lw a3 sp 0x108, 4) := by decide
theorem smm_at_4c4 : fetchRel scalar29MontMulCode 0x4C4 = some (.alu .add a4 a4 a3, 2) := by decide
theorem smm_at_4c6 : fetchRel scalar29MontMulCode 0x4C6 = some (.alu .mulhu (19 : Fin 32) (6 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_4ca : fetchRel scalar29MontMulCode 0x4CA = some (.load .lw (23 : Fin 32) sp 0xC8, 2) := by decide
theorem smm_at_4cc : fetchRel scalar29MontMulCode 0x4CC = some (.alu .add (23 : Fin 32) (23 : Fin 32) (30 : Fin 32), 2) := by decide
theorem smm_at_4ce : fetchRel scalar29MontMulCode 0x4CE = some (.alu .add a5 a5 a4, 2) := by decide
theorem smm_at_4d0 : fetchRel scalar29MontMulCode 0x4D0 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem smm_at_4d2 : fetchRel scalar29MontMulCode 0x4D2 = some (.alu .mulhu (17 : Fin 32) (22 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_4d6 : fetchRel scalar29MontMulCode 0x4D6 = some (.alu .add a6 (8 : Fin 32) a0, 4) := by decide
theorem smm_at_4da : fetchRel scalar29MontMulCode 0x4DA = some (.alu .mulhu a1 (29 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_4de : fetchRel scalar29MontMulCode 0x4DE = some (.alu .mulhu a2 (5 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_4e2 : fetchRel scalar29MontMulCode 0x4E2 = some (.alu .mul a0 a6 (28 : Fin 32), 4) := by decide
theorem smm_at_4e6 : fetchRel scalar29MontMulCode 0x4E6 = some (.store .sw sp a0 0xEC, 2) := by decide
theorem smm_at_4e8 : fetchRel scalar29MontMulCode 0x4E8 = some (.alu .mulhu (9 : Fin 32) (30 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_4ec : fetchRel scalar29MontMulCode 0x4EC = some (.store .sw sp (9 : Fin 32) 0xE8, 2) := by decide
theorem smm_at_4ee : fetchRel scalar29MontMulCode 0x4EE = some (.alu .mul (9 : Fin 32) (30 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_4f2 : fetchRel scalar29MontMulCode 0x4F2 = some (.store .sw sp (9 : Fin 32) 0xE0, 2) := by decide
theorem smm_at_4f4 : fetchRel scalar29MontMulCode 0x4F4 = some (.load .lw (9 : Fin 32) sp 0x114, 4) := by decide
theorem smm_at_4f8 : fetchRel scalar29MontMulCode 0x4F8 = some (.alu .add (19 : Fin 32) (19 : Fin 32) (9 : Fin 32), 2) := by decide
theorem smm_at_4fa : fetchRel scalar29MontMulCode 0x4FA = some (.alu .sltu (30 : Fin 32) a4 a3, 4) := by decide
theorem smm_at_4fe : fetchRel scalar29MontMulCode 0x4FE = some (.load .lw a3 sp 0xD4, 2) := by decide
theorem smm_at_500 : fetchRel scalar29MontMulCode 0x500 = some (.alu .add (20 : Fin 32) (20 : Fin 32) a3, 2) := by decide
theorem smm_at_502 : fetchRel scalar29MontMulCode 0x502 = some (.alu .add (30 : Fin 32) (30 : Fin 32) (19 : Fin 32), 2) := by decide
theorem smm_at_504 : fetchRel scalar29MontMulCode 0x504 = some (.alu .add (30 : Fin 32) (30 : Fin 32) (17 : Fin 32), 2) := by decide
theorem smm_at_506 : fetchRel scalar29MontMulCode 0x506 = some (.alu .sltu a4 a5 a4, 4) := by decide
theorem smm_at_50a : fetchRel scalar29MontMulCode 0x50A = some (.load .lw a3 sp 0x8C, 2) := by decide
theorem smm_at_50c : fetchRel scalar29MontMulCode 0x50C = some (.alu .sub (17 : Fin 32) a3 a1, 4) := by decide
theorem smm_at_510 : fetchRel scalar29MontMulCode 0x510 = some (.alu .add a4 a4 (30 : Fin 32), 2) := by decide
theorem smm_at_512 : fetchRel scalar29MontMulCode 0x512 = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_514 : fetchRel scalar29MontMulCode 0x514 = some (.load .lw (19 : Fin 32) sp 0x130, 4) := by decide
theorem smm_at_518 : fetchRel scalar29MontMulCode 0x518 = some (.alu .and a1 a0 (19 : Fin 32), 4) := by decide
theorem smm_at_51c : fetchRel scalar29MontMulCode 0x51C = some (.alu .mul a4 a1 (25 : Fin 32), 4) := by decide
theorem smm_at_520 : fetchRel scalar29MontMulCode 0x520 = some (.alu .mulhu (30 : Fin 32) a1 (25 : Fin 32), 4) := by decide
theorem smm_at_524 : fetchRel scalar29MontMulCode 0x524 = some (.alu .add (28 : Fin 32) x0 (25 : Fin 32), 2) := by decide
theorem smm_at_526 : fetchRel scalar29MontMulCode 0x526 = some (.alu .add (25 : Fin 32) x0 a1, 2) := by decide
theorem smm_at_528 : fetchRel scalar29MontMulCode 0x528 = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem smm_at_52c : fetchRel scalar29MontMulCode 0x52C = some (.aluImm .add a0 x0 0x14D, 4) := by decide
theorem smm_at_530 : fetchRel scalar29MontMulCode 0x530 = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_532 : fetchRel scalar29MontMulCode 0x532 = some (.store .sw sp (6 : Fin 32) 0x80, 2) := by decide
theorem smm_at_534 : fetchRel scalar29MontMulCode 0x534 = some (.alu .mul a5 (6 : Fin 32) a0, 4) := by decide
theorem smm_at_538 : fetchRel scalar29MontMulCode 0x538 = some (.aluImm .srl a1 (31 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_53c : fetchRel scalar29MontMulCode 0x53C = some (.alu .mulhu (9 : Fin 32) (6 : Fin 32) a0, 4) := by decide
theorem smm_at_540 : fetchRel scalar29MontMulCode 0x540 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_542 : fetchRel scalar29MontMulCode 0x542 = some (.alu .sltu a2 a6 (8 : Fin 32), 4) := by decide
theorem smm_at_546 : fetchRel scalar29MontMulCode 0x546 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_548 : fetchRel scalar29MontMulCode 0x548 = some (.alu .mulhu a2 (22 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_54c : fetchRel scalar29MontMulCode 0x54C = some (.alu .add a1 a1 (30 : Fin 32), 2) := by decide
theorem smm_at_54e : fetchRel scalar29MontMulCode 0x54E = some (.alu .add a0 a4 a6, 4) := by decide
theorem smm_at_552 : fetchRel scalar29MontMulCode 0x552 = some (.alu .sltu a4 a0 a4, 4) := by decide
theorem smm_at_556 : fetchRel scalar29MontMulCode 0x556 = some (.alu .mul (8 : Fin 32) (22 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_55a : fetchRel scalar29MontMulCode 0x55A = some (.alu .add (30 : Fin 32) a1 a4, 4) := by decide
theorem smm_at_55e : fetchRel scalar29MontMulCode 0x55E = some (.load .lw a1 sp 0x104, 4) := by decide
theorem smm_at_562 : fetchRel scalar29MontMulCode 0x562 = some (.alu .add a5 a5 a1, 2) := by decide
theorem smm_at_564 : fetchRel scalar29MontMulCode 0x564 = some (.load .lw a3 sp 0x120, 4) := by decide
theorem smm_at_568 : fetchRel scalar29MontMulCode 0x568 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem smm_at_56a : fetchRel scalar29MontMulCode 0x56A = some (.alu .sltu a4 a5 a1, 4) := by decide
theorem smm_at_56e : fetchRel scalar29MontMulCode 0x56E = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem smm_at_570 : fetchRel scalar29MontMulCode 0x570 = some (.alu .mul (9 : Fin 32) (5 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_574 : fetchRel scalar29MontMulCode 0x574 = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_576 : fetchRel scalar29MontMulCode 0x576 = some (.alu .mulhu a4 (5 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_57a : fetchRel scalar29MontMulCode 0x57A = some (.aluImm .srl a0 a0 0x1D, 2) := by decide
theorem smm_at_57c : fetchRel scalar29MontMulCode 0x57C = some (.alu .mul (31 : Fin 32) (25 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_580 : fetchRel scalar29MontMulCode 0x580 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a5, 2) := by decide
theorem smm_at_582 : fetchRel scalar29MontMulCode 0x582 = some (.alu .mulhu a1 (25 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_586 : fetchRel scalar29MontMulCode 0x586 = some (.alu .add (6 : Fin 32) x0 (25 : Fin 32), 2) := by decide
theorem smm_at_588 : fetchRel scalar29MontMulCode 0x588 = some (.alu .add (25 : Fin 32) x0 (27 : Fin 32), 2) := by decide
theorem smm_at_58a : fetchRel scalar29MontMulCode 0x58A = some (.alu .sltu a5 (8 : Fin 32) a5, 4) := by decide
theorem smm_at_58e : fetchRel scalar29MontMulCode 0x58E = some (.aluImm .sll a3 (30 : Fin 32) 0x3, 4) := by decide
theorem smm_at_592 : fetchRel scalar29MontMulCode 0x592 = some (.alu .or a0 a0 a3, 2) := by decide
theorem smm_at_594 : fetchRel scalar29MontMulCode 0x594 = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_596 : fetchRel scalar29MontMulCode 0x596 = some (.alu .add (9 : Fin 32) (9 : Fin 32) (8 : Fin 32), 2) := by decide
theorem smm_at_598 : fetchRel scalar29MontMulCode 0x598 = some (.alu .mul a3 (29 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_59c : fetchRel scalar29MontMulCode 0x59C = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_59e : fetchRel scalar29MontMulCode 0x59E = some (.alu .sltu a4 (9 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_5a2 : fetchRel scalar29MontMulCode 0x5A2 = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_5a4 : fetchRel scalar29MontMulCode 0x5A4 = some (.alu .add (31 : Fin 32) (31 : Fin 32) (9 : Fin 32), 2) := by decide
theorem smm_at_5a6 : fetchRel scalar29MontMulCode 0x5A6 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_5a8 : fetchRel scalar29MontMulCode 0x5A8 = some (.alu .sltu a2 (31 : Fin 32) (9 : Fin 32), 4) := by decide
theorem smm_at_5ac : fetchRel scalar29MontMulCode 0x5AC = some (.alu .add (27 : Fin 32) a1 a2, 4) := by decide
theorem smm_at_5b0 : fetchRel scalar29MontMulCode 0x5B0 = some (.alu .add a0 a0 (31 : Fin 32), 2) := by decide
theorem smm_at_5b2 : fetchRel scalar29MontMulCode 0x5B2 = some (.load .lw a2 sp 0x134, 4) := by decide
theorem smm_at_5b6 : fetchRel scalar29MontMulCode 0x5B6 = some (.load .lw a1 sp 0xA4, 2) := by decide
theorem smm_at_5b8 : fetchRel scalar29MontMulCode 0x5B8 = some (.alu .sub a2 a2 a1, 2) := by decide
theorem smm_at_5ba : fetchRel scalar29MontMulCode 0x5BA = some (.load .lw a6 sp 0x8, 2) := by decide
theorem smm_at_5bc : fetchRel scalar29MontMulCode 0x5BC = some (.alu .mul (8 : Fin 32) a0 a6, 4) := by decide
theorem smm_at_5c0 : fetchRel scalar29MontMulCode 0x5C0 = some (.store .sw sp (8 : Fin 32) 0xD4, 2) := by decide
theorem smm_at_5c2 : fetchRel scalar29MontMulCode 0x5C2 = some (.load .lw a4 sp 0x124, 4) := by decide
theorem smm_at_5c6 : fetchRel scalar29MontMulCode 0x5C6 = some (.alu .sub a4 a4 (17 : Fin 32), 4) := by decide
theorem smm_at_5ca : fetchRel scalar29MontMulCode 0x5CA = some (.alu .add a3 a3 a2, 2) := by decide
theorem smm_at_5cc : fetchRel scalar29MontMulCode 0x5CC = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem smm_at_5d0 : fetchRel scalar29MontMulCode 0x5D0 = some (.store .sw sp (22 : Fin 32) 0xA0, 2) := by decide
theorem smm_at_5d2 : fetchRel scalar29MontMulCode 0x5D2 = some (.aluImm .add a1 x0 0x14D, 4) := by decide
theorem smm_at_5d6 : fetchRel scalar29MontMulCode 0x5D6 = some (.alu .mul a5 (22 : Fin 32) a1, 4) := by decide
theorem smm_at_5da : fetchRel scalar29MontMulCode 0x5DA = some (.aluImm .srl (9 : Fin 32) (30 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_5de : fetchRel scalar29MontMulCode 0x5DE = some (.alu .mulhu (17 : Fin 32) (22 : Fin 32) a1, 4) := by decide
theorem smm_at_5e2 : fetchRel scalar29MontMulCode 0x5E2 = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_5e4 : fetchRel scalar29MontMulCode 0x5E4 = some (.alu .add a1 (27 : Fin 32) (9 : Fin 32), 4) := by decide
theorem smm_at_5e8 : fetchRel scalar29MontMulCode 0x5E8 = some (.alu .sltu a4 a0 (31 : Fin 32), 4) := by decide
theorem smm_at_5ec : fetchRel scalar29MontMulCode 0x5EC = some (.alu .mul (9 : Fin 32) (5 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_5f0 : fetchRel scalar29MontMulCode 0x5F0 = some (.alu .and (22 : Fin 32) (8 : Fin 32) (19 : Fin 32), 4) := by decide
theorem smm_at_5f4 : fetchRel scalar29MontMulCode 0x5F4 = some (.alu .mulhu (30 : Fin 32) (5 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_5f8 : fetchRel scalar29MontMulCode 0x5F8 = some (.alu .add (31 : Fin 32) a1 a4, 4) := by decide
theorem smm_at_5fc : fetchRel scalar29MontMulCode 0x5FC = some (.alu .mulhu a4 (22 : Fin 32) (28 : Fin 32), 4) := by decide
theorem smm_at_600 : fetchRel scalar29MontMulCode 0x600 = some (.alu .add a5 a5 a3, 2) := by decide
theorem smm_at_602 : fetchRel scalar29MontMulCode 0x602 = some (.alu .mul a1 (22 : Fin 32) (28 : Fin 32), 4) := by decide
theorem smm_at_606 : fetchRel scalar29MontMulCode 0x606 = some (.alu .add a2 a2 (17 : Fin 32), 2) := by decide
theorem smm_at_608 : fetchRel scalar29MontMulCode 0x608 = some (.alu .sltu a3 a5 a3, 4) := by decide
theorem smm_at_60c : fetchRel scalar29MontMulCode 0x60C = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_60e : fetchRel scalar29MontMulCode 0x60E = some (.store .sw sp (26 : Fin 32) 0xFC, 2) := by decide
theorem smm_at_610 : fetchRel scalar29MontMulCode 0x610 = some (.store .sw sp (6 : Fin 32) 0x100, 4) := by decide
theorem smm_at_614 : fetchRel scalar29MontMulCode 0x614 = some (.alu .mulhu (27 : Fin 32) (6 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_618 : fetchRel scalar29MontMulCode 0x618 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a5, 2) := by decide
theorem smm_at_61a : fetchRel scalar29MontMulCode 0x61A = some (.alu .mul (8 : Fin 32) (6 : Fin 32) (26 : Fin 32), 4) := by decide
theorem smm_at_61e : fetchRel scalar29MontMulCode 0x61E = some (.alu .add a2 a2 (30 : Fin 32), 2) := by decide
theorem smm_at_620 : fetchRel scalar29MontMulCode 0x620 = some (.alu .sltu a5 (9 : Fin 32) a5, 4) := by decide
theorem smm_at_624 : fetchRel scalar29MontMulCode 0x624 = some (.alu .add a4 a4 (31 : Fin 32), 2) := by decide
theorem smm_at_626 : fetchRel scalar29MontMulCode 0x626 = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_628 : fetchRel scalar29MontMulCode 0x628 = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_62a : fetchRel scalar29MontMulCode 0x62A = some (.alu .mulhu a5 (22 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_62e : fetchRel scalar29MontMulCode 0x62E = some (.alu .sltu a1 a0 a1, 4) := by decide
theorem smm_at_632 : fetchRel scalar29MontMulCode 0x632 = some (.alu .mul (30 : Fin 32) (22 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_636 : fetchRel scalar29MontMulCode 0x636 = some (.alu .add a3 a4 a1, 4) := by decide
theorem smm_at_63a : fetchRel scalar29MontMulCode 0x63A = some (.alu .add a2 a2 (27 : Fin 32), 2) := by decide
theorem smm_at_63c : fetchRel scalar29MontMulCode 0x63C = some (.aluImm .srl a0 a0 0x1D, 2) := by decide
theorem smm_at_63e : fetchRel scalar29MontMulCode 0x63E = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem smm_at_640 : fetchRel scalar29MontMulCode 0x640 = some (.alu .sltu a4 (8 : Fin 32) (9 : Fin 32), 4) := by decide
theorem smm_at_644 : fetchRel scalar29MontMulCode 0x644 = some (.aluImm .sll a1 a3 0x3, 4) := by decide
theorem smm_at_648 : fetchRel scalar29MontMulCode 0x648 = some (.alu .or a0 a0 a1, 2) := by decide
theorem smm_at_64a : fetchRel scalar29MontMulCode 0x64A = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_64c : fetchRel scalar29MontMulCode 0x64C = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_64e : fetchRel scalar29MontMulCode 0x64E = some (.alu .mul a1 (7 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_652 : fetchRel scalar29MontMulCode 0x652 = some (.alu .add (30 : Fin 32) (30 : Fin 32) (8 : Fin 32), 2) := by decide
theorem smm_at_654 : fetchRel scalar29MontMulCode 0x654 = some (.alu .mulhu a4 (7 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_658 : fetchRel scalar29MontMulCode 0x658 = some (.alu .sltu a5 (30 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_65c : fetchRel scalar29MontMulCode 0x65C = some (.alu .add (17 : Fin 32) (30 : Fin 32) a0, 4) := by decide
theorem smm_at_660 : fetchRel scalar29MontMulCode 0x660 = some (.alu .mul (9 : Fin 32) (21 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_664 : fetchRel scalar29MontMulCode 0x664 = some (.alu .mul a0 (17 : Fin 32) a6, 4) := by decide
theorem smm_at_668 : fetchRel scalar29MontMulCode 0x668 = some (.store .sw sp a0 0xC8, 2) := by decide
theorem smm_at_66a : fetchRel scalar29MontMulCode 0x66A = some (.alu .add (6 : Fin 32) x0 a6, 2) := by decide
theorem smm_at_66c : fetchRel scalar29MontMulCode 0x66C = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_66e : fetchRel scalar29MontMulCode 0x66E = some (.aluImm .srl a3 a3 0x1D, 2) := by decide
theorem smm_at_670 : fetchRel scalar29MontMulCode 0x670 = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_672 : fetchRel scalar29MontMulCode 0x672 = some (.alu .sltu a3 (17 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_676 : fetchRel scalar29MontMulCode 0x676 = some (.alu .mulhu (30 : Fin 32) (21 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_67a : fetchRel scalar29MontMulCode 0x67A = some (.load .lw a5 sp 0x10C, 4) := by decide
theorem smm_at_67e : fetchRel scalar29MontMulCode 0x67E = some (.alu .sltu (8 : Fin 32) a1 a5, 4) := by decide
theorem smm_at_682 : fetchRel scalar29MontMulCode 0x682 = some (.alu .add (31 : Fin 32) a2 a3, 4) := by decide
theorem smm_at_686 : fetchRel scalar29MontMulCode 0x686 = some (.alu .sub a4 a4 (8 : Fin 32), 2) := by decide
theorem smm_at_688 : fetchRel scalar29MontMulCode 0x688 = some (.load .lw a2 sp 0x110, 4) := by decide
theorem smm_at_68c : fetchRel scalar29MontMulCode 0x68C = some (.alu .sub a4 a4 a2, 2) := by decide
theorem smm_at_68e : fetchRel scalar29MontMulCode 0x68E = some (.alu .sub a1 a1 a5, 2) := by decide
theorem smm_at_690 : fetchRel scalar29MontMulCode 0x690 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a1, 2) := by decide
theorem smm_at_692 : fetchRel scalar29MontMulCode 0x692 = some (.alu .and (26 : Fin 32) a0 (19 : Fin 32), 4) := by decide
theorem smm_at_696 : fetchRel scalar29MontMulCode 0x696 = some (.store .sw sp (28 : Fin 32) 0x10, 2) := by decide
theorem smm_at_698 : fetchRel scalar29MontMulCode 0x698 = some (.alu .mulhu (8 : Fin 32) (26 : Fin 32) (28 : Fin 32), 4) := by decide
theorem smm_at_69c : fetchRel scalar29MontMulCode 0x69C = some (.store .sw sp (5 : Fin 32) 0xAC, 2) := by decide
theorem smm_at_69e : fetchRel scalar29MontMulCode 0x69E = some (.aluImm .add a3 x0 0x14D, 4) := by decide
theorem smm_at_6a2 : fetchRel scalar29MontMulCode 0x6A2 = some (.alu .mulhu a5 (5 : Fin 32) a3, 4) := by decide
theorem smm_at_6a6 : fetchRel scalar29MontMulCode 0x6A6 = some (.alu .mul a2 (26 : Fin 32) (28 : Fin 32), 4) := by decide
theorem smm_at_6aa : fetchRel scalar29MontMulCode 0x6AA = some (.alu .mul (27 : Fin 32) (5 : Fin 32) a3, 4) := by decide
theorem smm_at_6ae : fetchRel scalar29MontMulCode 0x6AE = some (.alu .add (30 : Fin 32) (30 : Fin 32) a4, 2) := by decide
theorem smm_at_6b0 : fetchRel scalar29MontMulCode 0x6B0 = some (.load .lw a4 sp 0x128, 4) := by decide
theorem smm_at_6b4 : fetchRel scalar29MontMulCode 0x6B4 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem smm_at_6b6 : fetchRel scalar29MontMulCode 0x6B6 = some (.alu .sltu a1 (9 : Fin 32) a1, 4) := by decide
theorem smm_at_6ba : fetchRel scalar29MontMulCode 0x6BA = some (.alu .sltu (9 : Fin 32) a4 (9 : Fin 32), 4) := by decide
theorem smm_at_6be : fetchRel scalar29MontMulCode 0x6BE = some (.alu .add a1 a1 (30 : Fin 32), 2) := by decide
theorem smm_at_6c0 : fetchRel scalar29MontMulCode 0x6C0 = some (.load .lw a3 sp 0x12C, 4) := by decide
theorem smm_at_6c4 : fetchRel scalar29MontMulCode 0x6C4 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem smm_at_6c6 : fetchRel scalar29MontMulCode 0x6C6 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem smm_at_6c8 : fetchRel scalar29MontMulCode 0x6C8 = some (.store .sw sp (18 : Fin 32) 0x14, 2) := by decide
theorem smm_at_6ca : fetchRel scalar29MontMulCode 0x6CA = some (.load .lw (19 : Fin 32) sp 0x100, 4) := by decide
theorem smm_at_6ce : fetchRel scalar29MontMulCode 0x6CE = some (.alu .mulhu (9 : Fin 32) (19 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_6d2 : fetchRel scalar29MontMulCode 0x6D2 = some (.alu .add (31 : Fin 32) (31 : Fin 32) (8 : Fin 32), 2) := by decide
theorem smm_at_6d4 : fetchRel scalar29MontMulCode 0x6D4 = some (.alu .add a5 a5 a1, 2) := by decide
theorem smm_at_6d6 : fetchRel scalar29MontMulCode 0x6D6 = some (.alu .add a0 a2 (17 : Fin 32), 4) := by decide
theorem smm_at_6da : fetchRel scalar29MontMulCode 0x6DA = some (.alu .add (27 : Fin 32) (27 : Fin 32) a4, 2) := by decide
theorem smm_at_6dc : fetchRel scalar29MontMulCode 0x6DC = some (.alu .sltu a1 a0 a2, 4) := by decide
theorem smm_at_6e0 : fetchRel scalar29MontMulCode 0x6E0 = some (.alu .sltu a2 (27 : Fin 32) a4, 4) := by decide
theorem smm_at_6e4 : fetchRel scalar29MontMulCode 0x6E4 = some (.alu .add (31 : Fin 32) (31 : Fin 32) a1, 2) := by decide
theorem smm_at_6e6 : fetchRel scalar29MontMulCode 0x6E6 = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_6e8 : fetchRel scalar29MontMulCode 0x6E8 = some (.aluImm .srl a0 a0 0x1D, 2) := by decide
theorem smm_at_6ea : fetchRel scalar29MontMulCode 0x6EA = some (.aluImm .sll a4 (31 : Fin 32) 0x3, 4) := by decide
theorem smm_at_6ee : fetchRel scalar29MontMulCode 0x6EE = some (.alu .or a3 a0 a4, 4) := by decide
theorem smm_at_6f2 : fetchRel scalar29MontMulCode 0x6F2 = some (.alu .add (30 : Fin 32) a2 (9 : Fin 32), 4) := by decide
theorem smm_at_6f6 : fetchRel scalar29MontMulCode 0x6F6 = some (.alu .mulhu a0 ra (24 : Fin 32), 4) := by decide
theorem smm_at_6fa : fetchRel scalar29MontMulCode 0x6FA = some (.store .sw sp a0 0x20, 2) := by decide
theorem smm_at_6fc : fetchRel scalar29MontMulCode 0x6FC = some (.alu .mul a0 ra (24 : Fin 32), 4) := by decide
theorem smm_at_700 : fetchRel scalar29MontMulCode 0x700 = some (.store .sw sp a0 0x1C, 2) := by decide
theorem smm_at_702 : fetchRel scalar29MontMulCode 0x702 = some (.alu .mul a0 (20 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_706 : fetchRel scalar29MontMulCode 0x706 = some (.store .sw sp a0 0x48, 2) := by decide
theorem smm_at_708 : fetchRel scalar29MontMulCode 0x708 = some (.alu .mulhu a0 (20 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_70c : fetchRel scalar29MontMulCode 0x70C = some (.store .sw sp a0 0x40, 2) := by decide
theorem smm_at_70e : fetchRel scalar29MontMulCode 0x70E = some (.load .lw a0 sp 0xB8, 2) := by decide
theorem smm_at_710 : fetchRel scalar29MontMulCode 0x710 = some (.alu .mul a1 (24 : Fin 32) a0, 4) := by decide
theorem smm_at_714 : fetchRel scalar29MontMulCode 0x714 = some (.store .sw sp a1 0x60, 2) := by decide
theorem smm_at_716 : fetchRel scalar29MontMulCode 0x716 = some (.alu .mulhu a1 (24 : Fin 32) a0, 4) := by decide
theorem smm_at_71a : fetchRel scalar29MontMulCode 0x71A = some (.store .sw sp a1 0x58, 2) := by decide
theorem smm_at_71c : fetchRel scalar29MontMulCode 0x71C = some (.load .lw (9 : Fin 32) sp 0xA8, 2) := by decide
theorem smm_at_71e : fetchRel scalar29MontMulCode 0x71E = some (.alu .mul a1 (9 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_722 : fetchRel scalar29MontMulCode 0x722 = some (.store .sw sp a1 0x24, 2) := by decide
theorem smm_at_724 : fetchRel scalar29MontMulCode 0x724 = some (.alu .mulhu a1 (9 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_728 : fetchRel scalar29MontMulCode 0x728 = some (.store .sw sp a1 0x18, 2) := by decide
theorem smm_at_72a : fetchRel scalar29MontMulCode 0x72A = some (.alu .mul a1 (23 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_72e : fetchRel scalar29MontMulCode 0x72E = some (.store .sw sp a1 0x44, 2) := by decide
theorem smm_at_730 : fetchRel scalar29MontMulCode 0x730 = some (.alu .mulhu a1 (23 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_734 : fetchRel scalar29MontMulCode 0x734 = some (.store .sw sp a1 0x4C, 2) := by decide
theorem smm_at_736 : fetchRel scalar29MontMulCode 0x736 = some (.load .lw a1 sp 0xC0, 2) := by decide
theorem smm_at_738 : fetchRel scalar29MontMulCode 0x738 = some (.alu .mul a2 (29 : Fin 32) a1, 4) := by decide
theorem smm_at_73c : fetchRel scalar29MontMulCode 0x73C = some (.store .sw sp a2 0x54, 2) := by decide
theorem smm_at_73e : fetchRel scalar29MontMulCode 0x73E = some (.alu .mulhu a2 (29 : Fin 32) a1, 4) := by decide
theorem smm_at_742 : fetchRel scalar29MontMulCode 0x742 = some (.store .sw sp a2 0x50, 2) := by decide
theorem smm_at_744 : fetchRel scalar29MontMulCode 0x744 = some (.alu .mul a6 (21 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_748 : fetchRel scalar29MontMulCode 0x748 = some (.alu .mulhu a2 (21 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_74c : fetchRel scalar29MontMulCode 0x74C = some (.store .sw sp a2 0xC, 2) := by decide
theorem smm_at_74e : fetchRel scalar29MontMulCode 0x74E = some (.alu .mul a2 ra (21 : Fin 32), 4) := by decide
theorem smm_at_752 : fetchRel scalar29MontMulCode 0x752 = some (.store .sw sp a2 0x3C, 2) := by decide
theorem smm_at_754 : fetchRel scalar29MontMulCode 0x754 = some (.alu .mulhu a2 ra (21 : Fin 32), 4) := by decide
theorem smm_at_758 : fetchRel scalar29MontMulCode 0x758 = some (.store .sw sp a2 0x38, 2) := by decide
theorem smm_at_75a : fetchRel scalar29MontMulCode 0x75A = some (.alu .mul a2 (20 : Fin 32) (21 : Fin 32), 4) := by decide
theorem smm_at_75e : fetchRel scalar29MontMulCode 0x75E = some (.store .sw sp a2 0x70, 2) := by decide
theorem smm_at_760 : fetchRel scalar29MontMulCode 0x760 = some (.alu .mulhu a2 (20 : Fin 32) (21 : Fin 32), 4) := by decide
theorem smm_at_764 : fetchRel scalar29MontMulCode 0x764 = some (.store .sw sp a2 0x6C, 2) := by decide
theorem smm_at_766 : fetchRel scalar29MontMulCode 0x766 = some (.alu .mul a2 (21 : Fin 32) a0, 4) := by decide
theorem smm_at_76a : fetchRel scalar29MontMulCode 0x76A = some (.store .sw sp a2 0x98, 2) := by decide
theorem smm_at_76c : fetchRel scalar29MontMulCode 0x76C = some (.alu .mulhu a2 (21 : Fin 32) a0, 4) := by decide
theorem smm_at_770 : fetchRel scalar29MontMulCode 0x770 = some (.store .sw sp a2 0x94, 2) := by decide
theorem smm_at_772 : fetchRel scalar29MontMulCode 0x772 = some (.alu .mulhu a2 (9 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_776 : fetchRel scalar29MontMulCode 0x776 = some (.store .sw sp a2 0x34, 2) := by decide
theorem smm_at_778 : fetchRel scalar29MontMulCode 0x778 = some (.alu .mul a2 (9 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_77c : fetchRel scalar29MontMulCode 0x77C = some (.store .sw sp a2 0x30, 2) := by decide
theorem smm_at_77e : fetchRel scalar29MontMulCode 0x77E = some (.alu .mul a2 (23 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_782 : fetchRel scalar29MontMulCode 0x782 = some (.store .sw sp a2 0x74, 2) := by decide
theorem smm_at_784 : fetchRel scalar29MontMulCode 0x784 = some (.alu .mul a2 (19 : Fin 32) (18 : Fin 32), 4) := by decide
theorem smm_at_788 : fetchRel scalar29MontMulCode 0x788 = some (.alu .mulhu a4 (23 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_78c : fetchRel scalar29MontMulCode 0x78C = some (.store .sw sp a4 0x68, 2) := by decide
theorem smm_at_78e : fetchRel scalar29MontMulCode 0x78E = some (.load .lw (8 : Fin 32) sp 0xFC, 2) := by decide
theorem smm_at_790 : fetchRel scalar29MontMulCode 0x790 = some (.alu .mul a4 (22 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_794 : fetchRel scalar29MontMulCode 0x794 = some (.alu .mul a5 (7 : Fin 32) a1, 4) := by decide
theorem smm_at_798 : fetchRel scalar29MontMulCode 0x798 = some (.store .sw sp a5 0x84, 2) := by decide
theorem smm_at_79a : fetchRel scalar29MontMulCode 0x79A = some (.alu .mulhu a5 (7 : Fin 32) a1, 4) := by decide
theorem smm_at_79e : fetchRel scalar29MontMulCode 0x79E = some (.store .sw sp a5 0x88, 2) := by decide
theorem smm_at_7a0 : fetchRel scalar29MontMulCode 0x7A0 = some (.alu .mulhu a5 (9 : Fin 32) ra, 4) := by decide
theorem smm_at_7a4 : fetchRel scalar29MontMulCode 0x7A4 = some (.store .sw sp a5 0x64, 2) := by decide
theorem smm_at_7a6 : fetchRel scalar29MontMulCode 0x7A6 = some (.alu .add (29 : Fin 32) x0 (25 : Fin 32), 2) := by decide
theorem smm_at_7a8 : fetchRel scalar29MontMulCode 0x7A8 = some (.alu .mul (17 : Fin 32) (26 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_7ac : fetchRel scalar29MontMulCode 0x7AC = some (.alu .mul a5 (9 : Fin 32) ra, 4) := by decide
theorem smm_at_7b0 : fetchRel scalar29MontMulCode 0x7B0 = some (.store .sw sp a5 0x5C, 2) := by decide
theorem smm_at_7b2 : fetchRel scalar29MontMulCode 0x7B2 = some (.alu .mul a5 (20 : Fin 32) (9 : Fin 32), 4) := by decide
theorem smm_at_7b6 : fetchRel scalar29MontMulCode 0x7B6 = some (.store .sw sp a5 0x90, 2) := by decide
theorem smm_at_7b8 : fetchRel scalar29MontMulCode 0x7B8 = some (.alu .mulhu a5 (20 : Fin 32) (9 : Fin 32), 4) := by decide
theorem smm_at_7bc : fetchRel scalar29MontMulCode 0x7BC = some (.store .sw sp a5 0x8C, 2) := by decide
theorem smm_at_7be : fetchRel scalar29MontMulCode 0x7BE = some (.alu .mul a5 (9 : Fin 32) a0, 4) := by decide
theorem smm_at_7c2 : fetchRel scalar29MontMulCode 0x7C2 = some (.store .sw sp a5 0x10C, 4) := by decide
theorem smm_at_7c6 : fetchRel scalar29MontMulCode 0x7C6 = some (.alu .mulhu a5 (9 : Fin 32) a0, 4) := by decide
theorem smm_at_7ca : fetchRel scalar29MontMulCode 0x7CA = some (.store .sw sp a5 0xA8, 2) := by decide
theorem smm_at_7cc : fetchRel scalar29MontMulCode 0x7CC = some (.alu .add a2 a2 (27 : Fin 32), 2) := by decide
theorem smm_at_7ce : fetchRel scalar29MontMulCode 0x7CE = some (.alu .add (9 : Fin 32) a2 a4, 4) := by decide
theorem smm_at_7d2 : fetchRel scalar29MontMulCode 0x7D2 = some (.alu .mul a4 a1 a0, 4) := by decide
theorem smm_at_7d6 : fetchRel scalar29MontMulCode 0x7D6 = some (.store .sw sp a4 0x2C, 2) := by decide
theorem smm_at_7d8 : fetchRel scalar29MontMulCode 0x7D8 = some (.alu .mulhu a4 a1 a0, 4) := by decide
theorem smm_at_7dc : fetchRel scalar29MontMulCode 0x7DC = some (.store .sw sp a4 0x28, 2) := by decide
theorem smm_at_7de : fetchRel scalar29MontMulCode 0x7DE = some (.alu .mul (7 : Fin 32) (23 : Fin 32) a0, 4) := by decide
theorem smm_at_7e2 : fetchRel scalar29MontMulCode 0x7E2 = some (.alu .mulhu (5 : Fin 32) (23 : Fin 32) a0, 4) := by decide
theorem smm_at_7e6 : fetchRel scalar29MontMulCode 0x7E6 = some (.alu .add (17 : Fin 32) (17 : Fin 32) (9 : Fin 32), 2) := by decide
theorem smm_at_7e8 : fetchRel scalar29MontMulCode 0x7E8 = some (.alu .add (28 : Fin 32) (17 : Fin 32) a3, 4) := by decide
theorem smm_at_7ec : fetchRel scalar29MontMulCode 0x7EC = some (.alu .mulhu a0 (23 : Fin 32) ra, 4) := by decide
theorem smm_at_7f0 : fetchRel scalar29MontMulCode 0x7F0 = some (.store .sw sp a0 0x7C, 2) := by decide
theorem smm_at_7f2 : fetchRel scalar29MontMulCode 0x7F2 = some (.alu .mul a0 (23 : Fin 32) ra, 4) := by decide
theorem smm_at_7f6 : fetchRel scalar29MontMulCode 0x7F6 = some (.store .sw sp a0 0x78, 2) := by decide
theorem smm_at_7f8 : fetchRel scalar29MontMulCode 0x7F8 = some (.alu .mulhu a3 (22 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_7fc : fetchRel scalar29MontMulCode 0x7FC = some (.alu .mul a0 (23 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_800 : fetchRel scalar29MontMulCode 0x800 = some (.store .sw sp a0 0xB8, 2) := by decide
theorem smm_at_802 : fetchRel scalar29MontMulCode 0x802 = some (.alu .mulhu a0 (20 : Fin 32) a1, 4) := by decide
theorem smm_at_806 : fetchRel scalar29MontMulCode 0x806 = some (.alu .mulhu (21 : Fin 32) (26 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_80a : fetchRel scalar29MontMulCode 0x80A = some (.alu .mul a4 (28 : Fin 32) (6 : Fin 32), 4) := by decide
theorem smm_at_80e : fetchRel scalar29MontMulCode 0x80E = some (.store .sw sp a4 0x110, 4) := by decide
theorem smm_at_812 : fetchRel scalar29MontMulCode 0x812 = some (.alu .mulhu (8 : Fin 32) (23 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_816 : fetchRel scalar29MontMulCode 0x816 = some (.store .sw sp (8 : Fin 32) 0xA4, 2) := by decide
theorem smm_at_818 : fetchRel scalar29MontMulCode 0x818 = some (.alu .mul (25 : Fin 32) (20 : Fin 32) a1, 4) := by decide
theorem smm_at_81c : fetchRel scalar29MontMulCode 0x81C = some (.alu .sltu (8 : Fin 32) a2 (27 : Fin 32), 4) := by decide
theorem smm_at_820 : fetchRel scalar29MontMulCode 0x820 = some (.alu .mul a5 ra a1, 4) := by decide
theorem smm_at_824 : fetchRel scalar29MontMulCode 0x824 = some (.store .sw sp a5 0x9C, 2) := by decide
theorem smm_at_826 : fetchRel scalar29MontMulCode 0x826 = some (.alu .mulhu a1 ra a1, 4) := by decide
theorem smm_at_82a : fetchRel scalar29MontMulCode 0x82A = some (.store .sw sp a1 0xC0, 2) := by decide
theorem smm_at_82c : fetchRel scalar29MontMulCode 0x82C = some (.alu .add (30 : Fin 32) (30 : Fin 32) (8 : Fin 32), 2) := by decide
theorem smm_at_82e : fetchRel scalar29MontMulCode 0x82E = some (.alu .add a3 a3 (30 : Fin 32), 2) := by decide
theorem smm_at_830 : fetchRel scalar29MontMulCode 0x830 = some (.alu .sltu a2 (9 : Fin 32) a2, 4) := by decide
theorem smm_at_834 : fetchRel scalar29MontMulCode 0x834 = some (.alu .add a0 a0 (5 : Fin 32), 2) := by decide
theorem smm_at_836 : fetchRel scalar29MontMulCode 0x836 = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_838 : fetchRel scalar29MontMulCode 0x838 = some (.alu .add a1 a2 (21 : Fin 32), 4) := by decide
theorem smm_at_83c : fetchRel scalar29MontMulCode 0x83C = some (.load .lw (24 : Fin 32) sp 0x130, 4) := by decide
theorem smm_at_840 : fetchRel scalar29MontMulCode 0x840 = some (.alu .and (18 : Fin 32) a4 (24 : Fin 32), 4) := by decide
theorem smm_at_844 : fetchRel scalar29MontMulCode 0x844 = some (.alu .add (25 : Fin 32) (25 : Fin 32) (7 : Fin 32), 2) := by decide
theorem smm_at_846 : fetchRel scalar29MontMulCode 0x846 = some (.load .lw ra sp 0x10, 2) := by decide
theorem smm_at_848 : fetchRel scalar29MontMulCode 0x848 = some (.alu .mulhu a3 (18 : Fin 32) ra, 4) := by decide
theorem smm_at_84c : fetchRel scalar29MontMulCode 0x84C = some (.alu .sltu a4 (25 : Fin 32) (7 : Fin 32), 4) := by decide
theorem smm_at_850 : fetchRel scalar29MontMulCode 0x850 = some (.alu .sltu a5 (17 : Fin 32) (9 : Fin 32), 4) := by decide
theorem smm_at_854 : fetchRel scalar29MontMulCode 0x854 = some (.alu .add (5 : Fin 32) a0 a4, 4) := by decide
theorem smm_at_858 : fetchRel scalar29MontMulCode 0x858 = some (.alu .add a1 a1 a5, 2) := by decide
theorem smm_at_85a : fetchRel scalar29MontMulCode 0x85A = some (.aluImm .srl a0 (31 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_85e : fetchRel scalar29MontMulCode 0x85E = some (.alu .mul a4 (18 : Fin 32) ra, 4) := by decide
theorem smm_at_862 : fetchRel scalar29MontMulCode 0x862 = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_864 : fetchRel scalar29MontMulCode 0x864 = some (.alu .sltu a1 (28 : Fin 32) (17 : Fin 32), 4) := by decide
theorem smm_at_868 : fetchRel scalar29MontMulCode 0x868 = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_86a : fetchRel scalar29MontMulCode 0x86A = some (.load .lw a2 sp 0x11C, 4) := by decide
theorem smm_at_86e : fetchRel scalar29MontMulCode 0x86E = some (.alu .sltu a1 a6 a2, 4) := by decide
theorem smm_at_872 : fetchRel scalar29MontMulCode 0x872 = some (.alu .add a0 a0 a3, 2) := by decide
theorem smm_at_874 : fetchRel scalar29MontMulCode 0x874 = some (.load .lw a3 sp 0xC, 2) := by decide
theorem smm_at_876 : fetchRel scalar29MontMulCode 0x876 = some (.alu .sub a1 a3 a1, 4) := by decide
theorem smm_at_87a : fetchRel scalar29MontMulCode 0x87A = some (.load .lw a3 sp 0x118, 4) := by decide
theorem smm_at_87e : fetchRel scalar29MontMulCode 0x87E = some (.alu .sub a1 a1 a3, 2) := by decide
theorem smm_at_880 : fetchRel scalar29MontMulCode 0x880 = some (.alu .sub a3 a6 a2, 4) := by decide
theorem smm_at_884 : fetchRel scalar29MontMulCode 0x884 = some (.load .lw a2 sp 0x20, 2) := by decide
theorem smm_at_886 : fetchRel scalar29MontMulCode 0x886 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_888 : fetchRel scalar29MontMulCode 0x888 = some (.load .lw a5 sp 0x1C, 2) := by decide
theorem smm_at_88a : fetchRel scalar29MontMulCode 0x88A = some (.alu .add a5 a5 a3, 2) := by decide
theorem smm_at_88c : fetchRel scalar29MontMulCode 0x88C = some (.alu .add (28 : Fin 32) (28 : Fin 32) a4, 2) := by decide
theorem smm_at_88e : fetchRel scalar29MontMulCode 0x88E = some (.alu .sltu a3 a5 a3, 4) := by decide
theorem smm_at_892 : fetchRel scalar29MontMulCode 0x892 = some (.load .lw a2 sp 0x18, 2) := by decide
theorem smm_at_894 : fetchRel scalar29MontMulCode 0x894 = some (.alu .add a3 a3 a2, 2) := by decide
theorem smm_at_896 : fetchRel scalar29MontMulCode 0x896 = some (.alu .sltu a4 (28 : Fin 32) a4, 4) := by decide
theorem smm_at_89a : fetchRel scalar29MontMulCode 0x89A = some (.alu .add a6 a0 a4, 4) := by decide
theorem smm_at_89e : fetchRel scalar29MontMulCode 0x89E = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_8a0 : fetchRel scalar29MontMulCode 0x8A0 = some (.load .lw a3 sp 0x24, 2) := by decide
theorem smm_at_8a2 : fetchRel scalar29MontMulCode 0x8A2 = some (.alu .add a3 a3 a5, 2) := by decide
theorem smm_at_8a4 : fetchRel scalar29MontMulCode 0x8A4 = some (.aluImm .add a0 x0 0x14D, 4) := by decide
theorem smm_at_8a8 : fetchRel scalar29MontMulCode 0x8A8 = some (.alu .mulhu a4 (19 : Fin 32) a0, 4) := by decide
theorem smm_at_8ac : fetchRel scalar29MontMulCode 0x8AC = some (.alu .sltu a5 a3 a5, 4) := by decide
theorem smm_at_8b0 : fetchRel scalar29MontMulCode 0x8B0 = some (.alu .mul a2 (19 : Fin 32) a0, 4) := by decide
theorem smm_at_8b4 : fetchRel scalar29MontMulCode 0x8B4 = some (.aluImm .add (27 : Fin 32) x0 0x14D, 4) := by decide
theorem smm_at_8b8 : fetchRel scalar29MontMulCode 0x8B8 = some (.load .lw (7 : Fin 32) sp 0xCC, 2) := by decide
theorem smm_at_8ba : fetchRel scalar29MontMulCode 0x8BA = some (.alu .add a5 a5 (7 : Fin 32), 2) := by decide
theorem smm_at_8bc : fetchRel scalar29MontMulCode 0x8BC = some (.load .lw (30 : Fin 32) sp 0xB0, 2) := by decide
theorem smm_at_8be : fetchRel scalar29MontMulCode 0x8BE = some (.alu .add (9 : Fin 32) a3 (30 : Fin 32), 4) := by decide
theorem smm_at_8c2 : fetchRel scalar29MontMulCode 0x8C2 = some (.alu .add a1 a1 a5, 2) := by decide
theorem smm_at_8c4 : fetchRel scalar29MontMulCode 0x8C4 = some (.alu .sltu a3 (9 : Fin 32) a3, 4) := by decide
theorem smm_at_8c8 : fetchRel scalar29MontMulCode 0x8C8 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_8ca : fetchRel scalar29MontMulCode 0x8CA = some (.load .lw (23 : Fin 32) sp 0x14, 2) := by decide
theorem smm_at_8cc : fetchRel scalar29MontMulCode 0x8CC = some (.alu .mul a3 (22 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_8d0 : fetchRel scalar29MontMulCode 0x8D0 = some (.alu .mulhu a5 (22 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_8d4 : fetchRel scalar29MontMulCode 0x8D4 = some (.alu .add (21 : Fin 32) x0 (22 : Fin 32), 2) := by decide
theorem smm_at_8d6 : fetchRel scalar29MontMulCode 0x8D6 = some (.load .lw (22 : Fin 32) sp 0xFC, 2) := by decide
theorem smm_at_8d8 : fetchRel scalar29MontMulCode 0x8D8 = some (.alu .mul (8 : Fin 32) (26 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_8dc : fetchRel scalar29MontMulCode 0x8DC = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_8de : fetchRel scalar29MontMulCode 0x8DE = some (.alu .add (20 : Fin 32) x0 (29 : Fin 32), 2) := by decide
theorem smm_at_8e0 : fetchRel scalar29MontMulCode 0x8E0 = some (.alu .mul (17 : Fin 32) (18 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_8e4 : fetchRel scalar29MontMulCode 0x8E4 = some (.aluImm .srl a0 (28 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_8e8 : fetchRel scalar29MontMulCode 0x8E8 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem smm_at_8ea : fetchRel scalar29MontMulCode 0x8EA = some (.alu .sltu (9 : Fin 32) a2 (9 : Fin 32), 4) := by decide
theorem smm_at_8ee : fetchRel scalar29MontMulCode 0x8EE = some (.aluImm .sll a4 a6 0x3, 4) := by decide
theorem smm_at_8f2 : fetchRel scalar29MontMulCode 0x8F2 = some (.alu .or a0 a0 a4, 2) := by decide
theorem smm_at_8f4 : fetchRel scalar29MontMulCode 0x8F4 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem smm_at_8f6 : fetchRel scalar29MontMulCode 0x8F6 = some (.alu .add a3 a3 a2, 2) := by decide
theorem smm_at_8f8 : fetchRel scalar29MontMulCode 0x8F8 = some (.alu .mulhu (29 : Fin 32) (26 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_8fc : fetchRel scalar29MontMulCode 0x8FC = some (.alu .add a5 a5 a1, 2) := by decide
theorem smm_at_8fe : fetchRel scalar29MontMulCode 0x8FE = some (.alu .add (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem smm_at_900 : fetchRel scalar29MontMulCode 0x900 = some (.alu .add a1 (8 : Fin 32) (17 : Fin 32), 4) := by decide
theorem smm_at_904 : fetchRel scalar29MontMulCode 0x904 = some (.alu .mulhu (9 : Fin 32) (18 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_908 : fetchRel scalar29MontMulCode 0x908 = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem smm_at_90c : fetchRel scalar29MontMulCode 0x90C = some (.alu .add (28 : Fin 32) a1 a0, 4) := by decide
theorem smm_at_910 : fetchRel scalar29MontMulCode 0x910 = some (.alu .sltu a0 (25 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_914 : fetchRel scalar29MontMulCode 0x914 = some (.alu .add (31 : Fin 32) x0 (6 : Fin 32), 2) := by decide
theorem smm_at_916 : fetchRel scalar29MontMulCode 0x916 = some (.alu .mul a4 (28 : Fin 32) (6 : Fin 32), 4) := by decide
theorem smm_at_91a : fetchRel scalar29MontMulCode 0x91A = some (.store .sw sp a4 0x11C, 4) := by decide
theorem smm_at_91e : fetchRel scalar29MontMulCode 0x91E = some (.alu .sub a0 (5 : Fin 32) a0, 4) := by decide
theorem smm_at_922 : fetchRel scalar29MontMulCode 0x922 = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_924 : fetchRel scalar29MontMulCode 0x924 = some (.alu .add a2 a2 (29 : Fin 32), 2) := by decide
theorem smm_at_926 : fetchRel scalar29MontMulCode 0x926 = some (.alu .sltu a3 (8 : Fin 32) a3, 4) := by decide
theorem smm_at_92a : fetchRel scalar29MontMulCode 0x92A = some (.alu .sub a0 a0 (7 : Fin 32), 4) := by decide
theorem smm_at_92e : fetchRel scalar29MontMulCode 0x92E = some (.store .sw sp a0 0x118, 4) := by decide
theorem smm_at_932 : fetchRel scalar29MontMulCode 0x932 = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_934 : fetchRel scalar29MontMulCode 0x934 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem smm_at_936 : fetchRel scalar29MontMulCode 0x936 = some (.alu .sltu a0 a1 (8 : Fin 32), 4) := by decide
theorem smm_at_93a : fetchRel scalar29MontMulCode 0x93A = some (.alu .add a0 a0 a2, 2) := by decide
theorem smm_at_93c : fetchRel scalar29MontMulCode 0x93C = some (.aluImm .srl a2 a6 0x1D, 4) := by decide
theorem smm_at_940 : fetchRel scalar29MontMulCode 0x940 = some (.alu .add a0 a0 a2, 2) := by decide
theorem smm_at_942 : fetchRel scalar29MontMulCode 0x942 = some (.alu .and (5 : Fin 32) a4 (24 : Fin 32), 4) := by decide
theorem smm_at_946 : fetchRel scalar29MontMulCode 0x946 = some (.alu .sltu a1 (28 : Fin 32) a1, 4) := by decide
theorem smm_at_94a : fetchRel scalar29MontMulCode 0x94A = some (.alu .mulhu a2 (5 : Fin 32) ra, 4) := by decide
theorem smm_at_94e : fetchRel scalar29MontMulCode 0x94E = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_950 : fetchRel scalar29MontMulCode 0x950 = some (.load .lw a1 sp 0x80, 2) := by decide
theorem smm_at_952 : fetchRel scalar29MontMulCode 0x952 = some (.aluImm .srl a1 a1 0xC, 2) := by decide
theorem smm_at_954 : fetchRel scalar29MontMulCode 0x954 = some (.load .lw a3 sp 0x114, 4) := by decide
theorem smm_at_958 : fetchRel scalar29MontMulCode 0x958 = some (.alu .sub a1 a1 a3, 2) := by decide
theorem smm_at_95a : fetchRel scalar29MontMulCode 0x95A = some (.load .lw a3 sp 0xC4, 2) := by decide
theorem smm_at_95c : fetchRel scalar29MontMulCode 0x95C = some (.aluImm .sll a3 a3 0x14, 2) := by decide
theorem smm_at_95e : fetchRel scalar29MontMulCode 0x95E = some (.load .lw a5 sp 0x108, 4) := by decide
theorem smm_at_962 : fetchRel scalar29MontMulCode 0x962 = some (.alu .sltu a4 a3 a5, 4) := by decide
theorem smm_at_966 : fetchRel scalar29MontMulCode 0x966 = some (.alu .sub a3 a3 a5, 2) := by decide
theorem smm_at_968 : fetchRel scalar29MontMulCode 0x968 = some (.load .lw a5 sp 0x28, 2) := by decide
theorem smm_at_96a : fetchRel scalar29MontMulCode 0x96A = some (.alu .sub a4 a4 a5, 2) := by decide
theorem smm_at_96c : fetchRel scalar29MontMulCode 0x96C = some (.load .lw a5 sp 0x2C, 2) := by decide
theorem smm_at_96e : fetchRel scalar29MontMulCode 0x96E = some (.alu .add a5 a5 a3, 2) := by decide
theorem smm_at_970 : fetchRel scalar29MontMulCode 0x970 = some (.alu .sub a1 a1 a4, 2) := by decide
theorem smm_at_972 : fetchRel scalar29MontMulCode 0x972 = some (.alu .sltu a3 a5 a3, 4) := by decide
theorem smm_at_976 : fetchRel scalar29MontMulCode 0x976 = some (.alu .add a0 a0 a2, 2) := by decide
theorem smm_at_978 : fetchRel scalar29MontMulCode 0x978 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_97a : fetchRel scalar29MontMulCode 0x97A = some (.load .lw a2 sp 0x38, 2) := by decide
theorem smm_at_97c : fetchRel scalar29MontMulCode 0x97C = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_97e : fetchRel scalar29MontMulCode 0x97E = some (.load .lw a2 sp 0x3C, 2) := by decide
theorem smm_at_980 : fetchRel scalar29MontMulCode 0x980 = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_982 : fetchRel scalar29MontMulCode 0x982 = some (.alu .sltu a3 a2 a5, 4) := by decide
theorem smm_at_986 : fetchRel scalar29MontMulCode 0x986 = some (.load .lw a4 sp 0x30, 2) := by decide
theorem smm_at_988 : fetchRel scalar29MontMulCode 0x988 = some (.alu .add a4 a4 a2, 2) := by decide
theorem smm_at_98a : fetchRel scalar29MontMulCode 0x98A = some (.load .lw a5 sp 0x34, 2) := by decide
theorem smm_at_98c : fetchRel scalar29MontMulCode 0x98C = some (.alu .add a3 a3 a5, 2) := by decide
theorem smm_at_98e : fetchRel scalar29MontMulCode 0x98E = some (.alu .sltu a2 a4 a2, 4) := by decide
theorem smm_at_992 : fetchRel scalar29MontMulCode 0x992 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_994 : fetchRel scalar29MontMulCode 0x994 = some (.load .lw a3 sp 0x40, 2) := by decide
theorem smm_at_996 : fetchRel scalar29MontMulCode 0x996 = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_998 : fetchRel scalar29MontMulCode 0x998 = some (.load .lw a3 sp 0x48, 2) := by decide
theorem smm_at_99a : fetchRel scalar29MontMulCode 0x99A = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_99c : fetchRel scalar29MontMulCode 0x99C = some (.alu .mul a5 (5 : Fin 32) ra, 4) := by decide
theorem smm_at_9a0 : fetchRel scalar29MontMulCode 0x9A0 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_9a2 : fetchRel scalar29MontMulCode 0x9A2 = some (.alu .sltu (9 : Fin 32) a3 a4, 4) := by decide
theorem smm_at_9a6 : fetchRel scalar29MontMulCode 0x9A6 = some (.load .lw a4 sp 0x44, 2) := by decide
theorem smm_at_9a8 : fetchRel scalar29MontMulCode 0x9A8 = some (.alu .add a4 a4 a3, 2) := by decide
theorem smm_at_9aa : fetchRel scalar29MontMulCode 0x9AA = some (.alu .mulhu (8 : Fin 32) (21 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_9ae : fetchRel scalar29MontMulCode 0x9AE = some (.load .lw a2 sp 0x4C, 2) := by decide
theorem smm_at_9b0 : fetchRel scalar29MontMulCode 0x9B0 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem smm_at_9b2 : fetchRel scalar29MontMulCode 0x9B2 = some (.alu .sltu a3 a4 a3, 4) := by decide
theorem smm_at_9b6 : fetchRel scalar29MontMulCode 0x9B6 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_9b8 : fetchRel scalar29MontMulCode 0x9B8 = some (.load .lw (17 : Fin 32) sp 0xB4, 2) := by decide
theorem smm_at_9ba : fetchRel scalar29MontMulCode 0x9BA = some (.alu .sub a2 a3 (17 : Fin 32), 4) := by decide
theorem smm_at_9be : fetchRel scalar29MontMulCode 0x9BE = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_9c0 : fetchRel scalar29MontMulCode 0x9C0 = some (.alu .mul a2 (21 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_9c4 : fetchRel scalar29MontMulCode 0x9C4 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a5, 2) := by decide
theorem smm_at_9c6 : fetchRel scalar29MontMulCode 0x9C6 = some (.load .lw (29 : Fin 32) sp 0xBC, 2) := by decide
theorem smm_at_9c8 : fetchRel scalar29MontMulCode 0x9C8 = some (.alu .sltu a3 a4 (29 : Fin 32), 4) := by decide
theorem smm_at_9cc : fetchRel scalar29MontMulCode 0x9CC = some (.alu .sub a1 a1 a3, 2) := by decide
theorem smm_at_9ce : fetchRel scalar29MontMulCode 0x9CE = some (.alu .sltu a5 (28 : Fin 32) a5, 4) := by decide
theorem smm_at_9d2 : fetchRel scalar29MontMulCode 0x9D2 = some (.alu .add a6 a0 a5, 4) := by decide
theorem smm_at_9d6 : fetchRel scalar29MontMulCode 0x9D6 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem smm_at_9d8 : fetchRel scalar29MontMulCode 0x9D8 = some (.aluImm .srl a0 (28 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_9dc : fetchRel scalar29MontMulCode 0x9DC = some (.alu .mul a3 (26 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_9e0 : fetchRel scalar29MontMulCode 0x9E0 = some (.alu .sub a4 a4 (29 : Fin 32), 4) := by decide
theorem smm_at_9e4 : fetchRel scalar29MontMulCode 0x9E4 = some (.alu .mulhu (8 : Fin 32) (26 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_9e8 : fetchRel scalar29MontMulCode 0x9E8 = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_9ea : fetchRel scalar29MontMulCode 0x9EA = some (.alu .mul (9 : Fin 32) (18 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_9ee : fetchRel scalar29MontMulCode 0x9EE = some (.alu .mulhu (28 : Fin 32) (18 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_9f2 : fetchRel scalar29MontMulCode 0x9F2 = some (.alu .mul (6 : Fin 32) (5 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_9f6 : fetchRel scalar29MontMulCode 0x9F6 = some (.alu .sltu a4 a2 a4, 4) := by decide
theorem smm_at_9fa : fetchRel scalar29MontMulCode 0x9FA = some (.aluImm .sll a5 a6 0x3, 4) := by decide
theorem smm_at_9fe : fetchRel scalar29MontMulCode 0x9FE = some (.alu .or a0 a0 a5, 2) := by decide
theorem smm_at_a00 : fetchRel scalar29MontMulCode 0xA00 = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_a02 : fetchRel scalar29MontMulCode 0xA02 = some (.alu .add a3 a3 a2, 2) := by decide
theorem smm_at_a04 : fetchRel scalar29MontMulCode 0xA04 = some (.alu .mulhu a4 (5 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_a08 : fetchRel scalar29MontMulCode 0xA08 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem smm_at_a0a : fetchRel scalar29MontMulCode 0xA0A = some (.alu .sltu a2 a3 a2, 4) := by decide
theorem smm_at_a0e : fetchRel scalar29MontMulCode 0xA0E = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_a10 : fetchRel scalar29MontMulCode 0xA10 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem smm_at_a12 : fetchRel scalar29MontMulCode 0xA12 = some (.alu .add (28 : Fin 32) (28 : Fin 32) a1, 2) := by decide
theorem smm_at_a14 : fetchRel scalar29MontMulCode 0xA14 = some (.alu .add (6 : Fin 32) (6 : Fin 32) (9 : Fin 32), 2) := by decide
theorem smm_at_a16 : fetchRel scalar29MontMulCode 0xA16 = some (.alu .sltu a2 (9 : Fin 32) a3, 4) := by decide
theorem smm_at_a1a : fetchRel scalar29MontMulCode 0xA1A = some (.alu .add (7 : Fin 32) (6 : Fin 32) a0, 4) := by decide
theorem smm_at_a1e : fetchRel scalar29MontMulCode 0xA1E = some (.alu .add a2 a2 (28 : Fin 32), 2) := by decide
theorem smm_at_a20 : fetchRel scalar29MontMulCode 0xA20 = some (.alu .mul (19 : Fin 32) (7 : Fin 32) (31 : Fin 32), 4) := by decide
theorem smm_at_a24 : fetchRel scalar29MontMulCode 0xA24 = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_a26 : fetchRel scalar29MontMulCode 0xA26 = some (.alu .sltu a0 (6 : Fin 32) (9 : Fin 32), 4) := by decide
theorem smm_at_a2a : fetchRel scalar29MontMulCode 0xA2A = some (.alu .sub (28 : Fin 32) (25 : Fin 32) (30 : Fin 32), 4) := by decide
theorem smm_at_a2e : fetchRel scalar29MontMulCode 0xA2E = some (.alu .add a0 a0 a2, 2) := by decide
theorem smm_at_a30 : fetchRel scalar29MontMulCode 0xA30 = some (.load .lw a2 sp 0x58, 2) := by decide
theorem smm_at_a32 : fetchRel scalar29MontMulCode 0xA32 = some (.load .lw a1 sp 0x50, 2) := by decide
theorem smm_at_a34 : fetchRel scalar29MontMulCode 0xA34 = some (.alu .add a2 a2 a1, 2) := by decide
theorem smm_at_a36 : fetchRel scalar29MontMulCode 0xA36 = some (.load .lw a3 sp 0x60, 2) := by decide
theorem smm_at_a38 : fetchRel scalar29MontMulCode 0xA38 = some (.load .lw a1 sp 0x54, 2) := by decide
theorem smm_at_a3a : fetchRel scalar29MontMulCode 0xA3A = some (.alu .add a3 a3 a1, 2) := by decide
theorem smm_at_a3c : fetchRel scalar29MontMulCode 0xA3C = some (.aluImm .srl a5 a6 0x1D, 4) := by decide
theorem smm_at_a40 : fetchRel scalar29MontMulCode 0xA40 = some (.alu .sltu (9 : Fin 32) a3 a1, 4) := by decide
theorem smm_at_a44 : fetchRel scalar29MontMulCode 0xA44 = some (.alu .add a0 a0 a5, 2) := by decide
theorem smm_at_a46 : fetchRel scalar29MontMulCode 0xA46 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem smm_at_a48 : fetchRel scalar29MontMulCode 0xA48 = some (.alu .sltu a5 (7 : Fin 32) (6 : Fin 32), 4) := by decide
theorem smm_at_a4c : fetchRel scalar29MontMulCode 0xA4C = some (.alu .and (31 : Fin 32) (19 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_a50 : fetchRel scalar29MontMulCode 0xA50 = some (.alu .mulhu (9 : Fin 32) (31 : Fin 32) ra, 4) := by decide
theorem smm_at_a54 : fetchRel scalar29MontMulCode 0xA54 = some (.load .lw a1 sp 0x104, 4) := by decide
theorem smm_at_a58 : fetchRel scalar29MontMulCode 0xA58 = some (.alu .sltu (8 : Fin 32) a3 a1, 4) := by decide
theorem smm_at_a5c : fetchRel scalar29MontMulCode 0xA5C = some (.alu .add a0 a0 a5, 2) := by decide
theorem smm_at_a5e : fetchRel scalar29MontMulCode 0xA5E = some (.alu .sub a2 a2 (8 : Fin 32), 2) := by decide
theorem smm_at_a60 : fetchRel scalar29MontMulCode 0xA60 = some (.load .lw a4 sp 0x120, 4) := by decide
theorem smm_at_a64 : fetchRel scalar29MontMulCode 0xA64 = some (.alu .sub a2 a2 a4, 2) := by decide
theorem smm_at_a66 : fetchRel scalar29MontMulCode 0xA66 = some (.alu .sub a3 a3 a1, 2) := by decide
theorem smm_at_a68 : fetchRel scalar29MontMulCode 0xA68 = some (.load .lw a5 sp 0xA0, 2) := by decide
theorem smm_at_a6a : fetchRel scalar29MontMulCode 0xA6A = some (.aluImm .srl a5 a5 0xC, 2) := by decide
theorem smm_at_a6c : fetchRel scalar29MontMulCode 0xA6C = some (.load .lw (8 : Fin 32) sp 0xD0, 2) := by decide
theorem smm_at_a6e : fetchRel scalar29MontMulCode 0xA6E = some (.aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x14, 2) := by decide
theorem smm_at_a70 : fetchRel scalar29MontMulCode 0xA70 = some (.alu .add a2 a2 a5, 2) := by decide
theorem smm_at_a72 : fetchRel scalar29MontMulCode 0xA72 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem smm_at_a74 : fetchRel scalar29MontMulCode 0xA74 = some (.alu .mul a5 (31 : Fin 32) ra, 4) := by decide
theorem smm_at_a78 : fetchRel scalar29MontMulCode 0xA78 = some (.alu .sltu a3 (8 : Fin 32) a3, 4) := by decide
theorem smm_at_a7c : fetchRel scalar29MontMulCode 0xA7C = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem smm_at_a7e : fetchRel scalar29MontMulCode 0xA7E = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_a80 : fetchRel scalar29MontMulCode 0xA80 = some (.load .lw a1 sp 0x64, 2) := by decide
theorem smm_at_a82 : fetchRel scalar29MontMulCode 0xA82 = some (.alu .add a2 a2 a1, 2) := by decide
theorem smm_at_a84 : fetchRel scalar29MontMulCode 0xA84 = some (.load .lw a3 sp 0x5C, 2) := by decide
theorem smm_at_a86 : fetchRel scalar29MontMulCode 0xA86 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem smm_at_a88 : fetchRel scalar29MontMulCode 0xA88 = some (.alu .sltu (9 : Fin 32) a3 (8 : Fin 32), 4) := by decide
theorem smm_at_a8c : fetchRel scalar29MontMulCode 0xA8C = some (.load .lw (8 : Fin 32) sp 0x70, 2) := by decide
theorem smm_at_a8e : fetchRel scalar29MontMulCode 0xA8E = some (.alu .add (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem smm_at_a90 : fetchRel scalar29MontMulCode 0xA90 = some (.load .lw a1 sp 0x6C, 2) := by decide
theorem smm_at_a92 : fetchRel scalar29MontMulCode 0xA92 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a1, 2) := by decide
theorem smm_at_a94 : fetchRel scalar29MontMulCode 0xA94 = some (.alu .sltu a3 (8 : Fin 32) a3, 4) := by decide
theorem smm_at_a98 : fetchRel scalar29MontMulCode 0xA98 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem smm_at_a9a : fetchRel scalar29MontMulCode 0xA9A = some (.load .lw a1 sp 0x68, 2) := by decide
theorem smm_at_a9c : fetchRel scalar29MontMulCode 0xA9C = some (.alu .add a3 a3 a1, 2) := by decide
theorem smm_at_a9e : fetchRel scalar29MontMulCode 0xA9E = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_aa0 : fetchRel scalar29MontMulCode 0xAA0 = some (.alu .add a6 a5 (7 : Fin 32), 4) := by decide
theorem smm_at_aa4 : fetchRel scalar29MontMulCode 0xAA4 = some (.load .lw a3 sp 0x74, 2) := by decide
theorem smm_at_aa6 : fetchRel scalar29MontMulCode 0xAA6 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem smm_at_aa8 : fetchRel scalar29MontMulCode 0xAA8 = some (.alu .mulhu (9 : Fin 32) (26 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_aac : fetchRel scalar29MontMulCode 0xAAC = some (.alu .sltu a5 a6 a5, 4) := by decide
theorem smm_at_ab0 : fetchRel scalar29MontMulCode 0xAB0 = some (.alu .sltu (8 : Fin 32) a3 (8 : Fin 32), 4) := by decide
theorem smm_at_ab4 : fetchRel scalar29MontMulCode 0xAB4 = some (.load .lw (25 : Fin 32) sp 0xD8, 2) := by decide
theorem smm_at_ab6 : fetchRel scalar29MontMulCode 0xAB6 = some (.alu .sub (8 : Fin 32) (8 : Fin 32) (25 : Fin 32), 4) := by decide
theorem smm_at_aba : fetchRel scalar29MontMulCode 0xABA = some (.alu .mul a4 (26 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_abe : fetchRel scalar29MontMulCode 0xABE = some (.alu .add a0 a0 a5, 2) := by decide
theorem smm_at_ac0 : fetchRel scalar29MontMulCode 0xAC0 = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem smm_at_ac2 : fetchRel scalar29MontMulCode 0xAC2 = some (.alu .mul a5 (18 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_ac6 : fetchRel scalar29MontMulCode 0xAC6 = some (.load .lw (24 : Fin 32) sp 0xDC, 2) := by decide
theorem smm_at_ac8 : fetchRel scalar29MontMulCode 0xAC8 = some (.alu .sltu (8 : Fin 32) a3 (24 : Fin 32), 4) := by decide
theorem smm_at_acc : fetchRel scalar29MontMulCode 0xACC = some (.alu .sub a2 a2 (8 : Fin 32), 2) := by decide
theorem smm_at_ace : fetchRel scalar29MontMulCode 0xACE = some (.alu .mulhu (8 : Fin 32) (18 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_ad2 : fetchRel scalar29MontMulCode 0xAD2 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem smm_at_ad4 : fetchRel scalar29MontMulCode 0xAD4 = some (.alu .mul (9 : Fin 32) (5 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_ad8 : fetchRel scalar29MontMulCode 0xAD8 = some (.alu .sub a3 a3 (24 : Fin 32), 4) := by decide
theorem smm_at_adc : fetchRel scalar29MontMulCode 0xADC = some (.alu .mulhu a1 (5 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_ae0 : fetchRel scalar29MontMulCode 0xAE0 = some (.alu .add a4 a4 a3, 2) := by decide
theorem smm_at_ae2 : fetchRel scalar29MontMulCode 0xAE2 = some (.alu .mul (6 : Fin 32) (31 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_ae6 : fetchRel scalar29MontMulCode 0xAE6 = some (.alu .mulhu (7 : Fin 32) (31 : Fin 32) (20 : Fin 32), 4) := by decide
theorem smm_at_aea : fetchRel scalar29MontMulCode 0xAEA = some (.alu .sltu a3 a4 a3, 4) := by decide
theorem smm_at_aee : fetchRel scalar29MontMulCode 0xAEE = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_af0 : fetchRel scalar29MontMulCode 0xAF0 = some (.alu .add a5 a5 a4, 2) := by decide
theorem smm_at_af2 : fetchRel scalar29MontMulCode 0xAF2 = some (.alu .add a2 a2 (8 : Fin 32), 2) := by decide
theorem smm_at_af4 : fetchRel scalar29MontMulCode 0xAF4 = some (.alu .sltu a3 a5 a4, 4) := by decide
theorem smm_at_af8 : fetchRel scalar29MontMulCode 0xAF8 = some (.alu .add a2 a2 a3, 2) := by decide
theorem smm_at_afa : fetchRel scalar29MontMulCode 0xAFA = some (.alu .add (9 : Fin 32) (9 : Fin 32) a5, 2) := by decide
theorem smm_at_afc : fetchRel scalar29MontMulCode 0xAFC = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_afe : fetchRel scalar29MontMulCode 0xAFE = some (.alu .sltu a2 (9 : Fin 32) a5, 4) := by decide
theorem smm_at_b02 : fetchRel scalar29MontMulCode 0xB02 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_b04 : fetchRel scalar29MontMulCode 0xB04 = some (.alu .add (6 : Fin 32) (6 : Fin 32) (9 : Fin 32), 2) := by decide
theorem smm_at_b06 : fetchRel scalar29MontMulCode 0xB06 = some (.alu .add a1 a1 (7 : Fin 32), 2) := by decide
theorem smm_at_b08 : fetchRel scalar29MontMulCode 0xB08 = some (.alu .sltu a2 (6 : Fin 32) (9 : Fin 32), 4) := by decide
theorem smm_at_b0c : fetchRel scalar29MontMulCode 0xB0C = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_b0e : fetchRel scalar29MontMulCode 0xB0E = some (.aluImm .srl a2 a6 0x1D, 4) := by decide
theorem smm_at_b12 : fetchRel scalar29MontMulCode 0xB12 = some (.aluImm .sll a3 a0 0x3, 4) := by decide
theorem smm_at_b16 : fetchRel scalar29MontMulCode 0xB16 = some (.aluImm .srl a0 a0 0x1D, 2) := by decide
theorem smm_at_b18 : fetchRel scalar29MontMulCode 0xB18 = some (.alu .or a2 a2 a3, 2) := by decide
theorem smm_at_b1a : fetchRel scalar29MontMulCode 0xB1A = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_b1c : fetchRel scalar29MontMulCode 0xB1C = some (.load .lw a3 sp 0x134, 4) := by decide
theorem smm_at_b20 : fetchRel scalar29MontMulCode 0xB20 = some (.load .lw a4 sp 0x84, 2) := by decide
theorem smm_at_b22 : fetchRel scalar29MontMulCode 0xB22 = some (.alu .sltu a1 a4 a3, 4) := by decide
theorem smm_at_b26 : fetchRel scalar29MontMulCode 0xB26 = some (.alu .sub a3 a4 a3, 4) := by decide
theorem smm_at_b2a : fetchRel scalar29MontMulCode 0xB2A = some (.load .lw a4 sp 0x88, 2) := by decide
theorem smm_at_b2c : fetchRel scalar29MontMulCode 0xB2C = some (.alu .sub a1 a4 a1, 4) := by decide
theorem smm_at_b30 : fetchRel scalar29MontMulCode 0xB30 = some (.load .lw a4 sp 0x98, 2) := by decide
theorem smm_at_b32 : fetchRel scalar29MontMulCode 0xB32 = some (.alu .add a4 a4 a3, 2) := by decide
theorem smm_at_b34 : fetchRel scalar29MontMulCode 0xB34 = some (.load .lw a5 sp 0x94, 2) := by decide
theorem smm_at_b36 : fetchRel scalar29MontMulCode 0xB36 = some (.alu .add a1 a1 a5, 2) := by decide
theorem smm_at_b38 : fetchRel scalar29MontMulCode 0xB38 = some (.alu .sltu a3 a4 a3, 4) := by decide
theorem smm_at_b3c : fetchRel scalar29MontMulCode 0xB3C = some (.load .lw a5 sp 0x124, 4) := by decide
theorem smm_at_b40 : fetchRel scalar29MontMulCode 0xB40 = some (.alu .sub a1 a1 a5, 2) := by decide
theorem smm_at_b42 : fetchRel scalar29MontMulCode 0xB42 = some (.load .lw a5 sp 0x8C, 2) := by decide
theorem smm_at_b44 : fetchRel scalar29MontMulCode 0xB44 = some (.alu .add a3 a3 a5, 2) := by decide
theorem smm_at_b46 : fetchRel scalar29MontMulCode 0xB46 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_b48 : fetchRel scalar29MontMulCode 0xB48 = some (.load .lw a3 sp 0x90, 2) := by decide
theorem smm_at_b4a : fetchRel scalar29MontMulCode 0xB4A = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_b4c : fetchRel scalar29MontMulCode 0xB4C = some (.alu .sltu (9 : Fin 32) a3 a4, 4) := by decide
theorem smm_at_b50 : fetchRel scalar29MontMulCode 0xB50 = some (.load .lw a5 sp 0x78, 2) := by decide
theorem smm_at_b52 : fetchRel scalar29MontMulCode 0xB52 = some (.alu .add a5 a5 a3, 2) := by decide
theorem smm_at_b54 : fetchRel scalar29MontMulCode 0xB54 = some (.load .lw a4 sp 0x7C, 2) := by decide
theorem smm_at_b56 : fetchRel scalar29MontMulCode 0xB56 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem smm_at_b58 : fetchRel scalar29MontMulCode 0xB58 = some (.alu .sltu a3 a5 a3, 4) := by decide
theorem smm_at_b5c : fetchRel scalar29MontMulCode 0xB5C = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_b5e : fetchRel scalar29MontMulCode 0xB5E = some (.load .lw (30 : Fin 32) sp 0xE4, 2) := by decide
theorem smm_at_b60 : fetchRel scalar29MontMulCode 0xB60 = some (.alu .sub a3 a3 (30 : Fin 32), 4) := by decide
theorem smm_at_b64 : fetchRel scalar29MontMulCode 0xB64 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_b66 : fetchRel scalar29MontMulCode 0xB66 = some (.alu .add (20 : Fin 32) (6 : Fin 32) a2, 4) := by decide
theorem smm_at_b6a : fetchRel scalar29MontMulCode 0xB6A = some (.alu .sltu a2 (20 : Fin 32) (6 : Fin 32), 4) := by decide
theorem smm_at_b6e : fetchRel scalar29MontMulCode 0xB6E = some (.load .lw ra sp 0xF4, 2) := by decide
theorem smm_at_b70 : fetchRel scalar29MontMulCode 0xB70 = some (.alu .sltu a3 a5 ra, 4) := by decide
theorem smm_at_b74 : fetchRel scalar29MontMulCode 0xB74 = some (.alu .add (6 : Fin 32) a0 a2, 4) := by decide
theorem smm_at_b78 : fetchRel scalar29MontMulCode 0xB78 = some (.alu .sub a1 a1 a3, 2) := by decide
theorem smm_at_b7a : fetchRel scalar29MontMulCode 0xB7A = some (.load .lw a2 sp 0xAC, 2) := by decide
theorem smm_at_b7c : fetchRel scalar29MontMulCode 0xB7C = some (.aluImm .srl a2 a2 0xC, 2) := by decide
theorem smm_at_b7e : fetchRel scalar29MontMulCode 0xB7E = some (.alu .mul a3 (18 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_b82 : fetchRel scalar29MontMulCode 0xB82 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_b84 : fetchRel scalar29MontMulCode 0xB84 = some (.alu .mulhu a2 (18 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_b88 : fetchRel scalar29MontMulCode 0xB88 = some (.load .lw a4 sp 0xF0, 2) := by decide
theorem smm_at_b8a : fetchRel scalar29MontMulCode 0xB8A = some (.aluImm .sll a4 a4 0x14, 2) := by decide
theorem smm_at_b8c : fetchRel scalar29MontMulCode 0xB8C = some (.alu .mul (9 : Fin 32) (5 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_b90 : fetchRel scalar29MontMulCode 0xB90 = some (.alu .sub a5 a5 ra, 4) := by decide
theorem smm_at_b94 : fetchRel scalar29MontMulCode 0xB94 = some (.alu .mulhu (8 : Fin 32) (5 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_b98 : fetchRel scalar29MontMulCode 0xB98 = some (.alu .add a4 a4 a5, 2) := by decide
theorem smm_at_b9a : fetchRel scalar29MontMulCode 0xB9A = some (.alu .mul a0 (31 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_b9e : fetchRel scalar29MontMulCode 0xB9E = some (.alu .mulhu (7 : Fin 32) (31 : Fin 32) (22 : Fin 32), 4) := by decide
theorem smm_at_ba2 : fetchRel scalar29MontMulCode 0xBA2 = some (.alu .sltu a5 a4 a5, 4) := by decide
theorem smm_at_ba6 : fetchRel scalar29MontMulCode 0xBA6 = some (.alu .add a1 a1 a5, 2) := by decide
theorem smm_at_ba8 : fetchRel scalar29MontMulCode 0xBA8 = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_baa : fetchRel scalar29MontMulCode 0xBAA = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_bac : fetchRel scalar29MontMulCode 0xBAC = some (.alu .sltu a2 a3 a4, 4) := by decide
theorem smm_at_bb0 : fetchRel scalar29MontMulCode 0xBB0 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_bb2 : fetchRel scalar29MontMulCode 0xBB2 = some (.alu .add (9 : Fin 32) (9 : Fin 32) a3, 2) := by decide
theorem smm_at_bb4 : fetchRel scalar29MontMulCode 0xBB4 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem smm_at_bb6 : fetchRel scalar29MontMulCode 0xBB6 = some (.alu .sltu a2 (9 : Fin 32) a3, 4) := by decide
theorem smm_at_bba : fetchRel scalar29MontMulCode 0xBBA = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_bbc : fetchRel scalar29MontMulCode 0xBBC = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem smm_at_bbe : fetchRel scalar29MontMulCode 0xBBE = some (.alu .add a1 a1 (7 : Fin 32), 2) := by decide
theorem smm_at_bc0 : fetchRel scalar29MontMulCode 0xBC0 = some (.alu .sltu a2 a0 (9 : Fin 32), 4) := by decide
theorem smm_at_bc4 : fetchRel scalar29MontMulCode 0xBC4 = some (.aluImm .sll a3 (6 : Fin 32) 0x3, 4) := by decide
theorem smm_at_bc8 : fetchRel scalar29MontMulCode 0xBC8 = some (.aluImm .srl a4 (20 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_bcc : fetchRel scalar29MontMulCode 0xBCC = some (.alu .or a3 a3 a4, 2) := by decide
theorem smm_at_bce : fetchRel scalar29MontMulCode 0xBCE = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_bd0 : fetchRel scalar29MontMulCode 0xBD0 = some (.load .lw a2 sp 0xA8, 2) := by decide
theorem smm_at_bd2 : fetchRel scalar29MontMulCode 0xBD2 = some (.load .lw a4 sp 0xC0, 2) := by decide
theorem smm_at_bd4 : fetchRel scalar29MontMulCode 0xBD4 = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_bd6 : fetchRel scalar29MontMulCode 0xBD6 = some (.load .lw a4 sp 0x10C, 4) := by decide
theorem smm_at_bda : fetchRel scalar29MontMulCode 0xBDA = some (.load .lw (9 : Fin 32) sp 0x9C, 2) := by decide
theorem smm_at_bdc : fetchRel scalar29MontMulCode 0xBDC = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem smm_at_bde : fetchRel scalar29MontMulCode 0xBDE = some (.aluImm .srl a5 (6 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_be2 : fetchRel scalar29MontMulCode 0xBE2 = some (.alu .sltu (9 : Fin 32) a4 (9 : Fin 32), 4) := by decide
theorem smm_at_be6 : fetchRel scalar29MontMulCode 0xBE6 = some (.alu .add a5 a5 a1, 2) := by decide
theorem smm_at_be8 : fetchRel scalar29MontMulCode 0xBE8 = some (.alu .add a2 a2 (9 : Fin 32), 2) := by decide
theorem smm_at_bea : fetchRel scalar29MontMulCode 0xBEA = some (.alu .add (6 : Fin 32) a0 a3, 4) := by decide
theorem smm_at_bee : fetchRel scalar29MontMulCode 0xBEE = some (.load .lw a1 sp 0x128, 4) := by decide
theorem smm_at_bf2 : fetchRel scalar29MontMulCode 0xBF2 = some (.load .lw a6 sp 0xE0, 2) := by decide
theorem smm_at_bf4 : fetchRel scalar29MontMulCode 0xBF4 = some (.alu .add a3 a1 a6, 4) := by decide
theorem smm_at_bf8 : fetchRel scalar29MontMulCode 0xBF8 = some (.alu .sltu a0 (6 : Fin 32) a0, 4) := by decide
theorem smm_at_bfc : fetchRel scalar29MontMulCode 0xBFC = some (.alu .sltu (9 : Fin 32) a4 a3, 4) := by decide
theorem smm_at_c00 : fetchRel scalar29MontMulCode 0xC00 = some (.alu .add (7 : Fin 32) a5 a0, 4) := by decide
theorem smm_at_c04 : fetchRel scalar29MontMulCode 0xC04 = some (.alu .sub a2 a2 (9 : Fin 32), 2) := by decide
theorem smm_at_c06 : fetchRel scalar29MontMulCode 0xC06 = some (.alu .sltu a5 a3 a1, 4) := by decide
theorem smm_at_c0a : fetchRel scalar29MontMulCode 0xC0A = some (.load .lw (9 : Fin 32) sp 0x12C, 4) := by decide
theorem smm_at_c0e : fetchRel scalar29MontMulCode 0xC0E = some (.load .lw (22 : Fin 32) sp 0xE8, 2) := by decide
theorem smm_at_c10 : fetchRel scalar29MontMulCode 0xC10 = some (.alu .add (9 : Fin 32) (9 : Fin 32) (22 : Fin 32), 2) := by decide
theorem smm_at_c12 : fetchRel scalar29MontMulCode 0xC12 = some (.alu .add a5 a5 (9 : Fin 32), 2) := by decide
theorem smm_at_c14 : fetchRel scalar29MontMulCode 0xC14 = some (.load .lw a0 sp 0xA4, 2) := by decide
theorem smm_at_c16 : fetchRel scalar29MontMulCode 0xC16 = some (.alu .add a2 a2 a0, 2) := by decide
theorem smm_at_c18 : fetchRel scalar29MontMulCode 0xC18 = some (.alu .sub a4 a4 a3, 2) := by decide
theorem smm_at_c1a : fetchRel scalar29MontMulCode 0xC1A = some (.alu .sub a2 a2 a5, 2) := by decide
theorem smm_at_c1c : fetchRel scalar29MontMulCode 0xC1C = some (.load .lw a3 sp 0xB8, 2) := by decide
theorem smm_at_c1e : fetchRel scalar29MontMulCode 0xC1E = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_c20 : fetchRel scalar29MontMulCode 0xC20 = some (.alu .mul a5 (5 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_c24 : fetchRel scalar29MontMulCode 0xC24 = some (.alu .sltu a4 a3 a4, 4) := by decide
theorem smm_at_c28 : fetchRel scalar29MontMulCode 0xC28 = some (.alu .mulhu (9 : Fin 32) (5 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_c2c : fetchRel scalar29MontMulCode 0xC2C = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_c2e : fetchRel scalar29MontMulCode 0xC2E = some (.alu .mul a4 (31 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_c32 : fetchRel scalar29MontMulCode 0xC32 = some (.load .lw (8 : Fin 32) sp 0xEC, 2) := by decide
theorem smm_at_c34 : fetchRel scalar29MontMulCode 0xC34 = some (.aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x14, 2) := by decide
theorem smm_at_c36 : fetchRel scalar29MontMulCode 0xC36 = some (.alu .mulhu a1 (31 : Fin 32) (23 : Fin 32), 4) := by decide
theorem smm_at_c3a : fetchRel scalar29MontMulCode 0xC3A = some (.load .lw a0 sp 0x100, 4) := by decide
theorem smm_at_c3e : fetchRel scalar29MontMulCode 0xC3E = some (.aluImm .srl a0 a0 0xC, 2) := by decide
theorem smm_at_c40 : fetchRel scalar29MontMulCode 0xC40 = some (.alu .add (8 : Fin 32) (8 : Fin 32) a3, 2) := by decide
theorem smm_at_c42 : fetchRel scalar29MontMulCode 0xC42 = some (.alu .add a0 a0 a2, 2) := by decide
theorem smm_at_c44 : fetchRel scalar29MontMulCode 0xC44 = some (.alu .sltu a2 (8 : Fin 32) a3, 4) := by decide
theorem smm_at_c48 : fetchRel scalar29MontMulCode 0xC48 = some (.alu .add a0 a0 a2, 2) := by decide
theorem smm_at_c4a : fetchRel scalar29MontMulCode 0xC4A = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem smm_at_c4c : fetchRel scalar29MontMulCode 0xC4C = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem smm_at_c4e : fetchRel scalar29MontMulCode 0xC4E = some (.alu .sltu a2 a5 (8 : Fin 32), 4) := by decide
theorem smm_at_c52 : fetchRel scalar29MontMulCode 0xC52 = some (.alu .add a0 a0 a2, 2) := by decide
theorem smm_at_c54 : fetchRel scalar29MontMulCode 0xC54 = some (.alu .add a4 a4 a5, 2) := by decide
theorem smm_at_c56 : fetchRel scalar29MontMulCode 0xC56 = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_c58 : fetchRel scalar29MontMulCode 0xC58 = some (.alu .sltu a1 a4 a5, 4) := by decide
theorem smm_at_c5c : fetchRel scalar29MontMulCode 0xC5C = some (.aluImm .sll a2 (7 : Fin 32) 0x3, 4) := by decide
theorem smm_at_c60 : fetchRel scalar29MontMulCode 0xC60 = some (.aluImm .srl a3 (6 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_c64 : fetchRel scalar29MontMulCode 0xC64 = some (.alu .or a2 a2 a3, 2) := by decide
theorem smm_at_c66 : fetchRel scalar29MontMulCode 0xC66 = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_c68 : fetchRel scalar29MontMulCode 0xC68 = some (.aluImm .srl a1 (7 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_c6c : fetchRel scalar29MontMulCode 0xC6C = some (.alu .add (7 : Fin 32) a4 a2, 4) := by decide
theorem smm_at_c70 : fetchRel scalar29MontMulCode 0xC70 = some (.alu .mul a3 (31 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_c74 : fetchRel scalar29MontMulCode 0xC74 = some (.alu .mulhu a5 (31 : Fin 32) (27 : Fin 32), 4) := by decide
theorem smm_at_c78 : fetchRel scalar29MontMulCode 0xC78 = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_c7a : fetchRel scalar29MontMulCode 0xC7A = some (.alu .sltu a1 (7 : Fin 32) a4, 4) := by decide
theorem smm_at_c7e : fetchRel scalar29MontMulCode 0xC7E = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_c80 : fetchRel scalar29MontMulCode 0xC80 = some (.load .lw a1 sp 0xD4, 2) := by decide
theorem smm_at_c82 : fetchRel scalar29MontMulCode 0xC82 = some (.aluImm .sll a1 a1 0x14, 2) := by decide
theorem smm_at_c84 : fetchRel scalar29MontMulCode 0xC84 = some (.aluImm .srl a4 (21 : Fin 32) 0xC, 4) := by decide
theorem smm_at_c88 : fetchRel scalar29MontMulCode 0xC88 = some (.alu .add a1 a1 (28 : Fin 32), 2) := by decide
theorem smm_at_c8a : fetchRel scalar29MontMulCode 0xC8A = some (.load .lw a2 sp 0x118, 4) := by decide
theorem smm_at_c8e : fetchRel scalar29MontMulCode 0xC8E = some (.alu .add a4 a4 a2, 2) := by decide
theorem smm_at_c90 : fetchRel scalar29MontMulCode 0xC90 = some (.alu .sltu (9 : Fin 32) a1 (28 : Fin 32), 4) := by decide
theorem smm_at_c94 : fetchRel scalar29MontMulCode 0xC94 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem smm_at_c96 : fetchRel scalar29MontMulCode 0xC96 = some (.aluImm .sll (9 : Fin 32) a0 0x3, 4) := by decide
theorem smm_at_c9a : fetchRel scalar29MontMulCode 0xC9A = some (.alu .add a4 a4 a5, 2) := by decide
theorem smm_at_c9c : fetchRel scalar29MontMulCode 0xC9C = some (.alu .add a3 a3 a1, 2) := by decide
theorem smm_at_c9e : fetchRel scalar29MontMulCode 0xC9E = some (.aluImm .srl a5 (7 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_ca2 : fetchRel scalar29MontMulCode 0xCA2 = some (.alu .sltu a1 a3 a1, 4) := by decide
theorem smm_at_ca6 : fetchRel scalar29MontMulCode 0xCA6 = some (.alu .or a5 a5 (9 : Fin 32), 2) := by decide
theorem smm_at_ca8 : fetchRel scalar29MontMulCode 0xCA8 = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_caa : fetchRel scalar29MontMulCode 0xCAA = some (.aluImm .srl a0 a0 0x1D, 2) := by decide
theorem smm_at_cac : fetchRel scalar29MontMulCode 0xCAC = some (.alu .add (28 : Fin 32) a3 a5, 4) := by decide
theorem smm_at_cb0 : fetchRel scalar29MontMulCode 0xCB0 = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_cb2 : fetchRel scalar29MontMulCode 0xCB2 = some (.alu .sltu a1 (28 : Fin 32) a3, 4) := by decide
theorem smm_at_cb6 : fetchRel scalar29MontMulCode 0xCB6 = some (.alu .add a0 a0 a1, 2) := by decide
theorem smm_at_cb8 : fetchRel scalar29MontMulCode 0xCB8 = some (.aluImm .sll a1 a0 0x3, 4) := by decide
theorem smm_at_cbc : fetchRel scalar29MontMulCode 0xCBC = some (.aluImm .srl a3 (26 : Fin 32) 0xC, 4) := by decide
theorem smm_at_cc0 : fetchRel scalar29MontMulCode 0xCC0 = some (.load .lw (9 : Fin 32) sp 0xC8, 2) := by decide
theorem smm_at_cc2 : fetchRel scalar29MontMulCode 0xCC2 = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x14, 2) := by decide
theorem smm_at_cc4 : fetchRel scalar29MontMulCode 0xCC4 = some (.alu .add a5 (9 : Fin 32) (29 : Fin 32), 4) := by decide
theorem smm_at_cc8 : fetchRel scalar29MontMulCode 0xCC8 = some (.alu .add a3 a3 (17 : Fin 32), 2) := by decide
theorem smm_at_cca : fetchRel scalar29MontMulCode 0xCCA = some (.aluImm .srl a4 (28 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_cce : fetchRel scalar29MontMulCode 0xCCE = some (.alu .sltu (9 : Fin 32) a5 (9 : Fin 32), 4) := by decide
theorem smm_at_cd2 : fetchRel scalar29MontMulCode 0xCD2 = some (.alu .or a1 a1 a4, 2) := by decide
theorem smm_at_cd4 : fetchRel scalar29MontMulCode 0xCD4 = some (.alu .add a3 a3 (9 : Fin 32), 2) := by decide
theorem smm_at_cd6 : fetchRel scalar29MontMulCode 0xCD6 = some (.aluImm .srl a4 a0 0x1D, 4) := by decide
theorem smm_at_cda : fetchRel scalar29MontMulCode 0xCDA = some (.alu .add (29 : Fin 32) a5 a1, 4) := by decide
theorem smm_at_cde : fetchRel scalar29MontMulCode 0xCDE = some (.alu .add a3 a3 a4, 2) := by decide
theorem smm_at_ce0 : fetchRel scalar29MontMulCode 0xCE0 = some (.alu .sltu a1 (29 : Fin 32) a5, 4) := by decide
theorem smm_at_ce4 : fetchRel scalar29MontMulCode 0xCE4 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_ce6 : fetchRel scalar29MontMulCode 0xCE6 = some (.aluImm .sll a3 a1 0x3, 4) := by decide
theorem smm_at_cea : fetchRel scalar29MontMulCode 0xCEA = some (.aluImm .srl a4 (18 : Fin 32) 0xC, 4) := by decide
theorem smm_at_cee : fetchRel scalar29MontMulCode 0xCEE = some (.load .lw (9 : Fin 32) sp 0x110, 4) := by decide
theorem smm_at_cf2 : fetchRel scalar29MontMulCode 0xCF2 = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x14, 2) := by decide
theorem smm_at_cf4 : fetchRel scalar29MontMulCode 0xCF4 = some (.alu .add a5 (9 : Fin 32) (24 : Fin 32), 4) := by decide
theorem smm_at_cf8 : fetchRel scalar29MontMulCode 0xCF8 = some (.alu .add a4 a4 (25 : Fin 32), 2) := by decide
theorem smm_at_cfa : fetchRel scalar29MontMulCode 0xCFA = some (.aluImm .srl a0 (29 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_cfe : fetchRel scalar29MontMulCode 0xCFE = some (.alu .sltu (9 : Fin 32) a5 (9 : Fin 32), 4) := by decide
theorem smm_at_d02 : fetchRel scalar29MontMulCode 0xD02 = some (.alu .or a0 a0 a3, 2) := by decide
theorem smm_at_d04 : fetchRel scalar29MontMulCode 0xD04 = some (.alu .add a4 a4 (9 : Fin 32), 2) := by decide
theorem smm_at_d06 : fetchRel scalar29MontMulCode 0xD06 = some (.aluImm .srl a1 a1 0x1D, 2) := by decide
theorem smm_at_d08 : fetchRel scalar29MontMulCode 0xD08 = some (.alu .add (18 : Fin 32) a5 a0, 4) := by decide
theorem smm_at_d0c : fetchRel scalar29MontMulCode 0xD0C = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_d0e : fetchRel scalar29MontMulCode 0xD0E = some (.alu .sltu a3 (18 : Fin 32) a5, 4) := by decide
theorem smm_at_d12 : fetchRel scalar29MontMulCode 0xD12 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_d14 : fetchRel scalar29MontMulCode 0xD14 = some (.aluImm .sll a3 a1 0x3, 4) := by decide
theorem smm_at_d18 : fetchRel scalar29MontMulCode 0xD18 = some (.aluImm .srl a4 (5 : Fin 32) 0xC, 4) := by decide
theorem smm_at_d1c : fetchRel scalar29MontMulCode 0xD1C = some (.load .lw (17 : Fin 32) sp 0x11C, 4) := by decide
theorem smm_at_d20 : fetchRel scalar29MontMulCode 0xD20 = some (.aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x14, 2) := by decide
theorem smm_at_d22 : fetchRel scalar29MontMulCode 0xD22 = some (.alu .add a5 (17 : Fin 32) ra, 4) := by decide
theorem smm_at_d26 : fetchRel scalar29MontMulCode 0xD26 = some (.alu .add a4 a4 (30 : Fin 32), 2) := by decide
theorem smm_at_d28 : fetchRel scalar29MontMulCode 0xD28 = some (.aluImm .srl a0 (18 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_d2c : fetchRel scalar29MontMulCode 0xD2C = some (.alu .sltu (8 : Fin 32) a5 (17 : Fin 32), 4) := by decide
theorem smm_at_d30 : fetchRel scalar29MontMulCode 0xD30 = some (.alu .or a0 a0 a3, 2) := by decide
theorem smm_at_d32 : fetchRel scalar29MontMulCode 0xD32 = some (.alu .add a4 a4 (8 : Fin 32), 2) := by decide
theorem smm_at_d34 : fetchRel scalar29MontMulCode 0xD34 = some (.aluImm .srl a1 a1 0x1D, 2) := by decide
theorem smm_at_d36 : fetchRel scalar29MontMulCode 0xD36 = some (.alu .add (9 : Fin 32) a5 a0, 4) := by decide
theorem smm_at_d3a : fetchRel scalar29MontMulCode 0xD3A = some (.alu .add a1 a1 a4, 2) := by decide
theorem smm_at_d3c : fetchRel scalar29MontMulCode 0xD3C = some (.alu .sltu a3 (9 : Fin 32) a5, 4) := by decide
theorem smm_at_d40 : fetchRel scalar29MontMulCode 0xD40 = some (.alu .add a1 a1 a3, 2) := by decide
theorem smm_at_d42 : fetchRel scalar29MontMulCode 0xD42 = some (.aluImm .sll a3 a1 0x3, 4) := by decide
theorem smm_at_d46 : fetchRel scalar29MontMulCode 0xD46 = some (.aluImm .srl a4 (31 : Fin 32) 0xC, 4) := by decide
theorem smm_at_d4a : fetchRel scalar29MontMulCode 0xD4A = some (.aluImm .sll (30 : Fin 32) (19 : Fin 32) 0x14, 4) := by decide
theorem smm_at_d4e : fetchRel scalar29MontMulCode 0xD4E = some (.alu .add a5 (30 : Fin 32) a6, 4) := by decide
theorem smm_at_d52 : fetchRel scalar29MontMulCode 0xD52 = some (.alu .add a4 a4 (22 : Fin 32), 2) := by decide
theorem smm_at_d54 : fetchRel scalar29MontMulCode 0xD54 = some (.aluImm .srl a0 (9 : Fin 32) 0x1D, 4) := by decide
theorem smm_at_d58 : fetchRel scalar29MontMulCode 0xD58 = some (.alu .sltu a2 a5 (30 : Fin 32), 4) := by decide
theorem smm_at_d5c : fetchRel scalar29MontMulCode 0xD5C = some (.alu .or a0 a0 a3, 2) := by decide
theorem smm_at_d5e : fetchRel scalar29MontMulCode 0xD5E = some (.alu .add a2 a2 a4, 2) := by decide
theorem smm_at_d60 : fetchRel scalar29MontMulCode 0xD60 = some (.aluImm .srl a1 a1 0x1D, 2) := by decide
theorem smm_at_d62 : fetchRel scalar29MontMulCode 0xD62 = some (.alu .add a0 a0 a5, 2) := by decide
theorem smm_at_d64 : fetchRel scalar29MontMulCode 0xD64 = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_d66 : fetchRel scalar29MontMulCode 0xD66 = some (.alu .sltu a2 a0 a5, 4) := by decide
theorem smm_at_d6a : fetchRel scalar29MontMulCode 0xD6A = some (.alu .add a1 a1 a2, 2) := by decide
theorem smm_at_d6c : fetchRel scalar29MontMulCode 0xD6C = some (.load .lw (8 : Fin 32) sp 0x130, 4) := by decide
theorem smm_at_d70 : fetchRel scalar29MontMulCode 0xD70 = some (.alu .and a2 (20 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_d74 : fetchRel scalar29MontMulCode 0xD74 = some (.alu .and a3 (6 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_d78 : fetchRel scalar29MontMulCode 0xD78 = some (.alu .and a4 (7 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_d7c : fetchRel scalar29MontMulCode 0xD7C = some (.alu .and a5 (28 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_d80 : fetchRel scalar29MontMulCode 0xD80 = some (.alu .and (5 : Fin 32) (29 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_d84 : fetchRel scalar29MontMulCode 0xD84 = some (.alu .and a6 (18 : Fin 32) (8 : Fin 32), 4) := by decide
theorem smm_at_d88 : fetchRel scalar29MontMulCode 0xD88 = some (.alu .and (9 : Fin 32) (9 : Fin 32) (8 : Fin 32), 2) := by decide
theorem smm_at_d8a : fetchRel scalar29MontMulCode 0xD8A = some (.alu .and (17 : Fin 32) a0 (8 : Fin 32), 4) := by decide
theorem smm_at_d8e : fetchRel scalar29MontMulCode 0xD8E = some (.aluImm .sll a1 a1 0x3, 2) := by decide
theorem smm_at_d90 : fetchRel scalar29MontMulCode 0xD90 = some (.aluImm .srl a0 a0 0x1D, 2) := by decide
theorem smm_at_d92 : fetchRel scalar29MontMulCode 0xD92 = some (.alu .or a0 a0 a1, 2) := by decide
theorem smm_at_d94 : fetchRel scalar29MontMulCode 0xD94 = some (.aluImm .add a1 sp 0x100, 2) := by decide
theorem smm_at_d96 : fetchRel scalar29MontMulCode 0xD96 = some (.store .sw a1 a2 0x38, 2) := by decide
theorem smm_at_d98 : fetchRel scalar29MontMulCode 0xD98 = some (.store .sw a1 a3 0x3C, 2) := by decide
theorem smm_at_d9a : fetchRel scalar29MontMulCode 0xD9A = some (.store .sw a1 a4 0x40, 2) := by decide
theorem smm_at_d9c : fetchRel scalar29MontMulCode 0xD9C = some (.store .sw a1 a5 0x44, 2) := by decide
theorem smm_at_d9e : fetchRel scalar29MontMulCode 0xD9E = some (.store .sw a1 (5 : Fin 32) 0x48, 4) := by decide
theorem smm_at_da2 : fetchRel scalar29MontMulCode 0xDA2 = some (.store .sw a1 a6 0x4C, 4) := by decide
theorem smm_at_da6 : fetchRel scalar29MontMulCode 0xDA6 = some (.store .sw a1 (9 : Fin 32) 0x50, 2) := by decide
theorem smm_at_da8 : fetchRel scalar29MontMulCode 0xDA8 = some (.store .sw a1 (17 : Fin 32) 0x54, 4) := by decide
theorem smm_at_dac : fetchRel scalar29MontMulCode 0xDAC = some (.store .sw a1 a0 0x58, 2) := by decide
theorem smm_at_dae : fetchRel scalar29MontMulCode 0xDAE = some (.aluImm .add a1 sp 0x138, 2) := by decide
theorem smm_at_db0 : fetchRel scalar29MontMulCode 0xDB0 = some (.load .lw a0 sp 0xF8, 2) := by decide
theorem smm_at_db2 : fetchRel scalar29MontMulCode 0xDB2 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem smm_at_db6 : fetchRel scalar29MontMulCode 0xDB6 = some (.jalr ra ra 0xFFFFFF3E, 4) := by decide
theorem smm_at_dba : fetchRel scalar29MontMulCode 0xDBA = some (.aluImm .add a0 sp 0x180, 2) := by decide
theorem smm_at_dbc : fetchRel scalar29MontMulCode 0xDBC = some (.load .lw ra a0 0xC, 4) := by decide
theorem smm_at_dc0 : fetchRel scalar29MontMulCode 0xDC0 = some (.load .lw (8 : Fin 32) a0 0x8, 2) := by decide
theorem smm_at_dc2 : fetchRel scalar29MontMulCode 0xDC2 = some (.load .lw (9 : Fin 32) a0 0x4, 2) := by decide
theorem smm_at_dc4 : fetchRel scalar29MontMulCode 0xDC4 = some (.load .lw (18 : Fin 32) a0 0x0, 4) := by decide
theorem smm_at_dc8 : fetchRel scalar29MontMulCode 0xDC8 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem smm_at_dca : fetchRel scalar29MontMulCode 0xDCA = some (.load .lw (19 : Fin 32) a0 0x7C, 4) := by decide
theorem smm_at_dce : fetchRel scalar29MontMulCode 0xDCE = some (.load .lw (20 : Fin 32) a0 0x78, 4) := by decide
theorem smm_at_dd2 : fetchRel scalar29MontMulCode 0xDD2 = some (.load .lw (21 : Fin 32) a0 0x74, 4) := by decide
theorem smm_at_dd6 : fetchRel scalar29MontMulCode 0xDD6 = some (.load .lw (22 : Fin 32) a0 0x70, 4) := by decide
theorem smm_at_dda : fetchRel scalar29MontMulCode 0xDDA = some (.load .lw (23 : Fin 32) a0 0x6C, 4) := by decide
theorem smm_at_dde : fetchRel scalar29MontMulCode 0xDDE = some (.load .lw (24 : Fin 32) a0 0x68, 4) := by decide
theorem smm_at_de2 : fetchRel scalar29MontMulCode 0xDE2 = some (.load .lw (25 : Fin 32) a0 0x64, 4) := by decide
theorem smm_at_de6 : fetchRel scalar29MontMulCode 0xDE6 = some (.load .lw (26 : Fin 32) a0 0x60, 4) := by decide
theorem smm_at_dea : fetchRel scalar29MontMulCode 0xDEA = some (.load .lw (27 : Fin 32) a0 0x5C, 4) := by decide
theorem smm_at_dee : fetchRel scalar29MontMulCode 0xDEE = some (.aluImm .add sp sp 0x190, 2) := by decide
theorem smm_at_df0 : fetchRel scalar29MontMulCode 0xDF0 = some (.jalr x0 ra 0x0, 2) := by decide
end

end C3.RV32
