import C3BootProofs.Proofs.MontMul12Main
import C3BootProofs.Proofs.UintSelect8

/-!
# P-256's Montgomery multiplication, as compiled

`crypto_bigint`'s `mul_montgomery_form::<8>` compiles to the same
instructions as `mul_montgomery_form::<12>` (`MontMul12.lean`), with eight
limbs: a 0x80-byte frame, loop counts of 8 and 7, and `Uint<8>::select`. This
file restates the declarations that depend on those sizes and reuses the rest.
-/

namespace C3.RV32

open C3.Image

set_option maxRecDepth 20000

theorem mm8_at_0 : fetchRel mulMont8Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) := by decide
theorem mm8_at_2 : fetchRel mulMont8Code 0x2 = some (.store .sw sp ra 0x7C, 2) := by decide
theorem mm8_at_4 : fetchRel mulMont8Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) := by decide
theorem mm8_at_6 : fetchRel mulMont8Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x74, 2) := by decide
theorem mm8_at_8 : fetchRel mulMont8Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x70, 2) := by decide
theorem mm8_at_a : fetchRel mulMont8Code 0xA = some (.store .sw sp (19 : Fin 32) 0x6C, 2) := by decide
theorem mm8_at_c : fetchRel mulMont8Code 0xC = some (.store .sw sp (20 : Fin 32) 0x68, 2) := by decide
theorem mm8_at_e : fetchRel mulMont8Code 0xE = some (.store .sw sp (21 : Fin 32) 0x64, 2) := by decide
theorem mm8_at_10 : fetchRel mulMont8Code 0x10 = some (.store .sw sp (22 : Fin 32) 0x60, 2) := by decide
theorem mm8_at_12 : fetchRel mulMont8Code 0x12 = some (.store .sw sp (23 : Fin 32) 0x5C, 2) := by decide
theorem mm8_at_14 : fetchRel mulMont8Code 0x14 = some (.store .sw sp (24 : Fin 32) 0x58, 2) := by decide
theorem mm8_at_16 : fetchRel mulMont8Code 0x16 = some (.store .sw sp (25 : Fin 32) 0x54, 2) := by decide
theorem mm8_at_18 : fetchRel mulMont8Code 0x18 = some (.store .sw sp (26 : Fin 32) 0x50, 2) := by decide
theorem mm8_at_1a : fetchRel mulMont8Code 0x1A = some (.alu .add (19 : Fin 32) x0 a4, 2) := by decide
theorem mm8_at_1c : fetchRel mulMont8Code 0x1C = some (.alu .add (23 : Fin 32) x0 a3, 2) := by decide
theorem mm8_at_1e : fetchRel mulMont8Code 0x1E = some (.alu .add (21 : Fin 32) x0 a2, 2) := by decide
theorem mm8_at_20 : fetchRel mulMont8Code 0x20 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem mm8_at_22 : fetchRel mulMont8Code 0x22 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem mm8_at_24 : fetchRel mulMont8Code 0x24 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem mm8_at_26 : fetchRel mulMont8Code 0x26 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem mm8_at_2a : fetchRel mulMont8Code 0x2A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm8_at_2c : fetchRel mulMont8Code 0x2C = some (.auipc ra 0x4000, 4) := by decide
theorem mm8_at_30 : fetchRel mulMont8Code 0x30 = some (.jalr ra ra 0xFFFFFC7C, 4) := by decide
theorem mm8_at_34 : fetchRel mulMont8Code 0x34 = some (.aluImm .add (22 : Fin 32) x0 0x0, 2) := by decide
theorem mm8_at_36 : fetchRel mulMont8Code 0x36 = some (.aluImm .add (28 : Fin 32) x0 0x0, 2) := by decide
theorem mm8_at_38 : fetchRel mulMont8Code 0x38 = some (.aluImm .add (29 : Fin 32) x0 0x0, 2) := by decide
theorem mm8_at_3a : fetchRel mulMont8Code 0x3A = some (.load .lw (6 : Fin 32) (21 : Fin 32) 0x0, 4) := by decide
theorem mm8_at_3e : fetchRel mulMont8Code 0x3E = some (.load .lw (7 : Fin 32) (23 : Fin 32) 0x0, 4) := by decide
theorem mm8_at_42 : fetchRel mulMont8Code 0x42 = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem mm8_at_44 : fetchRel mulMont8Code 0x44 = some (.aluImm .add a6 sp 0x10, 4) := by decide
theorem mm8_at_48 : fetchRel mulMont8Code 0x48 = some (.aluImm .add (17 : Fin 32) (23 : Fin 32) 0x4, 4) := by decide
theorem mm8_at_4c : fetchRel mulMont8Code 0x4C = some (.aluImm .add (5 : Fin 32) x0 0x8, 2) := by decide
theorem mm8_at_4e : fetchRel mulMont8Code 0x4E = some (.branch .beq (5 : Fin 32) x0 0xB4, 4) := by decide
theorem mm8_at_52 : fetchRel mulMont8Code 0x52 = some (.aluImm .sll a0 (29 : Fin 32) 0x2, 4) := by decide
theorem mm8_at_56 : fetchRel mulMont8Code 0x56 = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem mm8_at_58 : fetchRel mulMont8Code 0x58 = some (.load .lw (30 : Fin 32) a0 0x0, 4) := by decide
theorem mm8_at_5c : fetchRel mulMont8Code 0x5C = some (.alu .mul a0 (6 : Fin 32) (30 : Fin 32), 4) := by decide
theorem mm8_at_60 : fetchRel mulMont8Code 0x60 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem mm8_at_62 : fetchRel mulMont8Code 0x62 = some (.alu .add a1 a1 a0, 2) := by decide
theorem mm8_at_64 : fetchRel mulMont8Code 0x64 = some (.alu .mul (31 : Fin 32) (19 : Fin 32) a1, 4) := by decide
theorem mm8_at_68 : fetchRel mulMont8Code 0x68 = some (.alu .mulhu a2 (6 : Fin 32) (30 : Fin 32), 4) := by decide
theorem mm8_at_6c : fetchRel mulMont8Code 0x6C = some (.alu .mul a3 (31 : Fin 32) (7 : Fin 32), 4) := by decide
theorem mm8_at_70 : fetchRel mulMont8Code 0x70 = some (.alu .mulhu (9 : Fin 32) (31 : Fin 32) (7 : Fin 32), 4) := by decide
theorem mm8_at_74 : fetchRel mulMont8Code 0x74 = some (.alu .sltu a0 a1 a0, 4) := by decide
theorem mm8_at_78 : fetchRel mulMont8Code 0x78 = some (.alu .add a0 a0 a2, 2) := by decide
theorem mm8_at_7a : fetchRel mulMont8Code 0x7A = some (.alu .add a1 a1 a3, 2) := by decide
theorem mm8_at_7c : fetchRel mulMont8Code 0x7C = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem mm8_at_7e : fetchRel mulMont8Code 0x7E = some (.alu .sltu a2 a1 a3, 4) := by decide
theorem mm8_at_82 : fetchRel mulMont8Code 0x82 = some (.aluImm .add (25 : Fin 32) x0 0x7, 2) := by decide
theorem mm8_at_84 : fetchRel mulMont8Code 0x84 = some (.alu .add a2 a2 a0, 2) := by decide
theorem mm8_at_86 : fetchRel mulMont8Code 0x86 = some (.alu .sltu a3 a0 (9 : Fin 32), 4) := by decide
theorem mm8_at_8a : fetchRel mulMont8Code 0x8A = some (.alu .sltu a0 a2 a0, 4) := by decide
theorem mm8_at_8e : fetchRel mulMont8Code 0x8E = some (.alu .add (26 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem mm8_at_90 : fetchRel mulMont8Code 0x90 = some (.alu .add (24 : Fin 32) a3 a0, 4) := by decide
theorem mm8_at_94 : fetchRel mulMont8Code 0x94 = some (.alu .add a3 x0 a6, 2) := by decide
theorem mm8_at_96 : fetchRel mulMont8Code 0x96 = some (.alu .add (9 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem mm8_at_98 : fetchRel mulMont8Code 0x98 = some (.branch .beq (25 : Fin 32) x0 0x52, 4) := by decide
theorem mm8_at_9c : fetchRel mulMont8Code 0x9C = some (.load .lw a4 (26 : Fin 32) 0x0, 4) := by decide
theorem mm8_at_a0 : fetchRel mulMont8Code 0xA0 = some (.load .lw a5 (9 : Fin 32) 0x0, 2) := by decide
theorem mm8_at_a2 : fetchRel mulMont8Code 0xA2 = some (.alu .mulhu a0 a4 (31 : Fin 32), 4) := by decide
theorem mm8_at_a6 : fetchRel mulMont8Code 0xA6 = some (.alu .mul (8 : Fin 32) a5 (30 : Fin 32), 4) := by decide
theorem mm8_at_aa : fetchRel mulMont8Code 0xAA = some (.alu .mul a4 a4 (31 : Fin 32), 4) := by decide
theorem mm8_at_ae : fetchRel mulMont8Code 0xAE = some (.load .lw a1 a3 0x0, 2) := by decide
theorem mm8_at_b0 : fetchRel mulMont8Code 0xB0 = some (.alu .mulhu a5 a5 (30 : Fin 32), 4) := by decide
theorem mm8_at_b4 : fetchRel mulMont8Code 0xB4 = some (.alu .add a0 a0 (24 : Fin 32), 2) := by decide
theorem mm8_at_b6 : fetchRel mulMont8Code 0xB6 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem mm8_at_b8 : fetchRel mulMont8Code 0xB8 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem mm8_at_ba : fetchRel mulMont8Code 0xBA = some (.alu .add a2 a2 a4, 2) := by decide
theorem mm8_at_bc : fetchRel mulMont8Code 0xBC = some (.alu .sltu (8 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem mm8_at_c0 : fetchRel mulMont8Code 0xC0 = some (.alu .sltu a4 a2 a4, 4) := by decide
theorem mm8_at_c4 : fetchRel mulMont8Code 0xC4 = some (.alu .add a1 a1 a2, 2) := by decide
theorem mm8_at_c6 : fetchRel mulMont8Code 0xC6 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem mm8_at_c8 : fetchRel mulMont8Code 0xC8 = some (.alu .add a0 a0 a4, 2) := by decide
theorem mm8_at_ca : fetchRel mulMont8Code 0xCA = some (.alu .sltu a2 a1 a2, 4) := by decide
theorem mm8_at_ce : fetchRel mulMont8Code 0xCE = some (.alu .add a5 a5 a0, 2) := by decide
theorem mm8_at_d0 : fetchRel mulMont8Code 0xD0 = some (.store .sw a3 a1 0xFFFFFFFC, 4) := by decide
theorem mm8_at_d4 : fetchRel mulMont8Code 0xD4 = some (.alu .add a2 a2 a5, 2) := by decide
theorem mm8_at_d6 : fetchRel mulMont8Code 0xD6 = some (.alu .sltu (24 : Fin 32) a5 a0, 4) := by decide
theorem mm8_at_da : fetchRel mulMont8Code 0xDA = some (.alu .sltu a0 a2 a5, 4) := by decide
theorem mm8_at_de : fetchRel mulMont8Code 0xDE = some (.aluImm .add a3 a3 0x4, 2) := by decide
theorem mm8_at_e0 : fetchRel mulMont8Code 0xE0 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a0, 2) := by decide
theorem mm8_at_e2 : fetchRel mulMont8Code 0xE2 = some (.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x4, 2) := by decide
theorem mm8_at_e4 : fetchRel mulMont8Code 0xE4 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem mm8_at_e6 : fetchRel mulMont8Code 0xE6 = some (.branch .bne (25 : Fin 32) x0 0xFFFFFFB6, 4) := by decide
theorem mm8_at_ea : fetchRel mulMont8Code 0xEA = some (.alu .add (22 : Fin 32) (22 : Fin 32) a2, 2) := by decide
theorem mm8_at_ec : fetchRel mulMont8Code 0xEC = some (.alu .add a0 (24 : Fin 32) (28 : Fin 32), 4) := by decide
theorem mm8_at_f0 : fetchRel mulMont8Code 0xF0 = some (.alu .sltu a1 (22 : Fin 32) a2, 4) := by decide
theorem mm8_at_f4 : fetchRel mulMont8Code 0xF4 = some (.store .sw sp (22 : Fin 32) 0x28, 2) := by decide
theorem mm8_at_f6 : fetchRel mulMont8Code 0xF6 = some (.alu .add (22 : Fin 32) a0 a1, 4) := by decide
theorem mm8_at_fa : fetchRel mulMont8Code 0xFA = some (.aluImm .add (29 : Fin 32) (29 : Fin 32) 0x1, 2) := by decide
theorem mm8_at_fc : fetchRel mulMont8Code 0xFC = some (.aluImm .add (28 : Fin 32) x0 0x0, 2) := by decide
theorem mm8_at_fe : fetchRel mulMont8Code 0xFE = some (.branch .bne (29 : Fin 32) (5 : Fin 32) 0xFFFFFF54, 4) := by decide
theorem mm8_at_102 : fetchRel mulMont8Code 0x102 = some (.aluImm .add a0 sp 0x2C, 2) := by decide
theorem mm8_at_104 : fetchRel mulMont8Code 0x104 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem mm8_at_108 : fetchRel mulMont8Code 0x108 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm8_at_10a : fetchRel mulMont8Code 0x10A = some (.aluImm .add (19 : Fin 32) sp 0x2C, 4) := by decide
theorem mm8_at_10e : fetchRel mulMont8Code 0x10E = some (.auipc ra 0x4000, 4) := by decide
theorem mm8_at_112 : fetchRel mulMont8Code 0x112 = some (.jalr ra ra 0xFFFFFB9A, 4) := by decide
theorem mm8_at_116 : fetchRel mulMont8Code 0x116 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem mm8_at_118 : fetchRel mulMont8Code 0x118 = some (.aluImm .add (9 : Fin 32) sp 0xC, 2) := by decide
theorem mm8_at_11a : fetchRel mulMont8Code 0x11A = some (.aluImm .add (8 : Fin 32) x0 0x8, 2) := by decide
theorem mm8_at_11c : fetchRel mulMont8Code 0x11C = some (.branch .beq (8 : Fin 32) x0 0x20, 2) := by decide
theorem mm8_at_11e : fetchRel mulMont8Code 0x11E = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem mm8_at_120 : fetchRel mulMont8Code 0x120 = some (.load .lw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem mm8_at_124 : fetchRel mulMont8Code 0x124 = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem mm8_at_128 : fetchRel mulMont8Code 0x128 = some (.jalr ra ra 0x6BE, 4) := by decide
theorem mm8_at_12c : fetchRel mulMont8Code 0x12C = some (.alu .add a2 x0 a1, 2) := by decide
theorem mm8_at_12e : fetchRel mulMont8Code 0x12E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem mm8_at_130 : fetchRel mulMont8Code 0x130 = some (.store .sw (19 : Fin 32) a0 0x0, 4) := by decide
theorem mm8_at_134 : fetchRel mulMont8Code 0x134 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem mm8_at_136 : fetchRel mulMont8Code 0x136 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x4, 2) := by decide
theorem mm8_at_138 : fetchRel mulMont8Code 0x138 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem mm8_at_13a : fetchRel mulMont8Code 0x13A = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem mm8_at_13c : fetchRel mulMont8Code 0x13C = some (.store .sw sp (22 : Fin 32) 0x4C, 2) := by decide
theorem mm8_at_13e : fetchRel mulMont8Code 0x13E = some (.aluImm .add a0 sp 0x4C, 2) := by decide
theorem mm8_at_140 : fetchRel mulMont8Code 0x140 = some (.load .lw a0 sp 0x4C, 2) := by decide
theorem mm8_at_142 : fetchRel mulMont8Code 0x142 = some (.aluImm .sltu (9 : Fin 32) a0 0x1, 4) := by decide
theorem mm8_at_146 : fetchRel mulMont8Code 0x146 = some (.alu .and (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem mm8_at_148 : fetchRel mulMont8Code 0x148 = some (.store .sb sp (9 : Fin 32) 0x4C, 4) := by decide
theorem mm8_at_14c : fetchRel mulMont8Code 0x14C = some (.aluImm .add a0 sp 0x4C, 2) := by decide
theorem mm8_at_14e : fetchRel mulMont8Code 0x14E = some (.load .lbu a0 sp 0x4C, 4) := by decide
theorem mm8_at_152 : fetchRel mulMont8Code 0x152 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem mm8_at_154 : fetchRel mulMont8Code 0x154 = some (.alu .and a2 a2 a0, 2) := by decide
theorem mm8_at_156 : fetchRel mulMont8Code 0x156 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem mm8_at_158 : fetchRel mulMont8Code 0x158 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm8_at_15a : fetchRel mulMont8Code 0x15A = some (.auipc ra 0xFFFF1000, 4) := by decide
theorem mm8_at_15e : fetchRel mulMont8Code 0x15E = some (.jalr ra ra 0x688, 4) := by decide
theorem mm8_at_162 : fetchRel mulMont8Code 0x162 = some (.aluImm .add a1 sp 0x2C, 2) := by decide
theorem mm8_at_164 : fetchRel mulMont8Code 0x164 = some (.aluImm .add a2 sp 0xC, 2) := by decide
theorem mm8_at_166 : fetchRel mulMont8Code 0x166 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem mm8_at_168 : fetchRel mulMont8Code 0x168 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem mm8_at_16a : fetchRel mulMont8Code 0x16A = some (.auipc ra 0x0, 4) := by decide
theorem mm8_at_16e : fetchRel mulMont8Code 0x16E = some (.jalr ra ra 0x24, 4) := by decide
theorem mm8_at_172 : fetchRel mulMont8Code 0x172 = some (.load .lw ra sp 0x7C, 2) := by decide
theorem mm8_at_174 : fetchRel mulMont8Code 0x174 = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem mm8_at_176 : fetchRel mulMont8Code 0x176 = some (.load .lw (9 : Fin 32) sp 0x74, 2) := by decide
theorem mm8_at_178 : fetchRel mulMont8Code 0x178 = some (.load .lw (18 : Fin 32) sp 0x70, 2) := by decide
theorem mm8_at_17a : fetchRel mulMont8Code 0x17A = some (.load .lw (19 : Fin 32) sp 0x6C, 2) := by decide
theorem mm8_at_17c : fetchRel mulMont8Code 0x17C = some (.load .lw (20 : Fin 32) sp 0x68, 2) := by decide
theorem mm8_at_17e : fetchRel mulMont8Code 0x17E = some (.load .lw (21 : Fin 32) sp 0x64, 2) := by decide
theorem mm8_at_180 : fetchRel mulMont8Code 0x180 = some (.load .lw (22 : Fin 32) sp 0x60, 2) := by decide
theorem mm8_at_182 : fetchRel mulMont8Code 0x182 = some (.load .lw (23 : Fin 32) sp 0x5C, 2) := by decide
theorem mm8_at_184 : fetchRel mulMont8Code 0x184 = some (.load .lw (24 : Fin 32) sp 0x58, 2) := by decide
theorem mm8_at_186 : fetchRel mulMont8Code 0x186 = some (.load .lw (25 : Fin 32) sp 0x54, 2) := by decide
theorem mm8_at_188 : fetchRel mulMont8Code 0x188 = some (.load .lw (26 : Fin 32) sp 0x50, 2) := by decide
theorem mm8_at_18a : fetchRel mulMont8Code 0x18A = some (.aluImm .add sp sp 0x80, 2) := by decide
theorem mm8_at_18c : fetchRel mulMont8Code 0x18C = some (.jalr x0 ra 0x0, 2) := by decide

/-- The loop body in `mul_montgomery_form::<8>`. -/
abbrev mmBodyM8 : List BInstr :=
  mmBody (26 : Fin 32) (9 : Fin 32) a3 (31 : Fin 32) (30 : Fin 32) a2 (24 : Fin 32) (25 : Fin 32) a4 a5 a0
    (8 : Fin 32) a1

theorem mmBodyM_end8 : blockEnd mulMont8Code 0x9C mmBodyM8 = some 0xE6 := by decide

set_option maxRecDepth 20000 in
theorem mmBodyM_run8 {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmBodyM8 (M, f)).1 = memStore32 M (f a3 + 0xFFFFFFFC)
        (mmCols (memLoad32 M (f (26 : Fin 32) + 0)) (memLoad32 M (f (9 : Fin 32) + 0)) (memLoad32 M (f a3 + 0))
          (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2) (f (24 : Fin 32))).1 ∧
    (runBlock mmBodyM8 (M, f)).2 a2 = (mmCols (memLoad32 M (f (26 : Fin 32) + 0)) (memLoad32 M (f (9 : Fin 32) + 0))
        (memLoad32 M (f a3 + 0)) (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2) (f (24 : Fin 32))).2.1 ∧
    (runBlock mmBodyM8 (M, f)).2 (24 : Fin 32) = (mmCols (memLoad32 M (f (26 : Fin 32) + 0))
        (memLoad32 M (f (9 : Fin 32) + 0)) (memLoad32 M (f a3 + 0)) (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2)
        (f (24 : Fin 32))).2.2 ∧
    (runBlock mmBodyM8 (M, f)).2 (26 : Fin 32) = f (26 : Fin 32) + 4 ∧
    (runBlock mmBodyM8 (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock mmBodyM8 (M, f)).2 a3 = f a3 + 4 ∧
    (runBlock mmBodyM8 (M, f)).2 (25 : Fin 32) = f (25 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (26 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a3 → q ≠ a2 → q ≠ (24 : Fin 32) → q ≠ (25 : Fin 32) →
      q ≠ a4 → q ≠ a5 → q ≠ a0 → q ≠ (8 : Fin 32) → q ≠ a1 → (runBlock mmBodyM8 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmBody]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q q26 q9 q13 q12 q24 q25 q14 q15 q10 q8 q11 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q26, q9, q13, q12, q24, q25, q14, q15, q10, q8, q11]

theorem mmBodyM_ok8 {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hn : (f (26 : Fin 32) + 0).toNat % 4 = 0) (hy : (f (9 : Fin 32) + 0).toNat % 4 = 0)
    (ho : (f a3 + 0).toNat % 4 = 0) (hs : (f a3 + 0xFFFFFFFC).toNat % 4 = 0)
    (hsep : Sep (f a3 + 0xFFFFFFFC) 4 base len) : BlockOk base len mmBodyM8 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmBody, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hn, hy, ho, hs, hsep⟩

theorem cnt7_dec : ∀ k : Nat, k < 7 → BitVec.ofNat 32 (7 - k) + 0xFFFFFFFF = BitVec.ofNat 32 (7 - (k + 1)) := by
  decide

theorem cnt7_ne : ∀ k : Nat, k < 7 → (BitVec.ofNat 32 (7 - (k + 1)) != 0) = decide (k + 1 < 7) := by decide

/-- The registers the loop body leaves alone. -/
def bodyKeep8 (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26]

/-- **One pass of the inner loop**, from 0x9C: column `k + 1` of a pass,
which stores the accumulator's word `k`. -/
theorem mm_iter8 {M : Word → BitVec 8} {B np yp acc U X CL CH : Word} {n : Machine} {k : Nat}
    (s : St M B n 0x9C (reg n)) (hc : CodeIn M B mulMont8Code) (hk : k < 7)
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hS : Sep (acc + BitVec.ofNat 32 (4 * k)) 4 B mulMont8Code.length)
    (r26 : reg n (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)))
    (r9 : reg n (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 1)))
    (ra3 : reg n a3 = acc + BitVec.ofNat 32 (4 * (k + 1)))
    (r31 : reg n (31 : Fin 32) = U) (r30 : reg n (30 : Fin 32) = X) (ra2 : reg n a2 = CL)
    (r24 : reg n (24 : Fin 32) = CH) (r25 : reg n (25 : Fin 32) = BitVec.ofNat 32 (7 - k)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (acc + BitVec.ofNat 32 (4 * k))
        (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1))))
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) U X CL CH).1)
        B n' (if k + 1 < 7 then 0x9C else 0xEA) (reg n') ∧
      reg n' a2 = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n' (24 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n' (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a3 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (25 : Fin 32) = BitVec.ofNat 32 (7 - (k + 1)) ∧
      ∀ q, bodyKeep8 q = true → reg n' q = reg n q := by
  have hz := s.zero
  have ok := mmBodyM_ok8 (M := M) (f := reg n) (base := B) (len := mulMont8Code.length)
    (by rw [r26, add_lit_zero]; exact aligned_add hnp (by omega))
    (by rw [r9, add_lit_zero]; exact aligned_add hyp (by omega))
    (by rw [ra3, add_lit_zero]; exact aligned_add hacc (by omega))
    (by rw [ra3, back4 acc k]; exact aligned_add hacc (by omega))
    (by rw [ra3, back4 acc k]; exact hS)
  obtain ⟨n1, c1, u1⟩ := St.block mmBodyM8 s hc mmBodyM_end8 ok
  obtain ⟨em, e2, e24, e26, e9, e3, e25, fr⟩ := mmBodyM_run8 (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em, r26, r9, ra3, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero, back4 acc k] at u1'
  have g : ∀ q, reg n1 q = (runBlock mmBodyM8 (M, reg n)).2 q := u1.regs
  have hb : branchTaken .bne (reg n1 (25 : Fin 32)) (reg n1 x0) = decide (k + 1 < 7) := by
    rw [g, e25, r25, cnt7_dec k hk, u1'.zero]; exact cnt7_ne k hk
  have hc1 := CodeIn.store32 (v := (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
    (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
    U X CL CH).1) hc hS
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a2 = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n2 (24 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n2 (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 a3 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 (25 : Fin 32) = BitVec.ofNat 32 (7 - (k + 1)) ∧
      ∀ q, bodyKeep8 q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h2, g, e2, r26, r9, ra3, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e24, r26, r9, ra3, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e26, r26, ptr4]
    · rw [h2, g, e9, r9, ptr4]
    · rw [h2, g, e3, ra3, ptr4]
    · rw [h2, g, e25, r25, cnt7_dec k hk]
    · rw [h2, g]
      exact fr q (pkeep_ne (r := 26) hq rfl) (pkeep_ne (r := 9) hq rfl) (pkeep_ne (r := a3) hq rfl)
        (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := 24) hq rfl) (pkeep_ne (r := 25) hq rfl)
        (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := a0) hq rfl)
        (pkeep_ne (r := 8) hq rfl) (pkeep_ne (r := a1) hq rfl)
  by_cases hl : k + 1 < 7
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x9C mm8_at_e6 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0xEA mm8_at_e6 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- What one inner-loop pass does to the pass's sum: column `k + 1` moves
from the inputs into the stored words and the carry. -/
theorem mm_inv_step8 {M M0 : Word → BitVec 8} {acc yp np U X CL CH lo cl ch : Word} {k : Nat} (hk : k < 7)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAY : Sep acc 32 yp 32) (hAN : Sep acc 32 np 32)
    (hfr : ∀ a, Sep acc 32 a 1 → M a = M0 a)
    (hab : ∀ i, k ≤ i → i < 8 →
      memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
    (hinv : 2 ^ 32 * accV M acc k + (CL.toNat + 2 ^ 32 * CH.toNat) * 2 ^ (32 * (k + 1)) =
      X.toNat * accV M0 yp (k + 1) + accV M0 acc (k + 1) + U.toNat * accV M0 np (k + 1))
    (hbd : CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2)
    (hcol : mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1))))
      (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) U X CL CH = (lo, cl, ch)) :
    2 ^ 32 * accV (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo) acc (k + 1) +
        (cl.toNat + 2 ^ 32 * ch.toNat) * 2 ^ (32 * (k + 2)) =
      X.toNat * accV M0 yp (k + 2) + accV M0 acc (k + 2) + U.toNat * accV M0 np (k + 2) ∧
    cl.toNat + 2 ^ 32 * ch.toNat ≤ 2 * 2 ^ 32 - 2 ∧
    (∀ a, Sep acc 32 a 1 → memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo a = M0 a) ∧
    (∀ i, k + 1 ≤ i → i < 8 → memLoad32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo)
      (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) := by
  have st := mm_step (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1))))
    (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) U X CL CH hbd
  rw [hcol] at st
  obtain ⟨st, bd⟩ := st
  rw [load_frame hfr (hAN.subR (by omega)), load_frame hfr (hAY.subR (by omega)), hab (k + 1) (by omega) (by omega)] at st
  refine ⟨?_, bd, fun a ha => ?_, fun i hi1 hi2 => ?_⟩
  · have hA : accV (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo) acc (k + 1) = accV M acc k + lo.toNat * 2 ^ (32 * k) := by
      show accV _ acc k + _ = _
      rw [accV_store_above (by omega) k (Nat.le_refl k), memLoad32_store32_same]
    rw [hA, show k + 2 = (k + 1) + 1 from rfl, pow32_succ (k + 1), pow32_succ k]
    show _ = X.toNat * (accV M0 yp (k + 1) + _ * 2 ^ (32 * (k + 1))) + (accV M0 acc (k + 1) + _ * 2 ^ (32 * (k + 1))) +
      U.toNat * (accV M0 np (k + 1) + _ * 2 ^ (32 * (k + 1)))
    rw [pow32_succ k] at hinv ⊢
    exact mm_inner_arith hinv (by simp only at st; omega)
  · rw [memStore32_ne fun j hj e => (ha.point (i := 4 * k + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm), hfr a ha]
  · rw [memLoad32_store32_sep (sep_offsets acc (.inl (by omega)) (by omega) (by omega)), hab i (by omega) hi2]

/-- **The inner loop**, from column `k + 1` of a pass to its end at 0xEA:
columns `k + 1..11` of the pass. -/
theorem mm_inner8 {B acc yp np U X : Word} {M0 : Word → BitVec 8}
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0) (hw : acc.toNat + 32 ≤ 2 ^ 32)
    (hAY : Sep acc 32 yp 32) (hAN : Sep acc 32 np 32) (hAC : Sep acc 32 B mulMont8Code.length) :
    ∀ m k, k + m + 1 = 7 → ∀ {M : Word → BitVec 8} {n : Machine} {CL CH : Word},
      St M B n 0x9C (reg n) → CodeIn M B mulMont8Code →
      (∀ a, Sep acc 32 a 1 → M a = M0 a) →
      (∀ i, k ≤ i → i < 8 →
        memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) →
      2 ^ 32 * accV M acc k + (CL.toNat + 2 ^ 32 * CH.toNat) * 2 ^ (32 * (k + 1)) =
        X.toNat * accV M0 yp (k + 1) + accV M0 acc (k + 1) + U.toNat * accV M0 np (k + 1) →
      CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2 →
      reg n (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a3 = acc + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (31 : Fin 32) = U → reg n (30 : Fin 32) = X → reg n a2 = CL → reg n (24 : Fin 32) = CH →
      reg n (25 : Fin 32) = BitVec.ofNat 32 (7 - k) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0xEA (reg n') ∧ CodeIn M' B mulMont8Code ∧
        2 ^ 32 * accV M' acc 7 + ((reg n' a2).toNat + 2 ^ 32 * (reg n' (24 : Fin 32)).toNat) * 2 ^ (32 * 8) =
          X.toNat * accV M0 yp 8 + accV M0 acc 8 + U.toNat * accV M0 np 8 ∧
        (reg n' a2).toNat + 2 ^ 32 * (reg n' (24 : Fin 32)).toNat ≤ 2 * 2 ^ 32 - 2 ∧
        (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
        memLoad32 M' (acc + BitVec.ofNat 32 (4 * 7)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * 7)) ∧
        reg n' (26 : Fin 32) = np + BitVec.ofNat 32 (4 * 8) ∧
        reg n' (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * 8) ∧
        reg n' a3 = acc + BitVec.ofNat 32 (4 * 8) ∧
        reg n' (25 : Fin 32) = 0 ∧
        ∀ q, bodyKeep8 q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r26 r9 ra3 r31 r30 ra2 r24 r25
    have k10 : k = 6 := by omega
    subst k10
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (6 + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (6 + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (6 + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e2, e24, e26, e9, e3, e25, fr⟩ := mm_iter8 (k := 6) s hc (by decide) hnp hyp hacc
      (hAC.sub (by omega)) r26 r9 ra3 r31 r30 ra2 r24 r25
    rw [hcol] at u1 e2 e24
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step8 (k := 6) (by decide) hw hAY hAN hfr hab hinv hbd hcol
    refine ⟨n1, _, c1, u1, CodeIn.store32 hc (hAC.sub (by omega)), ?_, ?_, i3, i4 7 (by decide) (by decide),
      e26, e9, e3, e25, fr⟩
    · rw [e2, e24, show (8 : Nat) = 6 + 2 from rfl]; exact i1
    · rw [e2, e24]; exact i2
  | succ m ih =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r26 r9 ra3 r31 r30 ra2 r24 r25
    have hl : k + 1 < 7 := by omega
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e2, e24, e26, e9, e3, e25, fr⟩ := mm_iter8 (k := k) s hc (by omega) hnp hyp hacc
      (hAC.sub (by omega)) r26 r9 ra3 r31 r30 ra2 r24 r25
    rw [hcol] at u1 e2 e24
    rw [ite_eq_left hl] at u1
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step8 (k := k) (by omega) hw hAY hAN hfr hab hinv hbd hcol
    have k31 : reg n1 (31 : Fin 32) = U := by rw [fr _ rfl, r31]
    have k30 : reg n1 (30 : Fin 32) = X := by rw [fr _ rfl, r30]
    obtain ⟨n', M', c', u', hc', f1, f2, f3, f4, f26, f9, f3', f25, fr'⟩ :=
      ih (k + 1) (by omega) u1 (CodeIn.store32 hc (hAC.sub (by omega))) i3 i4 i1 i2 e26 e9 e3 k31 k30 e2 e24 e25
    exact ⟨n', M', c1.trans c', u', hc', f1, f2, f3, f4, f26, f9, f3', f25,
      fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- The start of a pass, from 0x52: load the first operand's limb, compute
the factor `u` and the first column's carry, and set up the inner loop. -/
def mmHeadBlock8 : List BInstr :=
  [.aluImm .sll a0 (29 : Fin 32) 2, .alu .add a0 a0 (20 : Fin 32), .lw (30 : Fin 32) a0 0,
   .alu .mul a0 (6 : Fin 32) (30 : Fin 32), .lw a1 sp 0xC, .alu .add a1 a1 a0, .alu .mul (31 : Fin 32) (19 : Fin 32) a1,
   .alu .mulhu a2 (6 : Fin 32) (30 : Fin 32), .alu .mul a3 (31 : Fin 32) (7 : Fin 32),
   .alu .mulhu (9 : Fin 32) (31 : Fin 32) (7 : Fin 32), .alu .sltu a0 a1 a0, .alu .add a0 a0 a2, .alu .add a1 a1 a3,
   .alu .add a0 a0 (9 : Fin 32), .alu .sltu a2 a1 a3, .aluImm .add (25 : Fin 32) x0 0x7, .alu .add a2 a2 a0,
   .alu .sltu a3 a0 (9 : Fin 32), .alu .sltu a0 a2 a0, .alu .add (26 : Fin 32) x0 (17 : Fin 32),
   .alu .add (24 : Fin 32) a3 a0, .alu .add a3 x0 a6, .alu .add (9 : Fin 32) x0 (21 : Fin 32)]

/-- The end of a pass, from 0xEA: add the old top carry into the last word,
store it, and count the pass. -/
def mmTailBlock8 : List BInstr :=
  [.alu .add (22 : Fin 32) (22 : Fin 32) a2, .alu .add a0 (24 : Fin 32) (28 : Fin 32), .alu .sltu a1 (22 : Fin 32) a2,
   .sw sp (22 : Fin 32) 0x28, .alu .add (22 : Fin 32) a0 a1, .aluImm .add (29 : Fin 32) (29 : Fin 32) 1,
   .aluImm .add (28 : Fin 32) x0 0]

theorem mmHeadBlock_end8 : blockEnd mulMont8Code 0x52 mmHeadBlock8 = some 0x98 := by decide

theorem mmTailBlock_end8 : blockEnd mulMont8Code 0xEA mmTailBlock8 = some 0xFE := by decide

/-- The registers the start of a pass leaves alone. -/
def headKeep8 (q : Fin 32) : Bool := q.val ∉ [9, 10, 11, 12, 13, 24, 25, 26, 30, 31]

set_option maxRecDepth 20000 in
theorem mmHeadBlock_run8 {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmHeadBlock8 (M, f)).1 = M ∧
    (runBlock mmHeadBlock8 (M, f)).2 (30 : Fin 32) =
      memLoad32 M (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0) ∧
    (runBlock mmHeadBlock8 (M, f)).2 (31 : Fin 32) = (mmHead (f (6 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (7 : Fin 32))).1 ∧
    (runBlock mmHeadBlock8 (M, f)).2 a2 = (mmHead (f (6 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (7 : Fin 32))).2.1 ∧
    (runBlock mmHeadBlock8 (M, f)).2 (24 : Fin 32) = (mmHead (f (6 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (7 : Fin 32))).2.2 ∧
    (runBlock mmHeadBlock8 (M, f)).2 (25 : Fin 32) = BitVec.ofNat 32 (7 - 0) ∧
    (runBlock mmHeadBlock8 (M, f)).2 (26 : Fin 32) = f (17 : Fin 32) ∧
    (runBlock mmHeadBlock8 (M, f)).2 a3 = f a6 ∧
    (runBlock mmHeadBlock8 (M, f)).2 (9 : Fin 32) = f (21 : Fin 32) ∧
    ∀ q, headKeep8 q = true → (runBlock mmHeadBlock8 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmHeadBlock8]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
        pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl, pkeep_ne (r := 24) hq rfl, pkeep_ne (r := 25) hq rfl,
        pkeep_ne (r := 26) hq rfl, pkeep_ne (r := 30) hq rfl, pkeep_ne (r := 31) hq rfl]

theorem mmHeadBlock_ok8 {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hx : (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0).toNat % 4 = 0)
    (hs : (f sp + 0xC).toNat % 4 = 0) : BlockOk base len mmHeadBlock8 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmHeadBlock8, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hx, hs⟩

/-- The registers the end of a pass leaves alone. -/
def tailKeep8 (q : Fin 32) : Bool := q.val ∉ [10, 11, 22, 28, 29]

set_option maxRecDepth 20000 in
theorem mmTailBlock_run8 {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmTailBlock8 (M, f)).1 = memStore32 M (f sp + 0x28) (aluEval .add (f (22 : Fin 32)) (f a2)) ∧
    (runBlock mmTailBlock8 (M, f)).2 (22 : Fin 32) = aluEval .add (aluEval .add (f (24 : Fin 32)) (f (28 : Fin 32)))
      (aluEval .sltu (aluEval .add (f (22 : Fin 32)) (f a2)) (f a2)) ∧
    (runBlock mmTailBlock8 (M, f)).2 (29 : Fin 32) = f (29 : Fin 32) + 1 ∧
    (runBlock mmTailBlock8 (M, f)).2 (28 : Fin 32) = 0 ∧
    ∀ q, tailKeep8 q = true → (runBlock mmTailBlock8 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmTailBlock8]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
        pkeep_ne (r := 22) hq rfl, pkeep_ne (r := 28) hq rfl, pkeep_ne (r := 29) hq rfl]

theorem mmTailBlock_ok8 {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hs : (f sp + 0x28).toNat % 4 = 0) (hsep : Sep (f sp + 0x28) 4 base len) :
    BlockOk base len mmTailBlock8 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmTailBlock8, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hs, hsep⟩

theorem sll8 : ∀ i : Nat, i < 8 → aluEval .sll (BitVec.ofNat 32 i) 2 = BitVec.ofNat 32 (4 * i) := by decide

theorem pass_ne8 : ∀ i : Nat, i < 8 → (BitVec.ofNat 32 (i + 1) != 8) = decide (i + 1 < 8) := by decide

/-- The registers a pass leaves alone. -/
def passKeep8 (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 22, 24, 25, 26, 28, 29, 30, 31]

theorem passKeep_head8 : ∀ q, passKeep8 q = true → headKeep8 q = true := by decide

theorem passKeep_body8 : ∀ q, passKeep8 q = true → bodyKeep8 q = true := by decide

theorem passKeep_tail8 : ∀ q, passKeep8 q = true → tailKeep8 q = true := by decide

theorem accV_frame32 {M M0 : Word → BitVec 8} {acc b : Word} {n : Nat} (hf : ∀ a, Sep acc 32 a 1 → M a = M0 a)
    (hs : Sep acc 32 b (4 * n)) : accV M b n = accV M0 b n :=
  accV_congr n fun l hl => load_frame hf (hs.subR (by omega))

/-- **One pass of the outer loop**, from 0x52: add limb `i` of the first
operand times the second operand, and `u` times the modulus, to the
accumulator and its top carry in `s6`, and shift the sum down a word. -/
theorem mm_pass8 {B acc xp yp np K : Word} {M0 : Word → BitVec 8} {i : Nat} (hi : i < 8)
    (hxp : xp.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAX : Sep acc 32 xp 32) (hAY : Sep acc 32 yp 32) (hAN : Sep acc 32 np 32)
    (hAC : Sep acc 32 B mulMont8Code.length)
    (hk : (K.toNat * (memLoad32 M0 np).toNat + 1) % 2 ^ 32 = 0)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x52 (reg n)) (hc : CodeIn M B mulMont8Code)
    (hfr : ∀ a, Sep acc 32 a 1 → M a = M0 a)
    (r29 : reg n (29 : Fin 32) = BitVec.ofNat 32 i) (r20 : reg n (20 : Fin 32) = xp)
    (r6 : reg n (6 : Fin 32) = memLoad32 M0 yp) (r7 : reg n (7 : Fin 32) = memLoad32 M0 np)
    (r19 : reg n (19 : Fin 32) = K) (rsp : reg n sp + 0xC = acc)
    (rsp38 : reg n sp + 0x28 = acc + BitVec.ofNat 32 (4 * 7))
    (r17 : reg n (17 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)))
    (r16 : reg n a6 = acc + BitVec.ofNat 32 (4 * (0 + 1)))
    (r21 : reg n (21 : Fin 32) = yp + BitVec.ofNat 32 (4 * (0 + 1)))
    (r28 : reg n (28 : Fin 32) = 0) (r5 : reg n (5 : Fin 32) = 8) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 8 then 0x52 else 0x102) (reg n') ∧ CodeIn M' B mulMont8Code ∧
      (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
      (∃ u : Nat, u < 2 ^ 32 ∧ 2 ^ 32 * (accV M' acc 8 + (reg n' (22 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M acc 8 + (reg n (22 : Fin 32)).toNat * 2 ^ (32 * 8) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 yp 8 + u * accV M0 np 8) ∧
      reg n' (29 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ reg n' (28 : Fin 32) = 0 ∧
      ∀ q, passKeep8 q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hX : aluEval .add (aluEval .sll (reg n (29 : Fin 32)) 2) (reg n (20 : Fin 32)) + 0 =
      xp + BitVec.ofNat 32 (4 * i) := by
    rw [r29, r20, sll8 i hi, add_lit_zero]; exact BitVec.add_comm _ _
  have ok1 := mmHeadBlock_ok8 (M := M) (f := reg n) (base := B) (len := mulMont8Code.length)
    (by rw [hX]; exact aligned_add hxp (by omega)) (by rw [rsp]; exact hacc)
  obtain ⟨n1, c1, u1⟩ := St.block mmHeadBlock8 s hc mmHeadBlock_end8 ok1
  obtain ⟨hm1, h30, h31, h2, h24, h25, h26, h3, h9, hfr1⟩ := mmHeadBlock_run8 (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [hm1] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock mmHeadBlock8 (M, reg n)).2 q := u1.regs
  rw [hX] at h30 h31 h2 h24
  rw [rsp, r6, r19, r7] at h31 h2 h24
  have eX : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
    load_frame hfr (hAX.subR (by omega))
  obtain ⟨u, cl, ch, hH⟩ : ∃ u cl ch, mmHead (memLoad32 M0 yp) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
      (memLoad32 M acc) K (memLoad32 M0 np) = (u, cl, ch) := ⟨_, _, _, rfl⟩
  have hd := mm_head (memLoad32 M0 yp) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) (memLoad32 M acc) K
    (memLoad32 M0 np) hk
  rw [hH] at hd h31 h2 h24
  simp only at hd h31 h2 h24
  obtain ⟨hd, bd⟩ := hd
  have hb : branchTaken .beq (reg n1 (25 : Fin 32)) (reg n1 x0) = false := by
    rw [g1, h25, u1'.zero]; decide
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 0x9C mm8_at_98 (by decide) hb
  have g2 : ∀ q, reg n2 q = (runBlock mmHeadBlock8 (M, reg n)).2 q := fun q => by rw [u2.regs, g1]
  have eY0 : memLoad32 M (yp + BitVec.ofNat 32 (4 * 0)) = memLoad32 M0 yp := by
    rw [load_frame hfr (hAY.subR (c := 4 * 0) (l := 4) (by omega)), Nat.mul_zero, add_ofNat_zero]
  have eN0 : memLoad32 M (np + BitVec.ofNat 32 (4 * 0)) = memLoad32 M0 np := by
    rw [load_frame hfr (hAN.subR (c := 4 * 0) (l := 4) (by omega)), Nat.mul_zero, add_ofNat_zero]
  have eO0 : memLoad32 M (acc + BitVec.ofNat 32 (4 * 0)) = memLoad32 M acc := by
    rw [Nat.mul_zero, add_ofNat_zero]
  have inv0 : 2 ^ 32 * accV M acc 0 + (cl.toNat + 2 ^ 32 * ch.toNat) * 2 ^ (32 * (0 + 1)) =
      (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M yp (0 + 1) + accV M acc (0 + 1) +
        u.toNat * accV M np (0 + 1) := by
    show 2 ^ 32 * 0 + _ * 2 ^ 32 = _ * (0 + (memLoad32 M (yp + BitVec.ofNat 32 (4 * 0))).toNat * 1) +
      (0 + (memLoad32 M (acc + BitVec.ofNat 32 (4 * 0))).toNat * 1) +
      _ * (0 + (memLoad32 M (np + BitVec.ofNat 32 (4 * 0))).toNat * 1)
    rw [eY0, eN0, eO0]
    simp only [Nat.zero_add, Nat.mul_one, Nat.mul_zero]
    omega
  obtain ⟨n3, M1, c3, u3, hc3, I1, I2, I3, I4, f26, f9, f3, f25, fr3⟩ :=
    mm_inner8 (M0 := M) (U := u) (X := memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) hnp hyp hacc hw hAY hAN hAC
      6 0 (by decide) u2.self hc (fun _ _ => rfl) (fun _ _ _ => rfl) inv0 bd
      (by rw [g2, h26, r17]) (by rw [g2, h9, r21]) (by rw [g2, h3, r16]) (by rw [g2, h31]) (by rw [g2, h30])
      (by rw [g2, h2]) (by rw [g2, h24]) (by rw [g2, h25])
  have k3 : ∀ q, passKeep8 q = true → reg n3 q = reg n q := fun q hq => by
    rw [fr3 q (passKeep_body8 q hq), g2, hfr1 q (passKeep_head8 q hq)]
  have hb3 : ∀ q, headKeep8 q = true → bodyKeep8 q = true → reg n3 q = reg n q := fun q h1 h2 => by
    rw [fr3 q h2, g2, hfr1 q h1]
  have sp3 : reg n3 sp = reg n sp := k3 sp rfl
  have ok3 := mmTailBlock_ok8 (M := M1) (f := reg n3) (base := B) (len := mulMont8Code.length)
    (by rw [sp3, rsp38]; exact aligned_add hacc (by omega)) (by rw [sp3, rsp38]; exact hAC.sub (by omega))
  obtain ⟨n4, c4, u4⟩ := St.block mmTailBlock8 u3 hc3 mmTailBlock_end8 ok3
  obtain ⟨hm4, t22, t29, t28, tfr⟩ := mmTailBlock_run8 (M := M1) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [hm4, sp3, rsp38] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock mmTailBlock8 (M1, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)) hc3 (hAC.sub (c := 4 * 7) (by omega))
  have e29 : reg n4 (29 : Fin 32) = BitVec.ofNat 32 (i + 1) := by
    rw [g4, t29, hb3 (29 : Fin 32) rfl rfl, r29, ofNat_succ]
  have e28 : reg n4 (28 : Fin 32) = 0 := by rw [g4, t28]
  have k4 : ∀ q, passKeep8 q = true → reg n4 q = reg n q := fun q hq => by
    rw [g4, tfr q (passKeep_tail8 q hq), k3 q hq]
  have hb4 : branchTaken .bne (reg n4 (29 : Fin 32)) (reg n4 (5 : Fin 32)) = decide (i + 1 < 8) := by
    rw [e29, k4 _ rfl, r5]; exact pass_ne8 i hi
  -- the arithmetic of the pass
  have arith : 2 ^ 32 * (accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7))
        (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2))) acc 8 + (reg n4 (22 : Fin 32)).toNat * 2 ^ (32 * 8)) =
      accV M acc 8 + (reg n (22 : Fin 32)).toNat * 2 ^ (32 * 8) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 yp 8 + u.toNat * accV M0 np 8 := by
    have hA : accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7)) (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)))
        acc 8 = accV M1 acc 7 + (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)).toNat * 2 ^ (32 * 7) := by
      rw [show (8 : Nat) = 7 + 1 from rfl, accV_succ1, accV_store_above (by omega) 7 (Nat.le_refl 7),
        memLoad32_store32_same]
    have ac := add_carry (reg n3 (22 : Fin 32)) (reg n3 a2)
    have hch : (reg n3 (24 : Fin 32)).toNat ≤ 1 := by omega
    have hcy : (aluEval .sltu (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)) (reg n3 a2)).toNat ≤ 1 := by
      have := (reg n3 (22 : Fin 32)).isLt; have := (reg n3 a2).isLt; omega
    have h22 : (reg n4 (22 : Fin 32)).toNat = (reg n3 (24 : Fin 32)).toNat +
        (aluEval .sltu (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)) (reg n3 a2)).toNat := by
      rw [g4, t22, hb3 (28 : Fin 32) rfl rfl, r28, show aluEval .add (reg n3 (24 : Fin 32)) 0 = reg n3 (24 : Fin 32) from
        BitVec.add_zero _, add_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    have p12 : (2 : Nat) ^ (32 * 8) = 2 ^ (32 * 7) * 2 ^ 32 := pow32_succ 7
    rw [eX, accV_frame32 (b := yp) (n := 8) hfr hAY, accV_frame32 (b := np) (n := 8) hfr hAN, p12] at I1
    rw [hA, h22, p12, hb3 (22 : Fin 32) rfl rfl]
    rw [hb3 (22 : Fin 32) rfl rfl] at ac
    exact mm_tail_arith I1 ac
  have fr4 : ∀ a, Sep acc 32 a 1 → memStore32 M1 (acc + BitVec.ofNat 32 (4 * 7))
      (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)) a = M0 a := fun a ha => by
    rw [memStore32_ne fun j hj e => (ha.point (i := 4 * 7 + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm), I3 a ha, hfr a ha]
  by_cases hl : i + 1 < 8
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x52 mm8_at_fe (by decide) (by rw [hb4]; exact decide_eq_true hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e29], by rw [g5, e28], fun q hq => by rw [g5, k4 q hq]⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x102 mm8_at_fe (by decide) (by rw [hb4]; exact decide_eq_false hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e29], by rw [g5, e28], fun q hq => by rw [g5, k4 q hq]⟩

/-- **The outer loop**, from pass `i` to its end at 0x102. The accumulator
and its top carry hold a sum `T` with `2^(32 i) T = X_i Y + U N`, for `X_i`
the first operand's low `i` limbs and some `U`, and `T < 2N`. -/
theorem mm_outer8 {B acc xp yp np K : Word} {M0 : Word → BitVec 8}
    (hxp : xp.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 32 ≤ 2 ^ 32) (hAX : Sep acc 32 xp 32) (hAY : Sep acc 32 yp 32) (hAN : Sep acc 32 np 32)
    (hAC : Sep acc 32 B mulMont8Code.length)
    (hk : (K.toNat * (memLoad32 M0 np).toNat + 1) % 2 ^ 32 = 0) (hYN : accV M0 yp 8 < accV M0 np 8) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x52 (reg n) → CodeIn M B mulMont8Code → (∀ a, Sep acc 32 a 1 → M a = M0 a) →
      (∃ U, 2 ^ (32 * i) * (accV M acc 8 + (reg n (22 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M0 xp i * accV M0 yp 8 + U * accV M0 np 8) →
      accV M acc 8 + (reg n (22 : Fin 32)).toNat * 2 ^ (32 * 8) < 2 * accV M0 np 8 →
      reg n (29 : Fin 32) = BitVec.ofNat 32 i → reg n (20 : Fin 32) = xp →
      reg n (6 : Fin 32) = memLoad32 M0 yp → reg n (7 : Fin 32) = memLoad32 M0 np →
      reg n (19 : Fin 32) = K → reg n sp + 0xC = acc →
      reg n sp + 0x28 = acc + BitVec.ofNat 32 (4 * 7) →
      reg n (17 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n a6 = acc + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (21 : Fin 32) = yp + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (28 : Fin 32) = 0 → reg n (5 : Fin 32) = 8 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0x102 (reg n') ∧ CodeIn M' B mulMont8Code ∧
        (∀ a, Sep acc 32 a 1 → M' a = M0 a) ∧
        (∃ U, 2 ^ (32 * 8) * (accV M' acc 8 + (reg n' (22 : Fin 32)).toNat * 2 ^ (32 * 8)) =
          accV M0 xp 8 * accV M0 yp 8 + U * accV M0 np 8) ∧
        accV M' acc 8 + (reg n' (22 : Fin 32)).toNat * 2 ^ (32 * 8) < 2 * accV M0 np 8 ∧
        ∀ q, passKeep8 q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hinv hbd r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    have i11 : i = 7 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e29, e28, k1⟩ := mm_pass8 (i := 7) (by decide) hxp hyp hnp hacc
      hw hAX hAY hAN hAC hk s hc hfr r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * 7))).isLt hu hYN
    refine ⟨n1, M1, c1, u1, hc1, hf1, ⟨U + 2 ^ (32 * 7) * u, ?_⟩, a2, k1⟩
    rw [pow32_succ 7] at a1 ⊢
    rw [a1, accV_succ1 M0 xp 7]
  | succ m ih =>
    intro i hi M n s hc hfr hinv hbd r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    have hl : i + 1 < 8 := idx_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e29, e28, k1⟩ := mm_pass8 (i := i) (Nat.lt_trans (Nat.lt_succ_self i) hl) hxp hyp hnp hacc
      hw hAX hAY hAN hAC hk s hc hfr r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    rw [ite_eq_left hl] at u1
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).isLt hu hYN
    have inv1 : ∃ U, 2 ^ (32 * (i + 1)) * (accV M1 acc 8 + (reg n1 (22 : Fin 32)).toNat * 2 ^ (32 * 8)) =
        accV M0 xp (i + 1) * accV M0 yp 8 + U * accV M0 np 8 :=
      ⟨U + 2 ^ (32 * i) * u, by rw [pow32_succ i, a1, accV_succ1 M0 xp i]⟩
    obtain ⟨n', M', c', u', hc', hf', hv', hb', k'⟩ := ih (i + 1) (idx_succ hi) u1 hc1 hf1 inv1 a2 e29
      (by rw [k1 _ rfl, r20]) (by rw [k1 _ rfl, r6]) (by rw [k1 _ rfl, r7]) (by rw [k1 _ rfl, r19])
      (by rw [k1 _ rfl, rsp]) (by rw [k1 _ rfl, rsp38]) (by rw [k1 _ rfl, r17]) (by rw [k1 _ rfl, r16])
      (by rw [k1 _ rfl, r21]) e28 (by rw [k1 _ rfl, r5])
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', hb', fun q hq => by rw [k' q hq, k1 q hq]⟩

/-- What `mul_montgomery_form::<8>` saves in its frame, at offsets from its
`sp`. -/
abbrev mmPs8 : List (Fin 32 × Word) :=
  [(ra, 0x7C), ((8 : Fin 32), 0x78), ((9 : Fin 32), 0x74), ((18 : Fin 32), 0x70), ((19 : Fin 32), 0x6C),
   ((20 : Fin 32), 0x68), ((21 : Fin 32), 0x64), ((22 : Fin 32), 0x60), ((23 : Fin 32), 0x5C),
   ((24 : Fin 32), 0x58), ((25 : Fin 32), 0x54), ((26 : Fin 32), 0x50)]

theorem mmSave_end8 : blockEnd mulMont8Code 2 (saveBlock mmPs8) = some 0x1A := by decide

theorem mmSetup_end8 : blockEnd mulMont8Code 0x34 mmSetup = some 0x4C := by decide

theorem mmRestore_end8 : blockEnd mulMont8Code 0x172 (restoreBlock mmPs8) = some 0x18A := by decide

theorem subTail_end8 : blockEnd mulMont8Code 0x12C subTail = some 0x13A := by decide

/-- `borrowing_sub`'s offset from `mul_montgomery_form::<8>`. -/
abbrev mmBsub8 (P : Word) : Word := P + 0xFFFF17E2

/-- **One round of the final subtraction**, from 0x11E: subtract limb `i` of
the modulus and the borrow from limb `i` of the accumulator, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem sub_iter8 {M : Word → BitVec 8} {P F acc np D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x11E (reg n)) (hc : CodeIn M P mulMont8Code) (hb : CodeIn M (mmBsub8 P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 8) (hF : F.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (mmBsub8 P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P mulMont8Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P mulMont8Code.length)
    (rsp : reg n sp = F) (r9 : reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i))
    (r23 : reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i)) (r19 : reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (r8 : reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 8 then 0x11E else 0x13C) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc mm8_at_11e (off' := 0x120) (by decide)
    (by rw [r9, add_lit_zero]; exact aligned_add hacc (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc mm8_at_120 (off' := 0x124) (by decide)
    (by rw [upd_ne (by decide) (by decide), r23, add_lit_zero]; exact aligned_add hnp (by omega))
  rw [r9, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (23 : Fin 32) + 0)) a0 =
      memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (23 : Fin 32) + 0)) a1 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [r23, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFF17E2 (by decide))
    mm8_at_124 mm8_at_128 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x124 + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P mulMont8Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have e19 : reg n3 (19 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block subTail u3 hc3 subTail_end8
    (subTail_ok (by rw [e19]; exact aligned_add hD (by omega)) (by rw [e19]; exact sDC))
  obtain ⟨em4, t2, t9, t23, t19, t8, tk⟩ := subTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, e19, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock subTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have e8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
    rw [g4, t8, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, cnt8_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (8 : Fin 32)) (reg n4 x0) = decide (i + 1 < 8) := by
    rw [e8, u4'.zero]; exact cnt8_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, e8], fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => ?_⟩
    · rw [h5, g4, t9, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, ptr4]
    · rw [h5, g4, t23, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r23, ptr4]
    · rw [h5, g4, t19, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, ptr4]
    · rw [h5, g4, tk q q2 q9 q23 q19 q8, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 8
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x11E mm8_at_13a (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x13C mm8_at_13a (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

theorem sub_loop8 {P F acc np D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hacc : acc.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 32 ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 acc 32) (sFN : Sep (F + 0xFFFFFFFC) 4 np 32) (sFD : Sep (F + 0xFFFFFFFC) 4 D 32)
    (sDA : Sep D 32 acc 32) (sDN : Sep D 32 np 32)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (mmBsub8 P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P mulMont8Code.length)
    (sDB : Sep D 32 (mmBsub8 P) borrowingSubCode.length) (sDC : Sep D 32 P mulMont8Code.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x11E (reg n) → CodeIn M P mulMont8Code → CodeIn M (mmBsub8 P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x13C (reg n') ∧ CodeIn M' P mulMont8Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc 8 + 2 ^ (32 * 8) * maskBit (reg n' a2) = accV M0 np 8 + accV M' D 8 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) →
          q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x11E (reg n) → CodeIn M P mulMont8Code → CodeIn M (mmBsub8 P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (8 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 8 then 0x11E else 0x13C) (reg n') ∧
        CodeIn M' P mulMont8Code ∧ CodeIn M' (mmBsub8 P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 32 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 np (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) →
          q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, e9, e23, e19, e8, fr⟩ := sub_iter8 (i := i) s hc hb hP hi hF hacc hnp hD
      sFB sFC (sDC.sub (by omega)) rsp r9 r23 r19 r8 ra2
    have eA : memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFA.subR (by omega)) (sDA.subR (by omega))
    have eN : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (mmBsub8 P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P mulMont8Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, e9, e23, e19, e8, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have i11 : i = 7 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 7 (by decide) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have hl : i + 1 < 8 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e9, e23, e19, e8, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 e9 e23 e19 e8 rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q9 q23 q19 q8, fr q q0 q1 q2 q3 q4 qr q9 q23 q19 q8]⟩

/-- From 0x13C: spill the top carry, and choose the accumulator when the
top carry is zero and the subtraction borrowed, through a byte of the
frame; then set up the call to `borrowing_sub` whose result goes unused. -/
def mmChoice8 : List BInstr :=
  [.sw sp (22 : Fin 32) 0x4C, .aluImm .add a0 sp 0x4C, .lw a0 sp 0x4C, .aluImm .sltu (9 : Fin 32) a0 1,
   .alu .and (9 : Fin 32) (9 : Fin 32) a2, .sb sp (9 : Fin 32) 0x4C, .aluImm .add a0 sp 0x4C, .lbu a0 sp 0x4C,
   .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a2 a2 a0, .alu .add a0 x0 (22 : Fin 32), .aluImm .add a1 x0 0]

/-- From 0x162: the arguments of `Uint<8>::select`. -/
def mmSelArgs8 : List BInstr :=
  [.aluImm .add a1 sp 0x2C, .aluImm .add a2 sp 0xC, .alu .add a0 x0 (18 : Fin 32), .alu .add a3 x0 (9 : Fin 32)]

/-- From 0x102: the arguments of the `memset` that zeroes the difference
buffer, which `s3` also points at. -/
def mmSubPre8 : List BInstr :=
  [.aluImm .add a0 sp 0x2C, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0, .aluImm .add (19 : Fin 32) sp 0x2C]

/-- From 0x116: the borrow, the accumulator pointer, and the count. -/
def mmSubInit8 : List BInstr :=
  [.aluImm .add a2 x0 0, .aluImm .add (9 : Fin 32) sp 0xC, .aluImm .add (8 : Fin 32) x0 0x8]

/-- From 0x1A: keep the arguments, and set up the `memset` that zeroes the
accumulator. -/
def mmPro8 : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a4, .alu .add (23 : Fin 32) x0 a3, .alu .add (21 : Fin 32) x0 a2,
   .alu .add (20 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0x20,
   .aluImm .add a1 x0 0]

theorem mmChoice_end8 : blockEnd mulMont8Code 0x13C mmChoice8 = some 0x15A := by decide

theorem mmSelArgs_end8 : blockEnd mulMont8Code 0x162 mmSelArgs8 = some 0x16A := by decide

theorem mmSubPre_end8 : blockEnd mulMont8Code 0x102 mmSubPre8 = some 0x10E := by decide

theorem mmSubInit_end8 : blockEnd mulMont8Code 0x116 mmSubInit8 = some 0x11C := by decide

theorem mmPro_end8 : blockEnd mulMont8Code 0x1A mmPro8 = some 0x2C := by decide

/-- The choice `mul_montgomery_form` passes to `Uint<8>::select`. -/
theorem choice_val8 (mc b : Word) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    aluEval .and (aluEval .sltu mc 1) b = if mc.toNat = 0 ∧ maskBit b = 1 then 1 else 0 := by
  have hs : aluEval .sltu mc 1 = if mc.toNat = 0 then 1 else 0 := by
    show (if mc.ult 1 then 1 else 0 : Word) = _
    by_cases h : mc.toNat = 0
    · rw [ite_eq_left h, ite_eq_left (show mc.ult 1 = true from by
        show decide (mc.toNat < (1 : Word).toNat) = true; rw [h]; rfl)]
    · rw [ite_eq_right h, ite_eq_right (show ¬ mc.ult 1 = true from by
        show ¬ decide (mc.toNat < (1 : Word).toNat) = true
        rw [show (1 : Word).toNat = 1 from rfl]
        exact fun e => h (by have := of_decide_eq_true e; omega))]
  rw [hs]
  rcases hb with rfl | rfl
  · rw [show maskBit 0 = 0 from rfl]
    by_cases h : mc.toNat = 0
    · rw [ite_eq_left h, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (by omega)]; rfl
  · rw [show maskBit 0xFFFFFFFF = 1 from rfl]
    by_cases h : mc.toNat = 0
    · rw [ite_eq_left h, ite_eq_left ⟨h, rfl⟩]; rfl
    · rw [ite_eq_right h, ite_eq_right (fun e => h e.1)]; rfl

set_option maxRecDepth 20000 in
theorem mmChoice_run8 {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmChoice8 (M, f)).1 = memStore8 (memStore32 M (f sp + 0x4C) (f (22 : Fin 32))) (f sp + 0x4C)
      ((aluEval .and (aluEval .sltu (f (22 : Fin 32)) 1) (f a2)).extractLsb' 0 8) ∧
    (runBlock mmChoice8 (M, f)).2 (9 : Fin 32) = aluEval .and (aluEval .sltu (f (22 : Fin 32)) 1) (f a2) ∧
    (runBlock mmChoice8 (M, f)).2 a0 = f (22 : Fin 32) ∧ (runBlock mmChoice8 (M, f)).2 a1 = 0 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (9 : Fin 32) → (runBlock mmChoice8 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmChoice8]
  refine ⟨?_, ?_, ?_, ?_, fun q q0 q1 q2 q9 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rw [memLoad32_store32_same]
  · simp +decide only [upd, ↓reduceIte]; rw [memLoad32_store32_same]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q9]

theorem mmChoice_ok8 {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f sp + 0x4C).toNat % 4 = 0) (hs : Sep (f sp + 0x4C) 4 base len) : BlockOk base len mmChoice8 (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmChoice8, upd, ↓reduceIte, and_true, true_and]
  exact ⟨⟨h, hs⟩, h, hs.sub (c := 0) (l := 1) (by decide) |> fun h' => by rwa [add_ofNat_zero] at h'⟩

theorem mmSelArgs_run8 {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmSelArgs8 (M, f)).1 = M ∧ (runBlock mmSelArgs8 (M, f)).2 a1 = f sp + 0x2C ∧
    (runBlock mmSelArgs8 (M, f)).2 a2 = f sp + 0xC ∧ (runBlock mmSelArgs8 (M, f)).2 a0 = f (18 : Fin 32) ∧
    (runBlock mmSelArgs8 (M, f)).2 a3 = f (9 : Fin 32) ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → (runBlock mmSelArgs8 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmSelArgs8]
  refine ⟨trivial, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q3]

theorem mmSubPre_run8 {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmSubPre8 (M, f)).1 = M ∧ (runBlock mmSubPre8 (M, f)).2 a0 = f sp + 0x2C ∧
    (runBlock mmSubPre8 (M, f)).2 a2 = 0x20 ∧ (runBlock mmSubPre8 (M, f)).2 a1 = 0 ∧
    (runBlock mmSubPre8 (M, f)).2 (19 : Fin 32) = f sp + 0x2C ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (19 : Fin 32) → (runBlock mmSubPre8 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmSubPre8]
  refine ⟨trivial, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q3]

theorem mmSubInit_run8 {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmSubInit8 (M, f)).1 = M ∧ (runBlock mmSubInit8 (M, f)).2 a2 = 0 ∧
    (runBlock mmSubInit8 (M, f)).2 (9 : Fin 32) = f sp + 0xC ∧
    (runBlock mmSubInit8 (M, f)).2 (8 : Fin 32) = BitVec.ofNat 32 (8 - 0) ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → (runBlock mmSubInit8 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmSubInit8]
  refine ⟨trivial, ?_, ?_, ?_, fun q q2 q9 q8 => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q9, q8]

theorem mmPro_run8 {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmPro8 (M, f)).1 = M ∧
    (runBlock mmPro8 (M, f)).2 (19 : Fin 32) = f a4 ∧ (runBlock mmPro8 (M, f)).2 (23 : Fin 32) = f a3 ∧
    (runBlock mmPro8 (M, f)).2 (21 : Fin 32) = f a2 ∧ (runBlock mmPro8 (M, f)).2 (20 : Fin 32) = f a1 ∧
    (runBlock mmPro8 (M, f)).2 (18 : Fin 32) = f a0 ∧ (runBlock mmPro8 (M, f)).2 a0 = f sp + 0xC ∧
    (runBlock mmPro8 (M, f)).2 a2 = 0x20 ∧ (runBlock mmPro8 (M, f)).2 a1 = 0 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) →
      q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) → (runBlock mmPro8 (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmPro8]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q18 q19 q20 q21 q23 => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q18, q19, q20, q21, q23]

/-- The Montgomery result's congruence, from the sum's. -/
theorem mont_congr8 {T N XY U R : Nat} (hR : R = T % N) (h : 2 ^ 256 * T = XY + U * N) :
    R * 2 ^ 256 % N = XY % N := by
  rw [hR, Nat.mod_mul_mod, Nat.mul_comm, h, Nat.add_mul_mod_self_right]

/-- Where `mul_montgomery_form::<8>` runs: its code and its callees' at
their offsets, the 0xC0 bytes of stack below `sp0` that it, `borrowing_sub`,
and `Uint<8>::select` use, and the result and operands, aligned and apart
from what each must not touch. -/
structure MMEnv8 (M : Word → BitVec 8) (P sp0 out xp yp np : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P mulMont8Code
  mset : CodeIn M (P + 0x3CA8) memsetCode
  bsub : CodeIn M (mmBsub8 P) borrowingSubCode
  sel : CodeIn M (P + 0x18E) uintSelect8Code
  stub : CodeIn M (P + 0x3D10) memcpyStubCode
  body : CodeIn M (P + 0x3D18) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xC0 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hxp : xp.toNat % 4 = 0
  hyp : yp.toNat % 4 = 0
  hnp : np.toNat % 4 = 0
  hwo : out.toNat + 32 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF40) 0xC0 P mulMont8Code.length
  sGM : Sep (sp0 + 0xFFFFFF40) 0xC0 (P + 0x3CA8) memsetCode.length
  sGB : Sep (sp0 + 0xFFFFFF40) 0xC0 (mmBsub8 P) borrowingSubCode.length
  sGL : Sep (sp0 + 0xFFFFFF40) 0xC0 (P + 0x18E) uintSelect8Code.length
  sGU : Sep (sp0 + 0xFFFFFF40) 0xC0 (P + 0x3D10) memcpyStubCode.length
  sGY : Sep (sp0 + 0xFFFFFF40) 0xC0 (P + 0x3D18) memcpyBodyCode.length
  sOG : Sep out 32 (sp0 + 0xFFFFFF40) 0xC0
  sOC : Sep out 32 P mulMont8Code.length
  sOL : Sep out 32 (P + 0x18E) uintSelect8Code.length
  sOY : Sep out 32 (P + 0x3D18) memcpyBodyCode.length
  sXG : Sep xp 32 (sp0 + 0xFFFFFF40) 0xC0
  sYG : Sep yp 32 (sp0 + 0xFFFFFF40) 0xC0
  sNG : Sep np 32 (sp0 + 0xFFFFFF40) 0xC0

theorem frameA08 (sp0 : Word) (h : 0xC0 ≤ sp0.toNat) :
    (sp0 + 0xFFFFFF40).toNat + 0xC0 = sp0.toNat ∧ sp0 + 0xFFFFFF80 = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x40 ∧
      (sp0 + 0xFFFFFF80).toNat + 0x80 = sp0.toNat := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.toNat_add]; have : (0xFFFFFF40 : Word).toNat = 0xFFFFFF40 := rfl; rw [this]; have := sp0.isLt; omega
  · rw [BitVec.add_assoc]; rfl
  · rw [BitVec.toNat_add]; have : (0xFFFFFF80 : Word).toNat = 0xFFFFFF80 := rfl; rw [this]; have := sp0.isLt; omega

/-- The frame `[F, F + 0x80)` of `mul_montgomery_form::<8>` inside its
stack region. -/
theorem MMEnv8.frame {M : Word → BitVec 8} {P sp0 out xp yp np : Word} (E : MMEnv8 M P sp0 out xp yp np)
    {b : Word} {l : Nat} (h : Sep (sp0 + 0xFFFFFF40) 0xC0 b l) : Sep (sp0 + 0xFFFFFF80) 0x80 b l := by
  rw [(frameA08 sp0 E.hS).2.1]; exact h.sub (by decide)

/-- **The prologue of `mul_montgomery_form::<8>`**, from 0 to the outer
loop at 0x52: open the frame at `F`, save registers, zero the accumulator
at `F + 0xC`, and set up the first pass. -/
theorem mm_pro8 (m : Machine) {P sp0 out xp yp np K : Word} (E : MMEnv8 m.mem P sp0 out xp yp np) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (ha2 : reg m a2 = yp) (ha3 : reg m a3 = np) (ha4 : reg m a4 = K)
    (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x52 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ mmPs8 → memLoad32 M (sp0 + 0xFFFFFF80 + o) = reg m r) ∧
      accV M (sp0 + 0xFFFFFF80 + 0xC) 8 = 0 ∧
      reg n sp = sp0 + 0xFFFFFF80 ∧ reg n (22 : Fin 32) = 0 ∧ reg n (29 : Fin 32) = BitVec.ofNat 32 0 ∧
      reg n (20 : Fin 32) = xp ∧ reg n (6 : Fin 32) = memLoad32 m.mem yp ∧
      reg n (7 : Fin 32) = memLoad32 m.mem np ∧ reg n (19 : Fin 32) = K ∧
      reg n (17 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n a6 = sp0 + 0xFFFFFF80 + 0xC + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n (21 : Fin 32) = yp + BitVec.ofNat 32 (4 * (0 + 1)) ∧ reg n (28 : Fin 32) = 0 ∧
      reg n (5 : Fin 32) = 8 ∧ reg n (18 : Fin 32) = out ∧ reg n (23 : Fin 32) = np ∧
      ∀ q, q.val ∈ [3, 4, 27] → reg n q = reg m q := by
  obtain ⟨hG, hFG, hFw⟩ := frameA08 sp0 E.hS
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hFa : (sp0 + 0xFFFFFF80).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFF80) (by decide)
  have sFC := E.frame E.sGC; have sFM := E.frame E.sGM
  obtain ⟨m1, d1, u1⟩ := s0.aluImm E.code mm8_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80) sp = sp0 + 0xFFFFFF80 := by
    simp +decide [upd, hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock mmPs8) u1 E.code mmSave_end8 (saveBlock_ok _ mmPs8 _ fun q hq => by
      rw [sp1]
      simp only [mmPs8, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hFa (by decide), sFC.sub (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF80) 0x80 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have I2 : ∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 →
      saveMem m.mem (sp0 + 0xFFFFFF80) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80)) mmPs8 x = m.mem x :=
    fun x hx => saveMem_outside mmPs8 fun q hq => by
      simp only [mmPs8, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hx.sub (by decide)
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFF80 := by rw [u2.regs]; exact sp1
  -- keep the arguments
  have hc2 := codeS E.code sFC I2
  obtain ⟨m3, c3, u3⟩ := St.block mmPro8 u2.self hc2 mmPro_end8 (by
    simp only [BlockOk, BInstr.ok, mmPro8]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial⟩)
  obtain ⟨em3, p19, p23, p21, p20, p18, pa0, pa2, pa1, pk⟩ := mmPro_run8 (M := saveMem m.mem (sp0 + 0xFFFFFF80)
    (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80)) mmPs8) (f := reg m2) u2.self.zero
  rw [em3] at u3
  have g3 : ∀ q, reg m3 q = (runBlock mmPro8 (saveMem m.mem (sp0 + 0xFFFFFF80)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80)) mmPs8, reg m2)).2 q := u3.regs
  -- zero the accumulator
  obtain ⟨m4, c4, u4, a04, fr4⟩ := u3.self.memsetW (B := P + 0x3CA8) (w := 8) (dst := sp0 + 0xFFFFFF80 + 0xC)
    (even_at P E.hP 0x3CA8 (by decide)) hc2 (codeS E.mset sFM I2) mm8_at_2c mm8_at_30
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP (0x2C + 8) (by decide)) (by decide)
    (by rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega) (by decide)
    (aligned_add hFa (k := 0xC) (by decide)) (sFM.sub (c := 0xC) (l := 32) (by decide))
    (by rw [g3, pa0, sp2]) (by rw [g3, pa1]) (by rw [g3, pa2]; rfl)
  obtain ⟨M4, hM4⟩ : ∃ M4, fillWords (saveMem m.mem (sp0 + 0xFFFFFF80)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80)) mmPs8) (sp0 + 0xFFFFFF80 + 0xC) 0 8 = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have I4 : ∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, fillWords_outside (dst := sp0 + 0xFFFFFF80 + 0xC) 8 (hx.sub (c := 0xC) (l := 32) (by decide)), I2 x hx]
  have k4 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m4 q = reg m3 q := fr4
  have e21 : reg m4 (21 : Fin 32) = yp := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3, p21,
      r2 _ (by decide), ha2]
  have e23 : reg m4 (23 : Fin 32) = np := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3, p23,
      r2 _ (by decide), ha3]
  have sp4 : reg m4 sp = sp0 + 0xFFFFFF80 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3,
      pk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  -- set up the first pass
  have hc4 := codeS E.code sFC I4
  obtain ⟨m5, c5, u5⟩ := St.block mmSetup u4.self hc4 mmSetup_end8
    (mmSetup_ok (by rw [e21, add_lit_zero]; exact E.hyp) (by rw [e23, add_lit_zero]; exact E.hnp))
  obtain ⟨em5, s22, s28, s29, s6, s7, s21, sa6, s17, sk⟩ := mmSetup_run (M := M4) (f := reg m4) u4.self.zero
  rw [em5] at u5
  have g5 : ∀ q, reg m5 q = (runBlock mmSetup (M4, reg m4)).2 q := u5.regs
  obtain ⟨m6, d6, u6⟩ := u5.self.aluImm hc4 mm8_at_4c (off' := 0x4E) (by decide)
  have v6 : upd (reg m5) (5 : Fin 32) (aluEval .add (reg m5 x0) 0x8) (5 : Fin 32) = 8 := by
    simp +decide only [upd, ↓reduceIte, u5.self.zero]
  obtain ⟨m7, d7, u7⟩ := u6.notTaken hc4 0x52 mm8_at_4e (by decide) (by
    rw [v6]; simp +decide only [upd, ↓reduceIte])
  have g7 : ∀ q, q ≠ (5 : Fin 32) → reg m7 q = reg m5 q := fun q hq => by
    rw [u7.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, u5.self.zero]
    · simp [upd, h0, hq]
  have kk : ∀ q, setupKeep q = true → q ≠ (5 : Fin 32) → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra →
      reg m7 q = (runBlock mmPro8 (saveMem m.mem (sp0 + 0xFFFFFF80)
        (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80)) mmPs8, reg m2)).2 q :=
    fun q hs h5 h2 h3 h4 h5' h6 hr => by rw [g7 q h5, g5, sk q hs, k4 q h2 h3 h4 h5' h6 hr, g3]
  have hyF : Sep (sp0 + 0xFFFFFF80) 0x80 yp 4 := (E.frame E.sYG.symm).subR (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  have hnF : Sep (sp0 + 0xFFFFFF80) 0x80 np 4 := (E.frame E.sNG.symm).subR (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  refine ⟨m7, M4, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (.single d7)))))), u7.self, I4,
    fun r o hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · have slot : ∀ (r : Fin 32) (o : Word), (r, o) ∈ mmPs8 → 0x50 ≤ o.toNat → o.toNat + 4 ≤ 0x80 →
        (∀ p ∈ mmPs8, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
          p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32)) → r ≠ sp →
        memLoad32 M4 (sp0 + 0xFFFFFF80 + o) = reg m r := fun r o hm h1 h2 hp hr => by
      have hFo : sp0 + 0xFFFFFF80 + BitVec.ofNat 32 o.toNat = sp0 + 0xFFFFFF80 + o := by rw [ofNat_toNat_self]
      rw [← hM4, ← hFo, fillWords_load_sep (dst := sp0 + 0xFFFFFF80 + 0xC) (by
        have := sep_offsets (sp0 + 0xFFFFFF80) (c := 0xC) (n := 32) (d := o.toNat) (k := 4) (.inl (by omega))
          (by omega) (by omega)
        exact this), hFo, saveMem_slot mmPs8 _ hm hp, upd_ne (by
          intro h; apply hr; exact Fin.ext (by
            simp only [mmPs8, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
              (rw [Prod.mk.injEq] at h'; rw [h'.1] at h; exact absurd h (by decide)))) hr]
    simp only [mmPs8, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
      (rw [Prod.mk.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'; exact slot _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide))
  · have hacw : (sp0 + 0xFFFFFF80 + 0xC).toNat + 4 * 8 ≤ 2 ^ 32 := by
      rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega
    rw [← hM4]
    exact accV_zero 8 fun i hi => fillWords_load 8 i hi hacw
  · rw [g7 _ (by decide), g5, sk _ rfl, sp4]
  · rw [g7 _ (by decide), g5, s22]
  · rw [g7 _ (by decide), g5, s29]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p20,
      r2 _ (by decide), ha1]
  · rw [g7 _ (by decide), g5, s6, e21, add_lit_zero, ← hM4,
      fillWords_load_sep (dst := sp0 + 0xFFFFFF80 + 0xC) ((hyF.sub (c := 0xC) (l := 32) (by decide))),
      load_frame I2 hyF]
  · rw [g7 _ (by decide), g5, s7, e23, add_lit_zero, ← hM4,
      fillWords_load_sep (dst := sp0 + 0xFFFFFF80 + 0xC) ((hnF.sub (c := 0xC) (l := 32) (by decide))),
      load_frame I2 hnF]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p19,
      r2 _ (by decide), ha4]
  · rw [g7 _ (by decide), g5, s17, e23]; rfl
  · have e : (0xC : Word) + BitVec.ofNat 32 (4 * (0 + 1)) = 0x10 := by decide
    rw [g7 _ (by decide), g5, sa6, sp4, BitVec.add_assoc (sp0 + 0xFFFFFF80) 0xC, e]
  · rw [g7 _ (by decide), g5, s21, e21]; rfl
  · rw [g7 _ (by decide), g5, s28]
  · rw [u7.regs, v6]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p18,
      r2 _ (by decide), ha0]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p23,
      r2 _ (by decide), ha3]
  · have key : ∀ q : Fin 32, q.val ∈ [3, 4, 27] → setupKeep q = true ∧ q ≠ (5 : Fin 32) ∧ q ≠ a2 ∧ q ≠ a3 ∧
        q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧
        q ≠ (20 : Fin 32) ∧ q ≠ (21 : Fin 32) ∧ q ≠ (23 : Fin 32) ∧ q ≠ sp := by decide
    obtain ⟨hs, h5, h2, h3, h4, h5', h6, hr, h0, h1, h18, h19, h20, h21, h23, hsp'⟩ := key q hq
    rw [kk q hs h5 h2 h3 h4 h5' h6 hr, pk q h0 h1 h2 h18 h19 h20 h21 h23, r2 q hsp']

/-- The registers the final subtraction leaves alone. -/
def midKeep8 (q : Fin 32) : Bool := q.val ∉ [1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 23]

theorem mm_mid8 {P sp0 out xp yp np : Word} {M0 : Word → BitVec 8} (E : MMEnv8 M0 P sp0 out xp yp np)
    {M : Word → BitVec 8} {n : Machine} (s : St M P n 0x102 (reg n))
    (hfr : ∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → M x = M0 x)
    (rsp : reg n sp = sp0 + 0xFFFFFF80) (r23 : reg n (23 : Fin 32) = np) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x13C (reg n') ∧
      (∀ x, Sep (sp0 + 0xFFFFFF7C) 4 x 1 → Sep (sp0 + 0xFFFFFF80 + 0x2C) 32 x 1 → M' x = M x) ∧
      (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
      accV M (sp0 + 0xFFFFFF80 + 0xC) 8 + 2 ^ (32 * 8) * maskBit (reg n' a2) =
        accV M np 8 + accV M' (sp0 + 0xFFFFFF80 + 0x2C) 8 ∧
      reg n' sp = sp0 + 0xFFFFFF80 ∧ ∀ q, midKeep8 q = true → reg n' q = reg n q := by
  obtain ⟨hG, hFG, hFw⟩ := frameA08 sp0 E.hS
  have hGa : (sp0 + 0xFFFFFF40).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFF40) (by decide)
  have eF4 : sp0 + 0xFFFFFF80 + 0xFFFFFFFC = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x3C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eF4' : sp0 + 0xFFFFFF7C = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x3C := by rw [BitVec.add_assoc]; rfl
  have eA : sp0 + 0xFFFFFF80 + 0xC = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x4C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eD : sp0 + 0xFFFFFF80 + 0x2C = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x6C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have go : ∀ c d k, c + 4 ≤ d ∨ d + k ≤ c → d + k ≤ 0xC0 → c + 4 ≤ 0xC0 →
      Sep (sp0 + 0xFFFFFF40 + BitVec.ofNat 32 c) 4 (sp0 + 0xFFFFFF40 + BitVec.ofNat 32 d) k :=
    fun c d k h h1 h2 => sep_offsets _ h (by omega) (by omega)
  have codeF : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn M0 b code →
      Sep (sp0 + 0xFFFFFF40) 0xC0 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → M' x = M0 x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ ((E.frame hs).subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hc := codeF E.code E.sGC hfr
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := St.block mmSubPre8 s hc mmSubPre_end8 (by
    simp only [BlockOk, BInstr.ok, mmSubPre8]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  obtain ⟨em1, b0, b2, b1, b19, bk⟩ := mmSubPre_run8 (M := M) (f := reg n) hz
  rw [em1] at u1
  have g1 : ∀ q, reg n1 q = (runBlock mmSubPre8 (M, reg n)).2 q := u1.regs
  rw [rsp] at b0 b19
  have hDa : (sp0 + 0xFFFFFF80 + 0x2C).toNat % 4 = 0 := by rw [eD]; exact aligned_add hGa (by decide)
  have hDw : (sp0 + 0xFFFFFF80 + 0x2C).toNat + 32 < 2 ^ 32 := by
    rw [eD, BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega
  obtain ⟨n2, c2, u2, a02, fr2⟩ := u1.self.memsetW (B := P + 0x3CA8) (w := 8) (dst := sp0 + 0xFFFFFF80 + 0x2C)
    (even_at P E.hP 0x3CA8 (by decide)) hc (codeF E.mset E.sGM hfr) mm8_at_10e mm8_at_112
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP (0x10E + 8) (by decide)) (by decide)
    (by omega) (by decide) hDa (by rw [eD]; exact E.sGM.sub (c := 0x6C) (l := 32) (by decide))
    (by rw [g1, b0]) (by rw [g1, b1]) (by rw [g1, b2]; rfl)
  obtain ⟨MS, hMS⟩ : ∃ MS, fillWords M (sp0 + 0xFFFFFF80 + 0x2C) 0 8 = MS := ⟨_, rfl⟩
  rw [hMS] at u2
  have hS : ∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → MS x = M0 x := fun x hx => by
    rw [← hMS, fillWords_outside 8 (by
      have := hx.sub (c := 0x2C) (l := 32) (by decide); exact this), hfr x hx]
  have hcS := codeF E.code E.sGC hS
  obtain ⟨n3, c3, u3⟩ := St.block mmSubInit8 u2 hcS mmSubInit_end8 (by
    simp only [BlockOk, BInstr.ok, mmSubInit8]; exact ⟨trivial, trivial, trivial, trivial⟩)
  obtain ⟨em3, i2, i9, i8, ik⟩ := mmSubInit_run8 (M := MS) (f := reg n2) u2.zero
  rw [em3] at u3
  have g3 : ∀ q, reg n3 q = (runBlock mmSubInit8 (MS, reg n2)).2 q := u3.regs
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hcS 0x11E mm8_at_11c (by decide) (by rw [g3, i8, u3.self.zero]; decide)
  have k2 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n2 q = (runBlock mmSubPre8 (M, reg n)).2 q :=
    fun q h2 h3 h4 h5 h6 hr => by rw [fr2 q h2 h3 h4 h5 h6 hr, g1]
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (19 : Fin 32) →
      q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n4 q = reg n q := fun q h0 h1 h2 h3 h4 h5 h6 hr h19 h9 h8 => by
    rw [u4.regs, g3, ik q h2 h9 h8, k2 q h2 h3 h4 h5 h6 hr, bk q h0 h1 h2 h19]
  have sp4 : reg n4 sp = sp0 + 0xFFFFFF80 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), rsp]
  have sDA : Sep (sp0 + 0xFFFFFF80 + 0x2C) 32 (sp0 + 0xFFFFFF80 + 0xC) 32 := by
    rw [eD, eA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide)
  obtain ⟨n5, M5, c5, u5, hc5, hf5, hm5, hv5, sp5, fr5⟩ := sub_loop8 (M0 := MS) (F := sp0 + 0xFFFFFF80)
    (acc := sp0 + 0xFFFFFF80 + 0xC) (np := np) (D := sp0 + 0xFFFFFF80 + 0x2C) E.hP
    (aligned_add E.hsp (k := 0xFFFFFF80) (by decide)) (by rw [eA]; exact aligned_add hGa (by decide)) E.hnp hDa (Nat.le_of_lt hDw)
    (by rw [eF4, eA]; exact go _ _ _ (.inl (by decide)) (by decide) (by decide))
    (by rw [eF4]; exact E.sNG.symm.sub (c := 0x3C) (l := 4) (by decide))
    (by rw [eF4, eD]; exact go _ _ _ (.inl (by decide)) (by decide) (by decide))
    sDA (by rw [eD]; exact E.sNG.symm.sub (c := 0x6C) (l := 32) (by decide))
    (by rw [eF4]; exact E.sGB.sub (c := 0x3C) (l := 4) (by decide))
    (by rw [eF4]; exact E.sGC.sub (c := 0x3C) (l := 4) (by decide))
    (by rw [eD]; exact E.sGB.sub (c := 0x6C) (l := 32) (by decide))
    (by rw [eD]; exact E.sGC.sub (c := 0x6C) (l := 32) (by decide))
    7 0 (by decide) u4.self hcS (codeF E.bsub E.sGB hS) (fun _ _ _ => rfl) (.inl rfl) (sub_inv0 _ _ _ _ _) sp4
    (by rw [u4.regs, g3, i9, k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      bk _ (by decide) (by decide) (by decide) (by decide), rsp, Nat.mul_zero, add_ofNat_zero])
    (by rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), r23, Nat.mul_zero, add_ofNat_zero])
    (by rw [u4.regs, g3, ik _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), b19, Nat.mul_zero, add_ofNat_zero])
    (by rw [u4.regs, g3, i8]) (by rw [u4.regs, g3, i2])
  have eAcc : accV MS (sp0 + 0xFFFFFF80 + 0xC) 8 = accV M (sp0 + 0xFFFFFF80 + 0xC) 8 :=
    accV_congr 8 fun i hi => by rw [← hMS]; exact fillWords_load_sep (sDA.subR (c := 4 * i) (l := 4) (by omega))
  have sDN : Sep (sp0 + 0xFFFFFF80 + 0x2C) 32 np 32 := by rw [eD]; exact E.sNG.symm.sub (c := 0x6C) (l := 32) (by decide)
  have eNp : accV MS np 8 = accV M np 8 :=
    accV_congr 8 fun i hi => by rw [← hMS]; exact fillWords_load_sep (sDN.subR (c := 4 * i) (l := 4) (by omega))
  refine ⟨n5, M5, c1.trans (c2.trans (c3.trans (.cons d4 c5))), u5, fun x h1 h2 => ?_, hm5, ?_, sp5, fun q hq => ?_⟩
  · rw [hf5 x (by rw [eF4]; rw [eF4'] at h1; exact h1) h2, ← hMS, fillWords_outside 8 h2]
  · rw [← eAcc, ← eNp]; exact hv5
  · have key : ∀ q : Fin 32, midKeep8 q = true → q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧
        q ≠ ra ∧ q ≠ (19 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (8 : Fin 32) ∧ q ≠ (23 : Fin 32) := by decide
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, hr, h19, h9, h8, h23⟩ := key q hq
    rw [fr5 q h0 h1 h2 h3 h4 hr h9 h23 h19 h8, k4 q h0 h1 h2 h3 h4 h5 h6 hr h19 h9 h8]

theorem mm_epi8 {P sp0 out xp yp np b : Word} {M0 : Word → BitVec 8} {v : Fin 32 → Word}
    (E : MMEnv8 M0 P sp0 out xp yp np) {M : Word → BitVec 8} {n : Machine} (s : St M P n 0x13C (reg n))
    (hfr : ∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → M x = M0 x)
    (hsl : ∀ r o, (r, o) ∈ mmPs8 → memLoad32 M (sp0 + 0xFFFFFF80 + o) = v r)
    (rsp : reg n sp = sp0 + 0xFFFFFF80) (r18 : reg n (18 : Fin 32) = out) (ra2 : reg n a2 = b)
    (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧ reg n' sp = sp0 ∧
      (∀ i, i < 8 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if (reg n (22 : Fin 32)).toNat = 0 ∧ maskBit b = 1 then memLoad32 M (sp0 + 0xFFFFFF80 + 0xC + BitVec.ofNat 32 (4 * i))
        else memLoad32 M (sp0 + 0xFFFFFF80 + 0x2C + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → Sep out 32 x 1 → n'.mem x = M0 x) ∧
      (∀ r o, (r, o) ∈ mmPs8 → reg n' r = v r) ∧ ∀ q, q.val ∈ [3, 4, 27] → reg n' q = reg n q := by
  obtain ⟨hG, hFG, hFw⟩ := frameA08 sp0 E.hS
  have hGa : (sp0 + 0xFFFFFF40).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFF40) (by decide)
  have hFa : (sp0 + 0xFFFFFF80).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFF80) (by decide)
  have eFo : ∀ c : Nat, sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 (0x40 + c) := by
    intro c; rw [hFG, add_ofNat_assoc]
  have e6C : sp0 + 0xFFFFFF80 + 0x4C = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x8C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eF4 : sp0 + 0xFFFFFF80 + 0xFFFFFFFC = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x3C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eA : sp0 + 0xFFFFFF80 + 0xC = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x4C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eD : sp0 + 0xFFFFFF80 + 0x2C = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x6C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have codeG : ∀ {M' : Word → BitVec 8} {b' : Word} {code : List Nat}, CodeIn M0 b' code →
      Sep (sp0 + 0xFFFFFF40) 0xC0 b' code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → M' x = M0 x) → CodeIn M' b' code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hc := codeG E.code E.sGC hfr
  have hz := s.zero
  -- the choice
  obtain ⟨n1, c1, u1⟩ := St.block mmChoice8 s hc mmChoice_end8 (mmChoice_ok8 (by rw [rsp]; exact aligned_add hFa (by decide))
    (by rw [rsp, e6C]; exact E.sGC.sub (c := 0x8C) (l := 4) (by decide)))
  obtain ⟨em1, h9, h0, h1, hk1⟩ := mmChoice_run8 (M := M) (f := reg n) hz
  rw [em1, rsp, ra2] at u1
  rw [ra2] at h9
  obtain ⟨c, hcv⟩ : ∃ c, aluEval .and (aluEval .sltu (reg n (22 : Fin 32)) 1) b = c := ⟨_, rfl⟩
  rw [hcv] at u1 h9
  have hc01 : c = 0 ∨ c = 1 := by
    rw [← hcv, choice_val8 _ _ hb]; split
    · exact .inr rfl
    · exact .inl rfl
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore8 (memStore32 M (sp0 + 0xFFFFFF80 + 0x4C) (reg n (22 : Fin 32)))
      (sp0 + 0xFFFFFF80 + 0x4C) (c.extractLsb' 0 8) = M1 := ⟨_, rfl⟩
  rw [hM1] at u1
  have I1 : ∀ x, Sep (sp0 + 0xFFFFFF80 + 0x4C) 4 x 1 → M1 x = M x := fun x hx => by
    rw [← hM1, memStore8_ne (fun e => hx.point (i := 0) (j := 0) (by decide) (by decide)
      (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)), memStore32_get_sep hx]
  have I1G : ∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → M1 x = M0 x := fun x hx => by
    rw [I1 x (by rw [e6C]; exact hx.sub (by decide)), hfr x hx]
  have g1 : ∀ q, reg n1 q = (runBlock mmChoice8 (M, reg n)).2 q := u1.regs
  -- the unused `borrowing_sub`
  obtain ⟨n2, c2, u2, _, _, sp2, fr2, mem2⟩ := u1.self.bsubCall (codeG E.code E.sGC I1G) (codeG E.bsub E.sGB I1G)
    (even_at P E.hP 0xFFFF17E2 (by decide)) mm8_at_15a mm8_at_15e (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P E.hP (0x15A + 8) (by decide))
    (by rw [g1, hk1 _ (by decide) (by decide) (by decide) (by decide), rsp]) hFa
    (by rw [eF4]; exact E.sGB.sub (c := 0x3C) (l := 4) (by decide))
  have I2G : ∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → n2.mem x = M0 x := fun x hx => by
    rw [mem2 x (by rw [eF4]; exact hx.sub (by decide)), I1G x hx]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → reg n2 q = reg n q :=
    fun q q0 q1 q2 q3 q4 qr q9 => by rw [fr2 q q0 q1 q2 q3 q4 qr, g1, hk1 q q0 q1 q2 q9]
  have e9 : reg n2 (9 : Fin 32) = c := by
    rw [fr2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1, h9]
  -- the arguments, and the call to `Uint<8>::select`
  have hc2 := codeG E.code E.sGC I2G
  obtain ⟨n3, c3, u3⟩ := St.block mmSelArgs8 u2 hc2 mmSelArgs_end8 (by
    simp only [BlockOk, BInstr.ok, mmSelArgs8]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  obtain ⟨em3, s1, s2, s0, s3, sk⟩ := mmSelArgs_run8 (M := n2.mem) (f := reg n2) u2.zero
  rw [em3] at u3
  rw [sp2] at s1 s2
  have g3 : ∀ q, reg n3 q = (runBlock mmSelArgs8 (n2.mem, reg n2)).2 q := u3.regs
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hc2 mm8_at_16a mm8_at_16e (cb := P + 0x18E)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP 0x18E (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have sp4 : reg m4 sp = sp0 + 0xFFFFFF80 := by
    rw [r4 _ (by decide), g3, sk _ (by decide) (by decide) (by decide) (by decide), sp2]
  have eSel : reg m4 sp + 0xFFFFFFC0 = sp0 + 0xFFFFFF40 := by
    rw [sp4, hFG, BitVec.add_assoc]; exact BitVec.add_zero _
  have hS50 : ∀ {b' : Word} {l : Nat}, Sep (sp0 + 0xFFFFFF40) 0xC0 b' l → Sep (sp0 + 0xFFFFFF40) 0x40 b' l :=
    fun h => (h.sub (c := 0) (l := 0x40) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
  have eM : P + 0x18E + 0x3B1A = P + 0x3CA8 := by rw [BitVec.add_assoc]; rfl
  have eU : P + 0x18E + 0x3B82 = P + 0x3D10 := by rw [BitVec.add_assoc]; rfl
  have eB : P + 0x18E + 0x3B8A = P + 0x3D18 := by rw [BitVec.add_assoc]; rfl
  have hF50 : 0x40 ≤ (sp0 + 0xFFFFFF80).toNat := by
    rw [hFG, BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega
  have SE : Sel8Env m4.mem (P + 0x18E) (reg m4 sp) out (sp0 + 0xFFFFFF80 + 0x2C) (sp0 + 0xFFFFFF80 + 0xC) := by
    rw [mem4]
    refine ⟨even_at P E.hP 0x18E (by decide), codeG E.sel E.sGL I2G, by rw [eM]; exact codeG E.mset E.sGM I2G,
      by rw [eU]; exact codeG E.stub E.sGU I2G, by rw [eB]; exact codeG E.body E.sGY I2G,
      by rw [sp4]; exact hFa, by rw [sp4]; exact hF50, E.hout,
      aligned_add hFa (by decide), aligned_add hFa (by decide), E.hwo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eSel]; exact hS50 E.sGL
    · rw [eSel, eM]; exact hS50 E.sGM
    · rw [eSel, eU]; exact hS50 E.sGU
    · rw [eSel, eB]; exact hS50 E.sGY
    · rw [eSel]; exact (E.sOG.subR (c := 0) (l := 0x40) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
    · exact E.sOL
    · rw [eB]; exact E.sOY
    · rw [eSel, eD]
      exact (sep_offsets (sp0 + 0xFFFFFF40) (c := 0x6C) (n := 32) (d := 0) (k := 0x40) (.inr (by decide)) (by decide)
        (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
    · rw [eSel, eA]
      exact (sep_offsets (sp0 + 0xFFFFFF40) (c := 0x4C) (n := 32) (d := 0) (k := 0x40) (.inr (by decide)) (by decide)
        (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
  obtain ⟨m5, c5, pc5, sp5, w5, mem5, k5⟩ := uintSelect8_correct m4 SE pc4
    (by rw [r4 _ (by decide), g3, s0, k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), r18])
    (by rw [r4 _ (by decide), g3, s1]) (by rw [r4 _ (by decide), g3, s2]) (by rw [r4 _ (by decide), g3, s3, e9])
    hc01 (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P E.hP (0x16A + 8) (by decide)))
  rw [eSel] at mem5
  rw [sp4] at sp5
  have I5 : ∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → Sep out 32 x 1 → m5.mem x = M0 x := fun x hx ho => by
    rw [mem5 x (hx.sub (c := 0) (l := 0x40) (by decide) |> fun h' => by rwa [add_ofNat_zero] at h') ho, mem4, I2G x hx]
  have codeGO : ∀ {b' : Word} {code : List Nat}, CodeIn M0 b' code → Sep (sp0 + 0xFFFFFF40) 0xC0 b' code.length →
      Sep out 32 b' code.length → CodeIn m5.mem b' code := fun hc' hs ho i hi => by
    rw [I5 _ (hs.subR (c := i) (l := 1) (by omega)) (ho.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have hc5 := codeGO E.code E.sGC E.sOC
  have u5 : St m5.mem P m5 0x172 (reg m5) := ⟨pc5, rfl, fun _ => rfl⟩
  -- the frame's saved slots, and the two buffers, are as they were at 0x13C
  have load5 : ∀ a, Sep (sp0 + 0xFFFFFF40) 0x40 a 4 → Sep out 32 a 4 →
      Sep (sp0 + 0xFFFFFF80 + 0xFFFFFFFC) 4 a 4 → Sep (sp0 + 0xFFFFFF80 + 0x4C) 4 a 4 →
      memLoad32 m5.mem a = memLoad32 M a := fun a h1 h2 h3 h4 => by
    rw [load_frame2 (u := sp0 + 0xFFFFFF40) (n := 0x40) (v := out) (k := 32)
      (fun x hx ho => by
        rw [mem5 x (by have := hx; exact this) ho]) h1 h2, mem4, load_frame mem2 h3, load_frame I1 h4]
  have slot : ∀ r o, (r, o) ∈ mmPs8 → 0x50 ≤ o.toNat → o.toNat + 4 ≤ 0x80 →
      memLoad32 m5.mem (sp0 + 0xFFFFFF80 + o) = v r := fun r o hm h1 h2 => by
    have hFo : sp0 + 0xFFFFFF80 + BitVec.ofNat 32 o.toNat = sp0 + 0xFFFFFF80 + o := by rw [ofNat_toNat_self]
    rw [← hFo, load5 _ (by
        rw [eFo]; exact (sep_offsets (sp0 + 0xFFFFFF40) (c := 0) (n := 0x40) (d := 0x40 + o.toNat) (k := 4)
          (.inl (by omega)) (by omega) (by omega)) |> fun h' => by rwa [add_ofNat_zero] at h')
      (by rw [eFo]; exact E.sOG.subR (c := 0x40 + o.toNat) (l := 4) (by omega))
      (by rw [eF4, eFo]; exact sep_offsets _ (.inl (by omega)) (by omega) (by omega))
      (by rw [e6C, eFo]; exact sep_offsets _ (.inl (by omega)) (by omega) (by omega)), hFo]
    exact hsl r o hm
  have hpsp : ∀ p ∈ mmPs8, p.1 ≠ sp := by decide
  obtain ⟨m6, c6, u6⟩ := St.block (restoreBlock mmPs8) u5 hc5 mmRestore_end8
    (restoreBlock_ok m5.mem (sp0 + 0xFFFFFF80) mmPs8 (reg m5) sp5 hpsp fun q hq => by
      simp only [mmPs8, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact aligned_add hFa (by decide))
  simp only [restoreBlock_run m5.mem (sp0 + 0xFFFFFF80) mmPs8 (reg m5) sp5 hpsp] at u6
  have rsp6 : restoreRegs m5.mem (sp0 + 0xFFFFFF80) (reg m5) mmPs8 sp = sp0 + 0xFFFFFF80 := by
    rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp5
  obtain ⟨m7, d7, u7⟩ := u6.aluImm hc5 mm8_at_18a (off' := 0x18C) (by decide)
  obtain ⟨m8, d8, pc8, mem8, regs8⟩ := u7.jalr hc5 mm8_at_18c
  have rra : restoreRegs m5.mem (sp0 + 0xFFFFFF80) (reg m5) mmPs8 ra = v ra := by
    simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
    exact slot ra _ (by decide) (by decide) (by decide)
  have sepF4 : ∀ c, 0x40 ≤ c → c + 4 ≤ 0xC0 →
      Sep (sp0 + 0xFFFFFF80 + 0xFFFFFFFC) 4 (sp0 + 0xFFFFFF40 + BitVec.ofNat 32 c) 4 := fun c h1 h2 => by
    rw [eF4]; exact sep_offsets _ (.inl (by omega)) (by omega) (by omega)
  have sep6C : ∀ c, c + 4 ≤ 0x8C →
      Sep (sp0 + 0xFFFFFF80 + 0x4C) 4 (sp0 + 0xFFFFFF40 + BitVec.ofNat 32 c) 4 := fun c h1 => by
    rw [e6C]; exact sep_offsets _ (.inr (by omega)) (by omega) (by omega)
  have hAcc : ∀ i, i < 8 → memLoad32 m4.mem (sp0 + 0xFFFFFF80 + 0xC + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (sp0 + 0xFFFFFF80 + 0xC + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [mem4, eA, add_ofNat_assoc, load_frame mem2 (sepF4 _ (by omega) (by omega)),
      load_frame I1 (sep6C _ (by omega))]
  have hDv : ∀ i, i < 8 → memLoad32 m4.mem (sp0 + 0xFFFFFF80 + 0x2C + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (sp0 + 0xFFFFFF80 + 0x2C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [mem4, eD, add_ofNat_assoc, load_frame mem2 (sepF4 _ (by omega) (by omega)),
      load_frame I1 (sep6C _ (by omega))]
  refine ⟨m8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (.cons d7 (.single d8))))))), ?_, ?_,
    fun i hi => ?_, fun x hx ho => ?_, fun r o hm => ?_, fun q hq => ?_⟩
  · rw [pc8]; simp +decide only [upd, ↓reduceIte]; rw [rra, add_lit_zero]
  · rw [regs8]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp6, hFG, BitVec.add_assoc, BitVec.add_assoc]; exact BitVec.add_zero _
  · rw [mem8, w5 i hi, hAcc i hi, hDv i hi, ← hcv, choice_val8 _ _ hb]
    by_cases hcd : (reg n (22 : Fin 32)).toNat = 0 ∧ maskBit b = 1
    · rw [ite_eq_left hcd, ite_eq_left rfl, ite_eq_left hcd]
    · rw [ite_eq_right hcd, ite_eq_right (by decide), ite_eq_right hcd]
  · rw [mem8, I5 x hx ho]
  · rw [regs8]
    simp only [mmPs8, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      exact slot _ _ (by decide) (by decide) (by decide)
  · have key : ∀ q : Fin 32, q.val ∈ [3, 4, 27] → selKeep q = true ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧
        q ≠ a3 ∧ q ≠ a4 ∧ q ≠ (9 : Fin 32) ∧ q ≠ sp ∧ q.val ≠ 0 ∧ (∀ p ∈ mmPs8, p.1 ≠ q) := by decide
    obtain ⟨hs, hr, h0, h1, h2, h3, h4, h9, hsp, hq0, hps⟩ := key q hq
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)), (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs m5.mem (sp0 + 0xFFFFFF80) f ps q = f q := by
      intro f ps
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    rw [regs8, upd_ne hq0 hsp, rr _ _ hps, k5 q hs, r4 q hr, g3, sk q h0 h1 h2 h3,
      k2 q h0 h1 h2 h3 h4 hr h9]

theorem accV_frameS8 {M M0 : Word → BitVec 8} {u b : Word} {k : Nat} (hf : ∀ x, Sep u k x 1 → M x = M0 x)
    (hs : Sep u k b 32) : accV M b 8 = accV M0 b 8 :=
  accV_congr 8 fun i hi => load_frame hf (hs.subR (by omega))

/-- **The compiled `mul_montgomery_form::<8>`.** For operands `x` and `y`
and modulus `n` of 8 limbs, with `y < n` and `k · n₀ ≡ -1 (mod 2^32)`, it
writes to `out` the number `r < n` with `r · 2^256 ≡ x · y (mod n)`,
returns with `sp` and the callee-saved registers restored, and writes only
`out` and the 0xC0 bytes of stack below `sp`. -/
theorem mulMont8_correct (m : Machine) {P sp0 out xp yp np K retAddr : Word}
    (E : MMEnv8 m.mem P sp0 out xp yp np) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (ha2 : reg m a2 = yp) (ha3 : reg m a3 = np) (ha4 : reg m a4 = K) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hk : (K.toNat * (memLoad32 m.mem np).toNat + 1) % 2 ^ 32 = 0) (hYN : accV m.mem yp 8 < accV m.mem np 8) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      accV m'.mem out 8 < accV m.mem np 8 ∧
      accV m'.mem out 8 * 2 ^ 256 % accV m.mem np 8 = accV m.mem xp 8 * accV m.mem yp 8 % accV m.mem np 8 ∧
      (∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x) ∧
      ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q := by
  obtain ⟨hG, hFG, hFw⟩ := frameA08 sp0 E.hS
  have hGa : (sp0 + 0xFFFFFF40).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFF40) (by decide)
  have eA : sp0 + 0xFFFFFF80 + 0xC = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x4C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨n1, M1, c1, u1, hf1, hsl1, hacc0, sp1, r22, r29, r20, r6, r7, r19, r17, ra6, r21, r28, r5, r18, r23, rk⟩ :=
    mm_pro8 m E hpc ha0 ha1 ha2 ha3 ha4 hsp
  have sXF := E.frame E.sXG.symm; have sYF := E.frame E.sYG.symm; have sNF := E.frame E.sNG.symm
  have eX1 : accV M1 xp 8 = accV m.mem xp 8 := accV_frameS8 hf1 sXF
  have eY1 : accV M1 yp 8 = accV m.mem yp 8 := accV_frameS8 hf1 sYF
  have eN1 : accV M1 np 8 = accV m.mem np 8 := accV_frameS8 hf1 sNF
  have ey0 : memLoad32 M1 yp = memLoad32 m.mem yp :=
    load_frame hf1 (sYF.subR (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
  have en0 : memLoad32 M1 np = memLoad32 m.mem np :=
    load_frame hf1 (sNF.subR (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
  have hc1 : CodeIn M1 P mulMont8Code := fun i hi => by
    rw [hf1 _ ((E.frame E.sGC).subR (c := i) (l := 1) (by omega))]; exact E.code i hi
  have hAw : (sp0 + 0xFFFFFF80 + 0xC).toNat + 32 ≤ 2 ^ 32 := by
    rw [eA, BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega
  have hN0 : 0 < accV m.mem np 8 := by omega
  -- the outer loop
  obtain ⟨n2, M2, c2, u2, hc2, hf2, ⟨U, hU⟩, hbd2, k2⟩ := mm_outer8 (M0 := M1) (K := K) E.hxp E.hyp E.hnp
    (by rw [eA]; exact aligned_add hGa (by decide)) hAw
    (by rw [eA]; exact E.sXG.symm.sub (c := 0x4C) (l := 32) (by decide))
    (by rw [eA]; exact E.sYG.symm.sub (c := 0x4C) (l := 32) (by decide))
    (by rw [eA]; exact E.sNG.symm.sub (c := 0x4C) (l := 32) (by decide))
    (by rw [eA]; exact E.sGC.sub (c := 0x4C) (l := 32) (by decide)) (by rw [en0]; exact hk)
    (by rw [eY1, eN1]; exact hYN) 7 0 (by decide) u1 hc1 (fun _ _ => rfl)
    ⟨0, by rw [hacc0, r22, show ((0 : Word)).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, Nat.mul_zero,
      show accV M1 xp 0 = 0 from rfl, Nat.zero_mul, Nat.zero_mul]⟩
    (by rw [hacc0, r22, show ((0 : Word)).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, eN1]; omega)
    r29 r20 (by rw [r6, ey0]) (by rw [r7, en0]) r19 (by rw [sp1])
    (by rw [sp1, BitVec.add_assoc (sp0 + 0xFFFFFF80) 0xC, show (0xC : Word) + BitVec.ofNat 32 (4 * 7) = 0x28 by decide])
    r17 ra6 r21 r28 r5
  rw [eX1, eY1, eN1] at hU
  rw [eN1] at hbd2
  have hf2' : ∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → M2 x = m.mem x := fun x hx => by
    rw [hf2 x (hx.sub (c := 0xC) (l := 32) (by decide)), hf1 x hx]
  -- the final subtraction
  obtain ⟨n3, M3, c3, u3, hf3, hm3, hv3, sp3, k3⟩ := mm_mid8 E u2 hf2'
    (by rw [k2 _ rfl, sp1]) (by rw [k2 _ rfl, r23])
  have eF4' : sp0 + 0xFFFFFF7C = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x3C := by rw [BitVec.add_assoc]; rfl
  have eD : sp0 + 0xFFFFFF80 + 0x2C = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 0x6C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hf3' : ∀ x, Sep (sp0 + 0xFFFFFF40) 0xC0 x 1 → M3 x = m.mem x := fun x hx => by
    rw [hf3 x (by rw [eF4']; exact hx.sub (by decide)) (by rw [eD]; exact hx.sub (by decide)),
      hf2' x (E.frame hx)]
  -- the end
  obtain ⟨n4, c4, pc4, sp4, w4, mf4, kr4, kq4⟩ := mm_epi8 (v := reg m) E u3 hf3' (fun r o hm => by
      have hb : 0x50 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x80 := by
        simp only [mmPs8, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      have eo : sp0 + 0xFFFFFF80 + o = sp0 + 0xFFFFFF40 + BitVec.ofNat 32 (0x40 + o.toNat) := by
        have e : BitVec.ofNat 32 0x40 + o = BitVec.ofNat 32 (0x40 + o.toNat) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        rw [hFG, BitVec.add_assoc, e]
      have h1 : Sep (sp0 + 0xFFFFFF7C) 4 (sp0 + 0xFFFFFF80 + o) 4 := by
        rw [eF4', eo]; exact sep_offsets _ (.inl (by omega)) (by omega) (by omega)
      have h2 : Sep (sp0 + 0xFFFFFF80 + 0x2C) 32 (sp0 + 0xFFFFFF80 + o) 4 := by
        rw [eD, eo]; exact sep_offsets _ (.inl (by omega)) (by omega) (by omega)
      have h3 : Sep (sp0 + 0xFFFFFF80 + 0xC) 32 (sp0 + 0xFFFFFF80 + o) 4 := by
        rw [eA, eo]; exact sep_offsets _ (.inl (by omega)) (by omega) (by omega)
      rw [load_frame2 hf3 h1 h2, load_frame hf2 h3]
      exact hsl1 r o hm)
    sp3 (by rw [k3 _ rfl, k2 _ rfl, r18]) rfl hm3
  -- the value
  have hDA : Sep (sp0 + 0xFFFFFF80 + 0x2C) 32 (sp0 + 0xFFFFFF80 + 0xC) 32 := by
    rw [eD, eA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide)
  have hFA : Sep (sp0 + 0xFFFFFF7C) 4 (sp0 + 0xFFFFFF80 + 0xC) 32 := by
    rw [eF4', eA]; exact sep_offsets _ (.inl (by decide)) (by decide) (by decide)
  have eA3 : accV M3 (sp0 + 0xFFFFFF80 + 0xC) 8 = accV M2 (sp0 + 0xFFFFFF80 + 0xC) 8 :=
    accV_congr 8 fun i hi => load_frame2 hf3 (hFA.subR (by omega)) (hDA.subR (by omega))
  have eN2 : accV M2 np 8 = accV m.mem np 8 := accV_frameS8 hf2' sNF
  rw [eN2] at hv3
  have e22 : reg n3 (22 : Fin 32) = reg n2 (22 : Fin 32) := k3 _ rfl
  have hR : accV n4.mem out 8 = (if (reg n2 (22 : Fin 32)).toNat = 0 ∧ maskBit (reg n3 a2) = 1 then
      accV M2 (sp0 + 0xFFFFFF80 + 0xC) 8 else accV M3 (sp0 + 0xFFFFFF80 + 0x2C) 8) := by
    by_cases hcd : (reg n2 (22 : Fin 32)).toNat = 0 ∧ maskBit (reg n3 a2) = 1
    · rw [ite_eq_left hcd, ← eA3]
      exact accV_congr2 8 fun i hi => by rw [w4 i hi, e22, ite_eq_left hcd]
    · rw [ite_eq_right hcd]
      exact accV_congr2 8 fun i hi => by rw [w4 i hi, e22, ite_eq_right hcd]
  have hmb : maskBit (reg n3 a2) ≤ 1 := mb_le1 _
  have hT := mm_final_arith (Bk := 2 ^ (32 * 8)) (accV_lt M3 _ 8) (accV_lt m.mem np 8) hbd2
    hv3 hmb
  rw [← hR] at hT
  refine ⟨n4, c1.trans (c2.trans (c3.trans c4)), by rw [pc4, hra, hret], sp4, ?_, ?_, fun x hx ho => ?_,
    fun q hq => ?_⟩
  · rw [hT]; exact Nat.mod_lt _ hN0
  · exact mont_congr8 hT hU
  · exact mf4 x hx ho
  · have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
        q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨ q = (24 : Fin 32) ∨ q = (25 : Fin 32) ∨
        q = (26 : Fin 32) ∨ (q.val ∈ [3, 4, 27] ∧ midKeep8 q = true ∧ passKeep8 q = true) := by decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨h1, h2, h3⟩
    · exact kr4 _ 0x7C (by decide)
    · exact kr4 _ 0x78 (by decide)
    · exact kr4 _ 0x74 (by decide)
    · exact kr4 _ 0x70 (by decide)
    · exact kr4 _ 0x6C (by decide)
    · exact kr4 _ 0x68 (by decide)
    · exact kr4 _ 0x64 (by decide)
    · exact kr4 _ 0x60 (by decide)
    · exact kr4 _ 0x5C (by decide)
    · exact kr4 _ 0x58 (by decide)
    · exact kr4 _ 0x54 (by decide)
    · exact kr4 _ 0x50 (by decide)
    · rw [kq4 q h1, k3 q h2, k2 q h3, rk q h1]

end C3.RV32
