import C3BootProofs.Proofs.CtAssign
import C3BootProofs.Proofs.EcdsaSig
import C3BootProofs.Proofs.ScalarIsZero

/-!
# Field-element `conditional_select` and its callers, as compiled

`<ConstMontyForm<p384 field> as ConditionallySelectable>::conditional_select`
copies `a` to its stack with the proved `memcpy`, overwrites the copy with `b`
through the proved `Uint<12>::ct_assign` when the choice is 1, and copies the
result to `out`. The P-256 instance does the same for 8 limbs with the
proved slice `ct_assign`. `CtOption<AffinePoint>::unwrap_or` selects both
coordinates through it and the identity byte with a mask, and
`CtOption<MontyFieldElement>::map` selects between the value and zero.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem cs4_at_0 : fetchRel condSelect384Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem cs4_at_2 : fetchRel condSelect384Code 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem cs4_at_4 : fetchRel condSelect384Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem cs4_at_6 : fetchRel condSelect384Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem cs4_at_8 : fetchRel condSelect384Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem cs4_at_a : fetchRel condSelect384Code 0xA = some (.alu .add (8 : Fin 32) x0 a3, 2) := by decide
theorem cs4_at_c : fetchRel condSelect384Code 0xC = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem cs4_at_e : fetchRel condSelect384Code 0xE = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem cs4_at_10 : fetchRel condSelect384Code 0x10 = some (.alu .add a0 x0 sp, 2) := by decide
theorem cs4_at_12 : fetchRel condSelect384Code 0x12 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem cs4_at_16 : fetchRel condSelect384Code 0x16 = some (.auipc ra 0x1000, 4) := by decide
theorem cs4_at_1a : fetchRel condSelect384Code 0x1A = some (.jalr ra ra 0x4, 4) := by decide
theorem cs4_at_1e : fetchRel condSelect384Code 0x1E = some (.alu .add a0 x0 sp, 2) := by decide
theorem cs4_at_20 : fetchRel condSelect384Code 0x20 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem cs4_at_22 : fetchRel condSelect384Code 0x22 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem cs4_at_24 : fetchRel condSelect384Code 0x24 = some (.auipc ra 0x0, 4) := by decide
theorem cs4_at_28 : fetchRel condSelect384Code 0x28 = some (.jalr ra ra 0x2C8, 4) := by decide
theorem cs4_at_2c : fetchRel condSelect384Code 0x2C = some (.alu .add a1 x0 sp, 2) := by decide
theorem cs4_at_2e : fetchRel condSelect384Code 0x2E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem cs4_at_32 : fetchRel condSelect384Code 0x32 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem cs4_at_34 : fetchRel condSelect384Code 0x34 = some (.auipc ra 0x1000, 4) := by decide
theorem cs4_at_38 : fetchRel condSelect384Code 0x38 = some (.jalr ra ra 0xFFFFFFE6, 4) := by decide
theorem cs4_at_3c : fetchRel condSelect384Code 0x3C = some (.load .lw ra sp 0x3C, 2) := by decide
theorem cs4_at_3e : fetchRel condSelect384Code 0x3E = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem cs4_at_40 : fetchRel condSelect384Code 0x40 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem cs4_at_42 : fetchRel condSelect384Code 0x42 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem cs4_at_44 : fetchRel condSelect384Code 0x44 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem cs4_at_46 : fetchRel condSelect384Code 0x46 = some (.jalr x0 ra 0x0, 2) := by decide
theorem cs2_at_0 : fetchRel condSelect256Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem cs2_at_2 : fetchRel condSelect256Code 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem cs2_at_4 : fetchRel condSelect256Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem cs2_at_6 : fetchRel condSelect256Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem cs2_at_8 : fetchRel condSelect256Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem cs2_at_a : fetchRel condSelect256Code 0xA = some (.alu .add (8 : Fin 32) x0 a3, 2) := by decide
theorem cs2_at_c : fetchRel condSelect256Code 0xC = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem cs2_at_e : fetchRel condSelect256Code 0xE = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem cs2_at_10 : fetchRel condSelect256Code 0x10 = some (.alu .add a0 x0 sp, 2) := by decide
theorem cs2_at_12 : fetchRel condSelect256Code 0x12 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem cs2_at_16 : fetchRel condSelect256Code 0x16 = some (.auipc ra 0x3000, 4) := by decide
theorem cs2_at_1a : fetchRel condSelect256Code 0x1A = some (.jalr ra ra 0x228, 4) := by decide
theorem cs2_at_1e : fetchRel condSelect256Code 0x1E = some (.alu .add a0 x0 sp, 2) := by decide
theorem cs2_at_20 : fetchRel condSelect256Code 0x20 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem cs2_at_22 : fetchRel condSelect256Code 0x22 = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem cs2_at_24 : fetchRel condSelect256Code 0x24 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem cs2_at_26 : fetchRel condSelect256Code 0x26 = some (.alu .add a4 x0 (8 : Fin 32), 2) := by decide
theorem cs2_at_28 : fetchRel condSelect256Code 0x28 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem cs2_at_2c : fetchRel condSelect256Code 0x2C = some (.jalr ra ra 0x4E, 4) := by decide
theorem cs2_at_30 : fetchRel condSelect256Code 0x30 = some (.alu .add a1 x0 sp, 2) := by decide
theorem cs2_at_32 : fetchRel condSelect256Code 0x32 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem cs2_at_36 : fetchRel condSelect256Code 0x36 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem cs2_at_38 : fetchRel condSelect256Code 0x38 = some (.auipc ra 0x3000, 4) := by decide
theorem cs2_at_3c : fetchRel condSelect256Code 0x3C = some (.jalr ra ra 0x206, 4) := by decide
theorem cs2_at_40 : fetchRel condSelect256Code 0x40 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem cs2_at_42 : fetchRel condSelect256Code 0x42 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem cs2_at_44 : fetchRel condSelect256Code 0x44 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem cs2_at_46 : fetchRel condSelect256Code 0x46 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem cs2_at_48 : fetchRel condSelect256Code 0x48 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem cs2_at_4a : fetchRel condSelect256Code 0x4A = some (.jalr x0 ra 0x0, 2) := by decide
theorem uo4_at_0 : fetchRel unwrapOr384Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem uo4_at_2 : fetchRel unwrapOr384Code 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem uo4_at_4 : fetchRel unwrapOr384Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem uo4_at_6 : fetchRel unwrapOr384Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem uo4_at_8 : fetchRel unwrapOr384Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem uo4_at_a : fetchRel unwrapOr384Code 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem uo4_at_c : fetchRel unwrapOr384Code 0xC = some (.alu .add (18 : Fin 32) x0 a2, 2) := by decide
theorem uo4_at_e : fetchRel unwrapOr384Code 0xE = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem uo4_at_10 : fetchRel unwrapOr384Code 0x10 = some (.load .lbu (8 : Fin 32) a1 0x64, 4) := by decide
theorem uo4_at_14 : fetchRel unwrapOr384Code 0x14 = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem uo4_at_16 : fetchRel unwrapOr384Code 0x16 = some (.alu .add a1 x0 a2, 2) := by decide
theorem uo4_at_18 : fetchRel unwrapOr384Code 0x18 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem uo4_at_1a : fetchRel unwrapOr384Code 0x1A = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem uo4_at_1c : fetchRel unwrapOr384Code 0x1C = some (.auipc ra 0x10000, 4) := by decide
theorem uo4_at_20 : fetchRel unwrapOr384Code 0x20 = some (.jalr ra ra 0x6F0, 4) := by decide
theorem uo4_at_24 : fetchRel unwrapOr384Code 0x24 = some (.aluImm .add a1 (18 : Fin 32) 0x30, 4) := by decide
theorem uo4_at_28 : fetchRel unwrapOr384Code 0x28 = some (.aluImm .add a2 (9 : Fin 32) 0x30, 4) := by decide
theorem uo4_at_2c : fetchRel unwrapOr384Code 0x2C = some (.aluImm .add a0 (19 : Fin 32) 0x30, 4) := by decide
theorem uo4_at_30 : fetchRel unwrapOr384Code 0x30 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem uo4_at_32 : fetchRel unwrapOr384Code 0x32 = some (.auipc ra 0x10000, 4) := by decide
theorem uo4_at_36 : fetchRel unwrapOr384Code 0x36 = some (.jalr ra ra 0x6DA, 4) := by decide
theorem uo4_at_3a : fetchRel unwrapOr384Code 0x3A = some (.load .lbu a0 (18 : Fin 32) 0x60, 4) := by decide
theorem uo4_at_3e : fetchRel unwrapOr384Code 0x3E = some (.load .lbu a1 (9 : Fin 32) 0x60, 4) := by decide
theorem uo4_at_42 : fetchRel unwrapOr384Code 0x42 = some (.alu .sub a2 x0 (8 : Fin 32), 4) := by decide
theorem uo4_at_46 : fetchRel unwrapOr384Code 0x46 = some (.alu .xor a1 a1 a0, 2) := by decide
theorem uo4_at_48 : fetchRel unwrapOr384Code 0x48 = some (.alu .and a1 a1 a2, 2) := by decide
theorem uo4_at_4a : fetchRel unwrapOr384Code 0x4A = some (.alu .xor a0 a0 a1, 2) := by decide
theorem uo4_at_4c : fetchRel unwrapOr384Code 0x4C = some (.store .sb (19 : Fin 32) a0 0x60, 4) := by decide
theorem uo4_at_50 : fetchRel unwrapOr384Code 0x50 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem uo4_at_52 : fetchRel unwrapOr384Code 0x52 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem uo4_at_54 : fetchRel unwrapOr384Code 0x54 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem uo4_at_56 : fetchRel unwrapOr384Code 0x56 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem uo4_at_58 : fetchRel unwrapOr384Code 0x58 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem uo4_at_5a : fetchRel unwrapOr384Code 0x5A = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem uo4_at_5c : fetchRel unwrapOr384Code 0x5C = some (.jalr x0 ra 0x0, 2) := by decide
theorem uo2_at_0 : fetchRel unwrapOr256Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem uo2_at_2 : fetchRel unwrapOr256Code 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem uo2_at_4 : fetchRel unwrapOr256Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem uo2_at_6 : fetchRel unwrapOr256Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem uo2_at_8 : fetchRel unwrapOr256Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem uo2_at_a : fetchRel unwrapOr256Code 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem uo2_at_c : fetchRel unwrapOr256Code 0xC = some (.alu .add (18 : Fin 32) x0 a2, 2) := by decide
theorem uo2_at_e : fetchRel unwrapOr256Code 0xE = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem uo2_at_10 : fetchRel unwrapOr256Code 0x10 = some (.load .lbu (8 : Fin 32) a1 0x44, 4) := by decide
theorem uo2_at_14 : fetchRel unwrapOr256Code 0x14 = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem uo2_at_16 : fetchRel unwrapOr256Code 0x16 = some (.alu .add a1 x0 a2, 2) := by decide
theorem uo2_at_18 : fetchRel unwrapOr256Code 0x18 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem uo2_at_1a : fetchRel unwrapOr256Code 0x1A = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem uo2_at_1c : fetchRel unwrapOr256Code 0x1C = some (.auipc ra 0xE000, 4) := by decide
theorem uo2_at_20 : fetchRel unwrapOr256Code 0x20 = some (.jalr ra ra 0x444, 4) := by decide
theorem uo2_at_24 : fetchRel unwrapOr256Code 0x24 = some (.aluImm .add a1 (18 : Fin 32) 0x20, 4) := by decide
theorem uo2_at_28 : fetchRel unwrapOr256Code 0x28 = some (.aluImm .add a2 (9 : Fin 32) 0x20, 4) := by decide
theorem uo2_at_2c : fetchRel unwrapOr256Code 0x2C = some (.aluImm .add a0 (19 : Fin 32) 0x20, 4) := by decide
theorem uo2_at_30 : fetchRel unwrapOr256Code 0x30 = some (.alu .add a3 x0 (8 : Fin 32), 2) := by decide
theorem uo2_at_32 : fetchRel unwrapOr256Code 0x32 = some (.auipc ra 0xE000, 4) := by decide
theorem uo2_at_36 : fetchRel unwrapOr256Code 0x36 = some (.jalr ra ra 0x42E, 4) := by decide
theorem uo2_at_3a : fetchRel unwrapOr256Code 0x3A = some (.load .lbu a0 (18 : Fin 32) 0x40, 4) := by decide
theorem uo2_at_3e : fetchRel unwrapOr256Code 0x3E = some (.load .lbu a1 (9 : Fin 32) 0x40, 4) := by decide
theorem uo2_at_42 : fetchRel unwrapOr256Code 0x42 = some (.alu .sub a2 x0 (8 : Fin 32), 4) := by decide
theorem uo2_at_46 : fetchRel unwrapOr256Code 0x46 = some (.alu .xor a1 a1 a0, 2) := by decide
theorem uo2_at_48 : fetchRel unwrapOr256Code 0x48 = some (.alu .and a1 a1 a2, 2) := by decide
theorem uo2_at_4a : fetchRel unwrapOr256Code 0x4A = some (.alu .xor a0 a0 a1, 2) := by decide
theorem uo2_at_4c : fetchRel unwrapOr256Code 0x4C = some (.store .sb (19 : Fin 32) a0 0x40, 4) := by decide
theorem uo2_at_50 : fetchRel unwrapOr256Code 0x50 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem uo2_at_52 : fetchRel unwrapOr256Code 0x52 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem uo2_at_54 : fetchRel unwrapOr256Code 0x54 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem uo2_at_56 : fetchRel unwrapOr256Code 0x56 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem uo2_at_58 : fetchRel unwrapOr256Code 0x58 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem uo2_at_5a : fetchRel unwrapOr256Code 0x5A = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem uo2_at_5c : fetchRel unwrapOr256Code 0x5C = some (.jalr x0 ra 0x0, 2) := by decide
theorem cm4_at_0 : fetchRel ctMap384Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem cm4_at_2 : fetchRel ctMap384Code 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem cm4_at_4 : fetchRel ctMap384Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem cm4_at_6 : fetchRel ctMap384Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem cm4_at_8 : fetchRel ctMap384Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem cm4_at_a : fetchRel ctMap384Code 0xA = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem cm4_at_c : fetchRel ctMap384Code 0xC = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem cm4_at_e : fetchRel ctMap384Code 0xE = some (.alu .add a0 x0 sp, 2) := by decide
theorem cm4_at_10 : fetchRel ctMap384Code 0x10 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem cm4_at_14 : fetchRel ctMap384Code 0x14 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem cm4_at_16 : fetchRel ctMap384Code 0x16 = some (.auipc ra 0x1000, 4) := by decide
theorem cm4_at_1a : fetchRel ctMap384Code 0x1A = some (.jalr ra ra 0xFFFFFEB0, 4) := by decide
theorem cm4_at_1e : fetchRel ctMap384Code 0x1E = some (.load .lbu (9 : Fin 32) (8 : Fin 32) 0x30, 4) := by decide
theorem cm4_at_22 : fetchRel ctMap384Code 0x22 = some (.alu .add a1 x0 sp, 2) := by decide
theorem cm4_at_24 : fetchRel ctMap384Code 0x24 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem cm4_at_26 : fetchRel ctMap384Code 0x26 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem cm4_at_28 : fetchRel ctMap384Code 0x28 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem cm4_at_2a : fetchRel ctMap384Code 0x2A = some (.auipc ra 0x0, 4) := by decide
theorem cm4_at_2e : fetchRel ctMap384Code 0x2E = some (.jalr ra ra 0xFFFFFEEA, 4) := by decide
theorem cm4_at_32 : fetchRel ctMap384Code 0x32 = some (.store .sb (18 : Fin 32) (9 : Fin 32) 0x30, 4) := by decide
theorem cm4_at_36 : fetchRel ctMap384Code 0x36 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem cm4_at_38 : fetchRel ctMap384Code 0x38 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem cm4_at_3a : fetchRel ctMap384Code 0x3A = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem cm4_at_3c : fetchRel ctMap384Code 0x3C = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem cm4_at_3e : fetchRel ctMap384Code 0x3E = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem cm4_at_40 : fetchRel ctMap384Code 0x40 = some (.jalr x0 ra 0x0, 2) := by decide
theorem cm2_at_0 : fetchRel ctMap256Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem cm2_at_2 : fetchRel ctMap256Code 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem cm2_at_4 : fetchRel ctMap256Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem cm2_at_6 : fetchRel ctMap256Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem cm2_at_8 : fetchRel ctMap256Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem cm2_at_a : fetchRel ctMap256Code 0xA = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem cm2_at_c : fetchRel ctMap256Code 0xC = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem cm2_at_e : fetchRel ctMap256Code 0xE = some (.alu .add a0 x0 sp, 2) := by decide
theorem cm2_at_10 : fetchRel ctMap256Code 0x10 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem cm2_at_14 : fetchRel ctMap256Code 0x14 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem cm2_at_16 : fetchRel ctMap256Code 0x16 = some (.auipc ra 0x3000, 4) := by decide
theorem cm2_at_1a : fetchRel ctMap256Code 0x1A = some (.jalr ra ra 0xFFFFFDDA, 4) := by decide
theorem cm2_at_1e : fetchRel ctMap256Code 0x1E = some (.load .lbu (9 : Fin 32) (8 : Fin 32) 0x20, 4) := by decide
theorem cm2_at_22 : fetchRel ctMap256Code 0x22 = some (.alu .add a1 x0 sp, 2) := by decide
theorem cm2_at_24 : fetchRel ctMap256Code 0x24 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem cm2_at_26 : fetchRel ctMap256Code 0x26 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem cm2_at_28 : fetchRel ctMap256Code 0x28 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem cm2_at_2a : fetchRel ctMap256Code 0x2A = some (.auipc ra 0x0, 4) := by decide
theorem cm2_at_2e : fetchRel ctMap256Code 0x2E = some (.jalr ra ra 0xFFFFFBF0, 4) := by decide
theorem cm2_at_32 : fetchRel ctMap256Code 0x32 = some (.store .sb (18 : Fin 32) (9 : Fin 32) 0x20, 4) := by decide
theorem cm2_at_36 : fetchRel ctMap256Code 0x36 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem cm2_at_38 : fetchRel ctMap256Code 0x38 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem cm2_at_3a : fetchRel ctMap256Code 0x3A = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem cm2_at_3c : fetchRel ctMap256Code 0x3C = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem cm2_at_3e : fetchRel ctMap256Code 0x3E = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem cm2_at_40 : fetchRel ctMap256Code 0x40 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem cs_copy_in {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  have e : dst + BitVec.ofNat 32 i - dst = BitVec.ofNat 32 i := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
  unfold copyBytes
  rw [e, ite_eq_left (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)]

abbrev cs4Ps : List (Fin 32 × Word) := [(ra, 0x3C), ((8 : Fin 32), 0x38), ((9 : Fin 32), 0x34), ((18 : Fin 32), 0x30)]

section
set_option maxRecDepth 20000
theorem cs4Save_end : blockEnd condSelect384Code 2 (saveBlock cs4Ps) = some 0xA := by decide
theorem cs4Restore_end : blockEnd condSelect384Code 0x3C (restoreBlock cs4Ps) = some 0x44 := by decide
end

/-- Where the P-384 field `conditional_select` runs: its code and its
callees', the 0x60 bytes of stack below `sp0`, the result `out`, and the
operands `a` and `b`. -/
structure CSEnv (M : Word → BitVec 8) (P sp0 out a b : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P condSelect384Code
  stub : CodeIn M (P + 0x101A) memcpyStubCode
  body : CodeIn M (P + 0x101A + 8) memcpyBodyCode
  cta : CodeIn M (P + 0x2EC) uint12CtAssignCode
  sca : CodeIn M (P + 0x2EC + 0xFFFF9B66) sliceCtAssignCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x60 ≤ sp0.toNat
  hb : b.toNat % 4 = 0
  haw : a.toNat + 48 < 2 ^ 32
  how : out.toNat + 48 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFFA0) 0x60 P condSelect384Code.length
  sGS : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x101A) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x101A + 8) memcpyBodyCode.length
  sGT : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x2EC) uint12CtAssignCode.length
  sGA : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x2EC + 0xFFFF9B66) sliceCtAssignCode.length
  sOC : Sep out 48 P condSelect384Code.length
  sOB : Sep out 48 (P + 0x101A + 8) memcpyBodyCode.length
  sOG : Sep out 48 (sp0 + 0xFFFFFFA0) 0x60
  sAG : Sep a 48 (sp0 + 0xFFFFFFA0) 0x60
  sBG : Sep b 48 (sp0 + 0xFFFFFFA0) 0x60

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled P-384 field `conditional_select`**: it stores at `out`
the 12 limbs of `b` when the choice `c` is 1 and those of `a` when it is 0. -/
theorem condSelect384_correct (m : Machine) {P sp0 out a b c retAddr : Word} (env : CSEnv m.mem P sp0 out a b)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = a) (ha2 : reg m a2 = b)
    (ha3 : reg m a3 = c) (hc : c = 0 ∨ c = 1) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 12 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 m.mem (b + BitVec.ofNat 32 (4 * i)) else memLoad32 m.mem (a + BitVec.ofNat 32 (4 * i))) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFA0 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGS := env.sGS; have sGB := env.sGB; have sGT := env.sGT; have sGA := env.sGA
  have sOG := env.sOG; have sAG := env.sAG; have sBG := env.sBG
  rw [hG] at sGC sGS sGB sGT sGA sOG sAG sBG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFC0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFFA0) (by decide)
  have hGw : G.toNat + 0x60 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFA0 : Word).toNat = 4294967200 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0x20) (by decide)
  have hFn : F.toNat = G.toNat + 0x20 := by
    rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x40 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eT : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x10 := by rw [← eGF, BitVec.add_assoc]; rfl
  have eU : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  -- the pieces of `G`: the callees' scratch, the copy, and the saved registers
  have pT : ∀ {y : Word}, Sep G 0x60 y 1 → Sep (F + 0xFFFFFFF0) 16 y 1 := fun h => by
    rw [eT]; exact h.sub (c := 0x10) (l := 16) (by decide)
  have pU : ∀ {y : Word}, Sep G 0x60 y 1 → Sep (F + 0xFFFFFFE0) 0x20 y 1 := fun h => by
    rw [eU]; exact h.sub (c := 0) (l := 0x20) (by decide)
  have pF : ∀ {y : Word} {l : Nat}, Sep G 0x60 y l → Sep F 48 y l := fun h => by
    rw [← eGF]; exact h.sub (c := 0x20) (l := 48) (by decide)
  have pF' : ∀ {y : Word} {l : Nat}, Sep y l G 0x60 → Sep y l F 48 := fun h => by
    rw [← eGF]; exact h.subR (c := 0x20) (l := 48) (by decide)
  have gw : G.toNat + 0x60 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x60 → d + k ≤ 0x60 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x60 b code'.length → (∀ y, Sep G 0x60 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod cs4_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have slotC : ∀ (o : Word), 0x30 ≤ o.toNat → o.toNat + 4 ≤ 0x40 → ∀ {b : Word} {l : Nat}, Sep G 0x60 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x20 + o.toNat) (l := 4) (by omega)
  have slotG : ∀ o : Word, 0x30 ≤ o.toNat → o.toNat + 4 ≤ 0x40 → ∀ y, Sep G 0x60 y 1 → Sep (F + o) 4 y 1 := by
    intro o h1 h2 y hy
    rw [← ofNat_toNat_self o, eFk]; exact hy.sub (c := 0x20 + o.toNat) (l := 4) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock cs4Ps) u1 env.cod cs4Save_end (saveBlock_ok _ cs4Ps _ fun p hp => by
    rw [sp1]
    simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
    exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0)) cs4Ps = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep G 0x60 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside cs4Ps fun p hp => by
      simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact slotG _ (by decide) (by decide) y hy
  have hslv : ∀ r o, (r, o) ∈ cs4Ps → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hc2 : CodeIn Msv P condSelect384Code := cIn env.cod sGC frSv
  -- copy `a` to the stack
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (8 : Fin 32) x0 a3, .alu .add (9 : Fin 32) x0 a2,
    .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp, .aluImm .add a2 x0 0x30] u2.self hc2 (off' := 0x16)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have z2 := u2.self.zero
  have v38 : reg m3 8 = c := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [z2, r2 a3 (by decide), ha3]; exact zw c
  have v39 : reg m3 9 = b := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a2 (by decide), ha2]; exact zw b
  have v318 : reg m3 18 = out := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw out
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a2 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
      reg m3 q = reg m2 q := fun q hv h0 h2 h8 h9 h18 => by
    rw [u3.regs, upd_ne hv h2, upd_ne hv h0, upd_ne hv h18, upd_ne hv h9, upd_ne hv h8]
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hc2 cs4_at_16 cs4_at_1a (cb := P + 0x101A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x101A (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have sp4 : reg m4 sp = F := by
    rw [r4 sp (by decide), k3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  have hFw : (F + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by
    rw [eT, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have E1 : McEnv Msv (P + 0x101A + 8) F a (F + 0xFFFFFFF0) 48 :=
    ⟨cIn env.body sGB frSv, pF sGB, by rw [eT]; exact sGB.sub (c := 0x10) (l := 16) (by decide),
      by rw [eT, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide),
      by rw [eT]; exact sAG.subR (c := 0x10) (l := 16) (by decide), (pF' sAG).symm,
      aligned_add hFa (by decide), hFw, by omega, env.haw⟩
  obtain ⟨m5, c5, pc5, sp5, _, f5, k5⟩ := memcpy_correct m4 (P + 0x101A) _ F a 48
    (fun i hi => by show m4.mem _ = _; rw [mem4]; exact cIn env.stub sGS frSv i hi)
    (even_at P env.hP 0x101A (by decide)) pc4
    (by rw [r4 a0 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact zw F)
    (by rw [r4 a1 (by decide), k3 a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          r2 a1 (by decide), ha1])
    (by rw [r4 a2 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x16 + 8) (by decide)))
    (by rw [mem4, sp4]; exact E1)
  rw [sp4, mem4] at f5
  rw [sp4] at sp5
  have fr5 : ∀ y, Sep G 0x60 y 1 → m5.mem y = m.mem y := fun y hy => by
    rw [f5 y (pT hy), copyBytes_sep (pF hy) (Nat.le_refl 48), frSv y hy]
  have hc5 : CodeIn m5.mem P condSelect384Code := cIn env.cod sGC fr5
  have u5 : St m5.mem P m5 (0x16 + 8) (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have k5' : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] → reg m5 q = reg m4 q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, ht0, ht1, h7', h28, h29, h30, hs⟩ : q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧
      q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧
      q ≠ (30 : Fin 32) ∧ q ≠ sp := by revert hq; revert q; decide
    exact k5 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs
  -- assign `b` under the choice
  obtain ⟨m6, c6, u6⟩ := St.block [.alu .add a0 x0 sp, .alu .add a1 x0 (9 : Fin 32), .alu .add a2 x0 (8 : Fin 32)]
    u5 hc5 (off' := 0x24) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u6
  have z5 := u5.zero
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6.self.callRa hc5 cs4_at_24 cs4_at_28 (cb := P + 0x2EC)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x2EC (by decide))
  have r7 := PEnv.reg1 regs7 u6.self.zero
  have k6 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m6 q = reg m5 q := fun q hv h0 h1 h2 => by
    rw [u6.regs, upd_ne hv h2, upd_ne hv h1, upd_ne hv h0]
  have v58 : reg m5 8 = c := by
    rw [k5' 8 (by decide), r4 8 (by decide), v38]
  have v59 : reg m5 9 = b := by rw [k5' 9 (by decide), r4 9 (by decide), v39]
  have sp7 : reg m7 sp = F := by
    rw [r7 sp (by decide), k6 sp (by decide) (by decide) (by decide) (by decide), sp5]
  obtain ⟨m8, c8, pc8, sp8, v8, f8, k8⟩ := uint12CtAssign_correct m7 (W := P + 0x2EC) (sp0 := F) (dst := F)
    (src := b) (c := c) (even_at P env.hP 0x2EC (by decide)) (by rw [mem7]; exact cIn env.cta sGT fr5)
    (by rw [mem7]; exact cIn env.sca sGA fr5) pc7 sp7 hFa (by omega)
    (by rw [r7 a0 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [z5, sp5]; exact zw F)
    (by rw [r7 a1 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v59]; exact zw b)
    (by rw [r7 a2 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v58]; exact zw c)
    hc (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x24 + 8) (by decide)))
    hFa env.hb (by omega) (by rw [eU]; exact sGA.sub (c := 0) (l := 0x20) (by decide)) (pF sGA)
    (by rw [eU, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide))
    (by rw [eU]; exact sBG.subR (c := 0) (l := 0x20) (by decide)) (pF' sBG).symm
  rw [mem7] at v8 f8
  have fr8 : ∀ y, Sep G 0x60 y 1 → m8.mem y = m.mem y := fun y hy => by
    rw [f8 y (pU hy) (pF hy), fr5 y hy]
  have hc8 : CodeIn m8.mem P condSelect384Code := cIn env.cod sGC fr8
  have u8 : St m8.mem P m8 (0x24 + 8) (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  have k8' : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] → reg m8 q = reg m7 q :=
    fun q hq => k8 q (by revert hq; revert q; decide)
  -- copy the result to `out`
  obtain ⟨m9, c9, u9⟩ := St.block [.alu .add a1 x0 sp, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]
    u8 hc8 (off' := 0x34) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u9
  have z8 := u8.zero
  obtain ⟨m10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hc8 cs4_at_34 cs4_at_38 (cb := P + 0x101A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x101A (by decide))
  have r10 := PEnv.reg1 regs10 u9.self.zero
  have k9 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m9 q = reg m8 q := fun q hv h0 h1 h2 => by
    rw [u9.regs, upd_ne hv h0, upd_ne hv h2, upd_ne hv h1]
  have k7_4 : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] → q ≠ ra →
      reg m8 q = reg m4 q := fun q hq hr => by
    have h' : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 := by revert hq; revert q; decide
    rw [k8' q hq, r7 q hr, k6 q h'.1 h'.2.1 h'.2.2.1 h'.2.2.2, k5' q hq]
  have sp10 : reg m10 sp = F := by
    rw [r10 sp (by decide), k9 sp (by decide) (by decide) (by decide) (by decide), sp8]
  have E2 : McEnv m8.mem (P + 0x101A + 8) out F (F + 0xFFFFFFF0) 48 :=
    ⟨cIn env.body sGB fr8, env.sOB, by rw [eT]; exact sGB.sub (c := 0x10) (l := 16) (by decide),
      by rw [eT]; exact sOG.subR (c := 0x10) (l := 16) (by decide),
      by rw [eT, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide), pF' sOG,
      aligned_add hFa (by decide), hFw, env.how, by omega⟩
  obtain ⟨m11, c11, pc11, sp11, _, f11, k11⟩ := memcpy_correct m10 (P + 0x101A) _ out F 48
    (fun i hi => by show m10.mem _ = _; rw [mem10]; exact cIn env.stub sGS fr8 i hi)
    (even_at P env.hP 0x101A (by decide)) pc10
    (by rw [r10 a0 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [k7_4 18 (by decide) (by decide), r4 18 (by decide), v318]; exact zw out)
    (by rw [r10 a1 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [z8, sp8]; exact zw F)
    (by rw [r10 a2 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs10]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x34 + 8) (by decide)))
    (by rw [mem10, sp10]; exact E2)
  rw [sp10, mem10] at f11
  rw [sp10] at sp11
  have fr11 : ∀ y, Sep G 0x60 y 1 → Sep out 48 y 1 → m11.mem y = m.mem y := fun y hy ho => by
    rw [f11 y (pT hy), copyBytes_sep ho (Nat.le_refl 48), fr8 y hy]
  have hc11 : CodeIn m11.mem P condSelect384Code := fun i hi => by
    rw [fr11 _ (sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  -- the saved registers
  have slotM : ∀ k, 0x50 ≤ k → k < 0x60 → m11.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    have hT : Sep (F + 0xFFFFFFF0) 16 (G + BitVec.ofNat 32 k) 1 := by
      rw [eT]; exact offs (.inl (by omega)) (by decide) (by omega)
    have hU : Sep (F + 0xFFFFFFE0) 0x20 (G + BitVec.ofNat 32 k) 1 := by
      rw [eU]; exact offs (.inl (by omega)) (by decide) (by omega)
    have hF' : Sep F 48 (G + BitVec.ofNat 32 k) 1 := by
      rw [← eGF]; exact offs (.inl (by omega)) (by decide) (by omega)
    rw [f11 _ hT, copyBytes_sep (sOG.subR (c := k) (l := 1) (by omega)) (Nat.le_refl 48), f8 _ hU hF', f5 _ hT,
      copyBytes_sep hF' (Nat.le_refl 48)]
  have slotW : ∀ r o, (r, o) ∈ cs4Ps → memLoad32 m11.mem (F + o) = reg m r := fun r o h => by
    have ho : 0x30 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x40 := by
      simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, eFk, slotM _ (by omega) (by omega)]
  have hpsp : ∀ p ∈ cs4Ps, p.1 ≠ sp := by decide
  have u11 : St m11.mem P m11 (0x34 + 8) (reg m11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
  have sp11' : reg m11 sp = F := sp11
  obtain ⟨n1, e1, w1⟩ := St.block (restoreBlock cs4Ps) u11 hc11 cs4Restore_end
    (restoreBlock_ok m11.mem F cs4Ps (reg m11) sp11' hpsp fun q hq => by
      simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run m11.mem F cs4Ps (reg m11) sp11' hpsp] at w1
  have rsp1 : restoreRegs m11.mem F (reg m11) cs4Ps sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp11'
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs m11.mem F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ cs4Ps → restoreRegs m11.mem F (reg m11) cs4Ps r = reg m r := fun r o hm => by
    simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, e2, w2⟩ := w1.aluImm hc11 cs4_at_44 (off' := 0x46) (by decide)
  obtain ⟨n3, e3, pc3, mem3, regs3⟩ := w2.jalr hc11 cs4_at_46
  have k11' : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m11 q = reg m q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, ht0, ht1, h7', h28, h29, h30, hs, hr, hv, h0, h8, h9, h18⟩ :
      q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧
      q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ sp ∧ q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧
      q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) := by revert hq; revert q; decide
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] := by
      clear h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs hr hv h0 h8 h9 h18; revert hq; revert q; decide
    rw [k11 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs, r10 q hr, k9 q hv h0 h1 h2, k7_4 q hq' hr, r4 q hr,
      k3 q hv h0 h2 h8 h9 h18, r2 q hs]
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (e1.trans (.cons e2 (.single e3))))))))))))), ?_, ?_, fun i hi => ?_,
    fun q hq => ?_, fun x hx ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x3C (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
  · have eo : ∀ j, j < 4 → m11.mem (out + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j) =
        m8.mem (F + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j) := fun j hj => by
      have hs : Sep (F + 0xFFFFFFF0) 16 (out + BitVec.ofNat 32 (4 * i + j)) 1 := by
        rw [eT]; exact (sOG.symm.sub (c := 0x10) (l := 16) (by decide)).subR (c := 4 * i + j) (l := 1) (by omega)
      rw [add_ofNat_assoc, add_ofNat_assoc, f11 _ hs, cs_copy_in (by omega) (by decide)]
    rw [mem3, memLoad32_congr2 eo, v8 i hi]
    have eb : memLoad32 m5.mem (b + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (b + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact fr5 _ (sBG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    have ea : memLoad32 m5.mem (F + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (a + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr2 fun j hj => by
        rw [add_ofNat_assoc, add_ofNat_assoc,
          f5 _ (by rw [eT, ← eGF, add_ofNat_assoc]; exact offs (.inl (by omega)) (by decide) (by omega)),
          cs_copy_in (by omega) (by decide), frSv _ (sAG.sub (c := 4 * i + j) (l := 1) (by omega)).symm]
    rw [eb, ea]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        (q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ cs4Ps, p.1 ≠ q)) := by
      decide
    rcases key q hq with rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x3C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x38 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x34 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x30 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact k11' q h1
  · rw [mem3]; exact fr11 x hx ho

abbrev cs2Ps : List (Fin 32 × Word) := [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20)]

section
set_option maxRecDepth 20000
theorem cs2Save_end : blockEnd condSelect256Code 2 (saveBlock cs2Ps) = some 0xA := by decide
theorem cs2Restore_end : blockEnd condSelect256Code 0x40 (restoreBlock cs2Ps) = some 0x48 := by decide
end

/-- Where the P-256 field `conditional_select` runs: its code and its
callees', the 0x50 bytes of stack below `sp0`, the result `out`, and the
operands `a` and `b`. -/
structure CS2Env (M : Word → BitVec 8) (P sp0 out a b : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P condSelect256Code
  stub : CodeIn M (P + 0x323E) memcpyStubCode
  body : CodeIn M (P + 0x323E + 8) memcpyBodyCode
  sca : CodeIn M (P + 0xFFFFC076) sliceCtAssignCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x50 ≤ sp0.toNat
  hb : b.toNat % 4 = 0
  haw : a.toNat + 32 < 2 ^ 32
  how : out.toNat + 32 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFFB0) 0x50 P condSelect256Code.length
  sGS : Sep (sp0 + 0xFFFFFFB0) 0x50 (P + 0x323E) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFFB0) 0x50 (P + 0x323E + 8) memcpyBodyCode.length
  sGA : Sep (sp0 + 0xFFFFFFB0) 0x50 (P + 0xFFFFC076) sliceCtAssignCode.length
  sOC : Sep out 32 P condSelect256Code.length
  sOB : Sep out 32 (P + 0x323E + 8) memcpyBodyCode.length
  sOG : Sep out 32 (sp0 + 0xFFFFFFB0) 0x50
  sAG : Sep a 32 (sp0 + 0xFFFFFFB0) 0x50
  sBG : Sep b 32 (sp0 + 0xFFFFFFB0) 0x50

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled P-256 field `conditional_select`**: it stores at `out`
the 8 limbs of `b` when the choice `c` is 1 and those of `a` when it is 0. -/
theorem condSelect256_correct (m : Machine) {P sp0 out a b c retAddr : Word} (env : CS2Env m.mem P sp0 out a b)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = a) (ha2 : reg m a2 = b)
    (ha3 : reg m a3 = c) (hc : c = 0 ∨ c = 1) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 8 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 m.mem (b + BitVec.ofNat 32 (4 * i)) else memLoad32 m.mem (a + BitVec.ofNat 32 (4 * i))) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFB0 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGS := env.sGS; have sGB := env.sGB; have sGA := env.sGA
  have sOG := env.sOG; have sAG := env.sAG; have sBG := env.sBG
  rw [hG] at sGC sGS sGB sGA sOG sAG sBG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFD0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFFB0) (by decide)
  have hGw : G.toNat + 0x50 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFB0 : Word).toNat = 4294967216 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0x20) (by decide)
  have hFn : F.toNat = G.toNat + 0x20 := by
    rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x30 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eT : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x10 := by rw [← eGF, BitVec.add_assoc]; rfl
  have eU : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  -- the pieces of `G`: the callees' scratch, the copy, and the saved registers
  have pT : ∀ {y : Word}, Sep G 0x50 y 1 → Sep (F + 0xFFFFFFF0) 16 y 1 := fun h => by
    rw [eT]; exact h.sub (c := 0x10) (l := 16) (by decide)
  have pU : ∀ {y : Word}, Sep G 0x50 y 1 → Sep (F + 0xFFFFFFE0) 0x20 y 1 := fun h => by
    rw [eU]; exact h.sub (c := 0) (l := 0x20) (by decide)
  have pF : ∀ {y : Word} {l : Nat}, Sep G 0x50 y l → Sep F 32 y l := fun h => by
    rw [← eGF]; exact h.sub (c := 0x20) (l := 32) (by decide)
  have pF' : ∀ {y : Word} {l : Nat}, Sep y l G 0x50 → Sep y l F 32 := fun h => by
    rw [← eGF]; exact h.subR (c := 0x20) (l := 32) (by decide)
  have gw : G.toNat + 0x50 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x50 → d + k ≤ 0x50 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x50 b code'.length → (∀ y, Sep G 0x50 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod cs2_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have slotC : ∀ (o : Word), 0x20 ≤ o.toNat → o.toNat + 4 ≤ 0x30 → ∀ {b : Word} {l : Nat}, Sep G 0x50 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x20 + o.toNat) (l := 4) (by omega)
  have slotG : ∀ o : Word, 0x20 ≤ o.toNat → o.toNat + 4 ≤ 0x30 → ∀ y, Sep G 0x50 y 1 → Sep (F + o) 4 y 1 := by
    intro o h1 h2 y hy
    rw [← ofNat_toNat_self o, eFk]; exact hy.sub (c := 0x20 + o.toNat) (l := 4) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock cs2Ps) u1 env.cod cs2Save_end (saveBlock_ok _ cs2Ps _ fun p hp => by
    rw [sp1]
    simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
    exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) cs2Ps = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep G 0x50 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside cs2Ps fun p hp => by
      simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact slotG _ (by decide) (by decide) y hy
  have hslv : ∀ r o, (r, o) ∈ cs2Ps → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hc2 : CodeIn Msv P condSelect256Code := cIn env.cod sGC frSv
  -- copy `a` to the stack
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (8 : Fin 32) x0 a3, .alu .add (9 : Fin 32) x0 a2,
    .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp, .aluImm .add a2 x0 0x20] u2.self hc2 (off' := 0x16)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have z2 := u2.self.zero
  have v38 : reg m3 8 = c := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [z2, r2 a3 (by decide), ha3]; exact zw c
  have v39 : reg m3 9 = b := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a2 (by decide), ha2]; exact zw b
  have v318 : reg m3 18 = out := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw out
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a2 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
      reg m3 q = reg m2 q := fun q hv h0 h2 h8 h9 h18 => by
    rw [u3.regs, upd_ne hv h2, upd_ne hv h0, upd_ne hv h18, upd_ne hv h9, upd_ne hv h8]
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hc2 cs2_at_16 cs2_at_1a (cb := P + 0x323E)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x323E (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have sp4 : reg m4 sp = F := by
    rw [r4 sp (by decide), k3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  have hFw : (F + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by
    rw [eT, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have E1 : McEnv Msv (P + 0x323E + 8) F a (F + 0xFFFFFFF0) 32 :=
    ⟨cIn env.body sGB frSv, pF sGB, by rw [eT]; exact sGB.sub (c := 0x10) (l := 16) (by decide),
      by rw [eT, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide),
      by rw [eT]; exact sAG.subR (c := 0x10) (l := 16) (by decide), (pF' sAG).symm,
      aligned_add hFa (by decide), hFw, by omega, env.haw⟩
  obtain ⟨m5, c5, pc5, sp5, _, f5, k5⟩ := memcpy_correct m4 (P + 0x323E) _ F a 32
    (fun i hi => by show m4.mem _ = _; rw [mem4]; exact cIn env.stub sGS frSv i hi)
    (even_at P env.hP 0x323E (by decide)) pc4
    (by rw [r4 a0 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact zw F)
    (by rw [r4 a1 (by decide), k3 a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          r2 a1 (by decide), ha1])
    (by rw [r4 a2 (by decide), u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x16 + 8) (by decide)))
    (by rw [mem4, sp4]; exact E1)
  rw [sp4, mem4] at f5
  rw [sp4] at sp5
  have fr5 : ∀ y, Sep G 0x50 y 1 → m5.mem y = m.mem y := fun y hy => by
    rw [f5 y (pT hy), copyBytes_sep (pF hy) (Nat.le_refl 32), frSv y hy]
  have hc5 : CodeIn m5.mem P condSelect256Code := cIn env.cod sGC fr5
  have u5 : St m5.mem P m5 (0x16 + 8) (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have k5' : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] → reg m5 q = reg m4 q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, ht0, ht1, h7', h28, h29, h30, hs⟩ : q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧
      q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧
      q ≠ (30 : Fin 32) ∧ q ≠ sp := by revert hq; revert q; decide
    exact k5 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs
  -- assign `b` under the choice
  obtain ⟨m6, c6, u6⟩ := St.block [.alu .add a0 x0 sp, .aluImm .add a1 x0 8, .aluImm .add a3 x0 8,
    .alu .add a2 x0 (9 : Fin 32), .alu .add a4 x0 (8 : Fin 32)] u5 hc5 (off' := 0x28) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u6
  have z5 := u5.zero
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6.self.callRa hc5 cs2_at_28 cs2_at_2c (cb := P + 0xFFFFC076)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFC076 (by decide))
  have r7 := PEnv.reg1 regs7 u6.self.zero
  have k6 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg m6 q = reg m5 q :=
    fun q hv h0 h1 h2 h3 h4 => by
      rw [u6.regs, upd_ne hv h4, upd_ne hv h2, upd_ne hv h3, upd_ne hv h1, upd_ne hv h0]
  have v58 : reg m5 8 = c := by
    rw [k5' 8 (by decide), r4 8 (by decide), v38]
  have v59 : reg m5 9 = b := by rw [k5' 9 (by decide), r4 9 (by decide), v39]
  have sp7 : reg m7 sp = F := by
    rw [r7 sp (by decide), k6 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp5]
  obtain ⟨m8, c8, pc8, sp8, v8, f8, k8⟩ := sliceCtAssign_correct m7 (B := P + 0xFFFFC076) (sp0 := F) (dst := F)
    (src := b) (c := c) (n := 8) (by rw [mem7]; exact cIn env.sca sGA fr5) pc7 sp7 hFa (by omega)
    (by rw [r7 a0 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [z5, sp5]; exact zw F)
    (by rw [r7 a1 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [r7 a2 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v59]; exact zw b)
    (by rw [r7 a3 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [r7 a4 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v58]; exact zw c)
    hc (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x28 + 8) (by decide)))
    hFa env.hb (by omega) (by rw [eU]; exact sGA.sub (c := 0) (l := 0x20) (by decide)) (pF sGA)
    (by rw [eU, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide))
    (by rw [eU]; exact sBG.subR (c := 0) (l := 0x20) (by decide)) (pF' sBG).symm
  rw [mem7] at v8 f8
  have fr8 : ∀ y, Sep G 0x50 y 1 → m8.mem y = m.mem y := fun y hy => by
    rw [f8 y (pU hy) (pF hy), fr5 y hy]
  have hc8 : CodeIn m8.mem P condSelect256Code := cIn env.cod sGC fr8
  have u8 : St m8.mem P m8 (0x28 + 8) (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  have k8' : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] → reg m8 q = reg m7 q :=
    fun q hq => k8 q (by revert hq; revert q; decide)
  -- copy the result to `out`
  obtain ⟨m9, c9, u9⟩ := St.block [.alu .add a1 x0 sp, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (18 : Fin 32)]
    u8 hc8 (off' := 0x38) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u9
  have z8 := u8.zero
  obtain ⟨m10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hc8 cs2_at_38 cs2_at_3c (cb := P + 0x323E)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x323E (by decide))
  have r10 := PEnv.reg1 regs10 u9.self.zero
  have k9 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m9 q = reg m8 q := fun q hv h0 h1 h2 => by
    rw [u9.regs, upd_ne hv h0, upd_ne hv h2, upd_ne hv h1]
  have k7_4 : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] → q ≠ ra →
      reg m8 q = reg m4 q := fun q hq hr => by
    have h' : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 := by revert hq; revert q; decide
    rw [k8' q hq, r7 q hr, k6 q h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1 h'.2.2.2.2.1 h'.2.2.2.2.2, k5' q hq]
  have sp10 : reg m10 sp = F := by
    rw [r10 sp (by decide), k9 sp (by decide) (by decide) (by decide) (by decide), sp8]
  have E2 : McEnv m8.mem (P + 0x323E + 8) out F (F + 0xFFFFFFF0) 32 :=
    ⟨cIn env.body sGB fr8, env.sOB, by rw [eT]; exact sGB.sub (c := 0x10) (l := 16) (by decide),
      by rw [eT]; exact sOG.subR (c := 0x10) (l := 16) (by decide),
      by rw [eT, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide), pF' sOG,
      aligned_add hFa (by decide), hFw, env.how, by omega⟩
  obtain ⟨m11, c11, pc11, sp11, _, f11, k11⟩ := memcpy_correct m10 (P + 0x323E) _ out F 32
    (fun i hi => by show m10.mem _ = _; rw [mem10]; exact cIn env.stub sGS fr8 i hi)
    (even_at P env.hP 0x323E (by decide)) pc10
    (by rw [r10 a0 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [k7_4 18 (by decide) (by decide), r4 18 (by decide), v318]; exact zw out)
    (by rw [r10 a1 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [z8, sp8]; exact zw F)
    (by rw [r10 a2 (by decide), u9.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs10]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x38 + 8) (by decide)))
    (by rw [mem10, sp10]; exact E2)
  rw [sp10, mem10] at f11
  rw [sp10] at sp11
  have fr11 : ∀ y, Sep G 0x50 y 1 → Sep out 32 y 1 → m11.mem y = m.mem y := fun y hy ho => by
    rw [f11 y (pT hy), copyBytes_sep ho (Nat.le_refl 32), fr8 y hy]
  have hc11 : CodeIn m11.mem P condSelect256Code := fun i hi => by
    rw [fr11 _ (sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  -- the saved registers
  have slotM : ∀ k, 0x40 ≤ k → k < 0x50 → m11.mem (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    have hT : Sep (F + 0xFFFFFFF0) 16 (G + BitVec.ofNat 32 k) 1 := by
      rw [eT]; exact offs (.inl (by omega)) (by decide) (by omega)
    have hU : Sep (F + 0xFFFFFFE0) 0x20 (G + BitVec.ofNat 32 k) 1 := by
      rw [eU]; exact offs (.inl (by omega)) (by decide) (by omega)
    have hF' : Sep F 32 (G + BitVec.ofNat 32 k) 1 := by
      rw [← eGF]; exact offs (.inl (by omega)) (by decide) (by omega)
    rw [f11 _ hT, copyBytes_sep (sOG.subR (c := k) (l := 1) (by omega)) (Nat.le_refl 32), f8 _ hU hF', f5 _ hT,
      copyBytes_sep hF' (Nat.le_refl 32)]
  have slotW : ∀ r o, (r, o) ∈ cs2Ps → memLoad32 m11.mem (F + o) = reg m r := fun r o h => by
    have ho : 0x20 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x30 := by
      simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, eFk, slotM _ (by omega) (by omega)]
  have hpsp : ∀ p ∈ cs2Ps, p.1 ≠ sp := by decide
  have u11 : St m11.mem P m11 (0x38 + 8) (reg m11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
  have sp11' : reg m11 sp = F := sp11
  obtain ⟨n1, e1, w1⟩ := St.block (restoreBlock cs2Ps) u11 hc11 cs2Restore_end
    (restoreBlock_ok m11.mem F cs2Ps (reg m11) sp11' hpsp fun q hq => by
      simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run m11.mem F cs2Ps (reg m11) sp11' hpsp] at w1
  have rsp1 : restoreRegs m11.mem F (reg m11) cs2Ps sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp11'
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs m11.mem F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ cs2Ps → restoreRegs m11.mem F (reg m11) cs2Ps r = reg m r := fun r o hm => by
    simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, e2, w2⟩ := w1.aluImm hc11 cs2_at_48 (off' := 0x4A) (by decide)
  obtain ⟨n3, e3, pc3, mem3, regs3⟩ := w2.jalr hc11 cs2_at_4a
  have k11' : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m11 q = reg m q := fun q hq => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, ht0, ht1, h7', h28, h29, h30, hs, hr, hv, h0, h8, h9, h18⟩ :
      q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧
      q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ sp ∧ q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧
      q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) := by revert hq; revert q; decide
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31] := by
      clear h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs hr hv h0 h8 h9 h18; revert hq; revert q; decide
    rw [k11 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs, r10 q hr, k9 q hv h0 h1 h2, k7_4 q hq' hr, r4 q hr,
      k3 q hv h0 h2 h8 h9 h18, r2 q hs]
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (e1.trans (.cons e2 (.single e3))))))))))))), ?_, ?_, fun i hi => ?_,
    fun q hq => ?_, fun x hx ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x2C (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
  · have eo : ∀ j, j < 4 → m11.mem (out + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j) =
        m8.mem (F + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j) := fun j hj => by
      have hs : Sep (F + 0xFFFFFFF0) 16 (out + BitVec.ofNat 32 (4 * i + j)) 1 := by
        rw [eT]; exact (sOG.symm.sub (c := 0x10) (l := 16) (by decide)).subR (c := 4 * i + j) (l := 1) (by omega)
      rw [add_ofNat_assoc, add_ofNat_assoc, f11 _ hs, cs_copy_in (by omega) (by decide)]
    rw [mem3, memLoad32_congr2 eo, v8 i hi]
    have eb : memLoad32 m5.mem (b + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (b + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact fr5 _ (sBG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    have ea : memLoad32 m5.mem (F + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (a + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr2 fun j hj => by
        rw [add_ofNat_assoc, add_ofNat_assoc,
          f5 _ (by rw [eT, ← eGF, add_ofNat_assoc]; exact offs (.inl (by omega)) (by decide) (by omega)),
          cs_copy_in (by omega) (by decide), frSv _ (sAG.sub (c := 4 * i + j) (l := 1) (by omega)).symm]
    rw [eb, ea]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        (q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ cs2Ps, p.1 ≠ q)) := by
      decide
    rcases key q hq with rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x2C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x28 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x24 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x20 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact k11' q h1
  · rw [mem3]; exact fr11 x hx ho

theorem uo_ext_zext (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have := b.isLt; omega

theorem uo_sel32 (S D c : Word) (hc : c = 0 ∨ c = 1) :
    aluEval .xor D (aluEval .and (aluEval .xor S D) (aluEval .sub 0 c)) = if c = 1 then S else D := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases hc with rfl | rfl
  · rw [ite_eq_right (by decide)]
    show (D ^^^ ((S ^^^ D) &&& (0 - 0))).getLsbD i = D.getLsbD i
    have h0 : (0 - 0 : Word).getLsbD i = false := BitVec.getLsbD_zero
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, h0, Bool.and_false, Bool.xor_false]
  · rw [ite_eq_left rfl]
    show (D ^^^ ((S ^^^ D) &&& (0 - 1))).getLsbD i = S.getLsbD i
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor, ones_bit ⟨i, hi⟩, Bool.and_true]
    generalize S.getLsbD i = x
    generalize D.getLsbD i = y
    cases x <;> cases y <;> rfl

theorem uo_sel (c : Word) (hc : c = 0 ∨ c = 1) (si di : BitVec 8) :
    (aluEval .xor (di.zeroExtend 32) (aluEval .and (aluEval .xor (si.zeroExtend 32) (di.zeroExtend 32))
      (aluEval .sub 0 c))).extractLsb' 0 8 = if c = 1 then si else di := by
  rw [uo_sel32 _ _ c hc]
  rcases hc with rfl | rfl
  · rw [ite_eq_right (by decide), ite_eq_right (by decide), uo_ext_zext]
  · rw [ite_eq_left rfl, ite_eq_left rfl, uo_ext_zext]

theorem uo_choice {b : BitVec 8} (h : b = 0 ∨ b = 1) :
    (b.zeroExtend 32 = 0 ∨ b.zeroExtend 32 = 1) ∧ (b.zeroExtend 32 = 1 ↔ b = 1) := by
  rcases h with rfl | rfl <;> decide

theorem uite_gen {cb : BitVec 8} (hcE : cb.zeroExtend 32 = 1 ↔ cb = 1) {α : Type} (X Y : α) :
    (if cb.zeroExtend 32 = 1 then X else Y) = (if cb = 1 then X else Y) := by
  by_cases h : cb = 1
  · rw [ite_eq_left (hcE.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hcE.mp h')), ite_eq_right h]

abbrev uoPs : List (Fin 32 × Word) :=
  [(ra, 0x1C), ((8 : Fin 32), 0x18), ((9 : Fin 32), 0x14), ((18 : Fin 32), 0x10), ((19 : Fin 32), 0xC)]

section
set_option maxRecDepth 20000
theorem uoSave_end : blockEnd unwrapOr384Code 2 (saveBlock uoPs) = some 0xC := by decide
theorem uoRestore_end : blockEnd unwrapOr384Code 0x50 (restoreBlock uoPs) = some 0x5A := by decide
end

/-- Where `CtOption<AffinePoint<NistP384>>::unwrap_or` runs: its code and its
callees', the 0x80 bytes of stack below `sp0`, the result `out`, the option
`s`, and the default `d`. -/
structure UOEnv (M : Word → BitVec 8) (P sp0 out s d : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P unwrapOr384Code
  cs : CodeIn M (P + 0x1070C) condSelect384Code
  stub : CodeIn M (P + 0x1070C + 0x101A) memcpyStubCode
  body : CodeIn M (P + 0x1070C + 0x101A + 8) memcpyBodyCode
  cta : CodeIn M (P + 0x1070C + 0x2EC) uint12CtAssignCode
  sca : CodeIn M (P + 0x1070C + 0x2EC + 0xFFFF9B66) sliceCtAssignCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x80 ≤ sp0.toNat
  hs : s.toNat % 4 = 0
  hsw : s.toNat + 0x65 < 2 ^ 32
  hdw : d.toNat + 0x61 < 2 ^ 32
  how : out.toNat + 0x61 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF80) 0x80 P unwrapOr384Code.length
  sGK : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0x1070C) condSelect384Code.length
  sGS : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0x1070C + 0x101A) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0x1070C + 0x101A + 8) memcpyBodyCode.length
  sGT : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0x1070C + 0x2EC) uint12CtAssignCode.length
  sGA : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0x1070C + 0x2EC + 0xFFFF9B66) sliceCtAssignCode.length
  sOC : Sep out 0x61 P unwrapOr384Code.length
  sOK : Sep out 0x61 (P + 0x1070C) condSelect384Code.length
  sOB : Sep out 0x61 (P + 0x1070C + 0x101A + 8) memcpyBodyCode.length
  sOU : Sep out 0x61 (P + 0x1070C + 0x101A) memcpyStubCode.length
  sOT : Sep out 0x61 (P + 0x1070C + 0x2EC) uint12CtAssignCode.length
  sOA : Sep out 0x61 (P + 0x1070C + 0x2EC + 0xFFFF9B66) sliceCtAssignCode.length
  sOG : Sep out 0x61 (sp0 + 0xFFFFFF80) 0x80
  sSG : Sep s 0x65 (sp0 + 0xFFFFFF80) 0x80
  sDG : Sep d 0x61 (sp0 + 0xFFFFFF80) 0x80
  sOS : Sep out 0x61 s 0x65
  sOD : Sep out 0x61 d 0x61

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `CtOption<AffinePoint<NistP384>>::unwrap_or`**: with the
option's choice byte at `s + 0x64`, it stores at `out` the point at `s` when
the choice is 1 and the point at `d` when it is 0: both 48-byte coordinates
and the identity byte at `0x60`. -/
theorem unwrapOr384_correct (m : Machine) {P sp0 out s d retAddr : Word} (env : UOEnv m.mem P sp0 out s d)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = s) (ha2 : reg m a2 = d)
    (hc : m.mem (s + 0x64) = 0 ∨ m.mem (s + 0x64) = 1)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 12 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if m.mem (s + 0x64) = 1 then memLoad32 m.mem (s + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem (d + BitVec.ofNat 32 (4 * i))) ∧
      (∀ i, i < 12 → memLoad32 m'.mem (out + 0x30 + BitVec.ofNat 32 (4 * i)) =
        if m.mem (s + 0x64) = 1 then memLoad32 m.mem (s + 0x30 + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem (d + 0x30 + BitVec.ofNat 32 (4 * i))) ∧
      m'.mem (out + 0x60) = (if m.mem (s + 0x64) = 1 then m.mem (s + 0x60) else m.mem (d + 0x60)) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF80) 0x80 y 1 → Sep out 0x61 y 1 → m'.mem y = m.mem y := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF80 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGK := env.sGK; have sGS := env.sGS; have sGB := env.sGB; have sGT := env.sGT
  have sGA := env.sGA; have sOG := env.sOG; have sSG := env.sSG; have sDG := env.sDG
  rw [hG] at sGC sGK sGS sGB sGT sGA sOG sSG sDG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF80) (by decide)
  have hGw : G.toNat + 0x80 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF80 : Word).toNat = 4294967168 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0x60 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0x60) (by decide)
  have hFn : F.toNat = G.toNat + 0x60 := by rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x60 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eK : F + 0xFFFFFFA0 = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0x80 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x80 → d + k ≤ 0x80 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x80 b code'.length → (∀ y, Sep G 0x80 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inK : ∀ {b : Word} {l : Nat}, Sep G 0x80 b l → Sep (F + 0xFFFFFFA0) 0x60 b l := fun h => by
    rw [eK]; exact h.sub (c := 0) (l := 0x60) (by decide)
  have inK' : ∀ {b : Word} {l : Nat}, Sep b l G 0x80 → Sep b l (F + 0xFFFFFFA0) 0x60 := fun h => by
    rw [eK]; exact h.subR (c := 0) (l := 0x60) (by decide)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod uo4_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have slotC : ∀ (o : Word), 0xC ≤ o.toNat → o.toNat + 4 ≤ 0x20 → ∀ {b : Word} {l : Nat}, Sep G 0x80 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x60 + o.toNat) (l := 4) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock uoPs) u1 env.cod uoSave_end (saveBlock_ok _ uoPs _ fun p hp => by
    rw [sp1]
    simp only [uoPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) uoPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep G 0x80 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside uoPs fun p hp => by
      simp only [uoPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) (by decide) hy
  have hslv : ∀ r o, (r, o) ∈ uoPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [uoPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hc2 : CodeIn Msv P unwrapOr384Code := cIn env.cod sGC frSv
  have rs : ∀ {a b : Word} {n k l : Nat}, Sep a n b k → l ≤ n → Sep a l b k := fun {a b n k l} h hl => by
    have := h.sub (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this
  have e30 : ∀ a : Word, a + 0x30 = a + BitVec.ofNat 32 0x30 := fun _ => rfl
  have e60 : ∀ a : Word, a + 0x60 = a + BitVec.ofNat 32 0x60 := fun _ => rfl
  have e64 : ∀ a : Word, a + 0x64 = a + BitVec.ofNat 32 0x64 := fun _ => rfl
  obtain ⟨cb, hcb⟩ : ∃ cb, m.mem (s + 0x64) = cb := ⟨_, rfl⟩
  rw [hcb] at hc ⊢
  have hcW := (uo_choice hc).1
  have hcE := (uo_choice hc).2
  have uite : ∀ {α : Type} (X Y : α), (if cb.zeroExtend 32 = 1 then X else Y) = (if cb = 1 then X else Y) :=
    fun X Y => by
      by_cases h : cb = 1
      · rw [ite_eq_left (hcE.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun h' => h (hcE.mp h')), ite_eq_right h]
  -- the first coordinate
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (18 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1,
    .lbu (8 : Fin 32) a1 0x64, .alu .add (19 : Fin 32) x0 a0, .alu .add a1 x0 a2, .alu .add a2 x0 (9 : Fin 32),
    .alu .add a3 x0 (8 : Fin 32)] u2.self hc2 (off' := 0x1C) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have z2 := u2.self.zero
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
      q ≠ (19 : Fin 32) → reg m3 q = reg m2 q := fun q hv h1 h2 h3 h8 h9 h18 h19 => by
    rw [u3.regs, upd_ne hv h3, upd_ne hv h2, upd_ne hv h1, upd_ne hv h19, upd_ne hv h8, upd_ne hv h9, upd_ne hv h18]
  have cv : (Msv (s + 0x64)).zeroExtend 32 = cb.zeroExtend 32 := by
    rw [frSv _ (by rw [e64]; exact (env.sSG.sub (c := 0x64) (l := 1) (by decide)).symm |> fun h => by rwa [hG] at h),
      hcb]
  have v3 : reg m3 8 = cb.zeroExtend 32 ∧ reg m3 9 = s ∧ reg m3 18 = d ∧ reg m3 19 = out ∧ reg m3 a1 = d ∧
      reg m3 a2 = s ∧ reg m3 a3 = cb.zeroExtend 32 ∧ reg m3 a0 = out ∧ reg m3 sp = F := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [u3.regs] <;> simp +decide only [upd_app, ↓reduceIte]
    all_goals first
      | (rw [r2 a1 (by decide), ha1]; exact cv)
      | (rw [r2 a1 (by decide), ha1]; exact zw s)
      | (rw [r2 a2 (by decide), ha2]; exact zw d)
      | (rw [r2 a0 (by decide), ha0]; exact zw out)
      | (rw [r2 a2 (by decide), ha2]; exact zw d)
      | (rw [r2 a1 (by decide), ha1]; exact zw s)
      | (rw [r2 a0 (by decide), ha0])
      | exact sp2
      | (rw [r2 a1 (by decide), ha1, ev_add, ev_add, zw, zw])
      | (rw [r2 a1 (by decide), ha1, ev_add, zw, cv])
  obtain ⟨v38, v39, v318, v319, v3a1, v3a2, v3a3, v3a0, v3sp⟩ := v3
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hc2 uo4_at_1c uo4_at_20 (cb := P + 0x1070C)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x1070C (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have env1 : CSEnv m4.mem (P + 0x1070C) F out d s := by
    rw [mem4]
    exact ⟨even_at P env.hP 0x1070C (by decide), cIn env.cs sGK frSv, cIn env.stub sGS frSv, cIn env.body sGB frSv,
      cIn env.cta sGT frSv, cIn env.sca sGA frSv, hFa, by omega, env.hs, by have := env.hdw; omega,
      by have := env.how; omega, inK sGK, inK sGS, inK sGB, inK sGT, inK sGA, rs env.sOK (by decide),
      rs env.sOB (by decide), inK' (rs sOG (by decide)), inK' (rs sDG (by decide)), inK' (rs sSG (by decide))⟩
  obtain ⟨m5, c5, pc5, sp5, w5, k5, f5⟩ := condSelect384_correct m4 env1 pc4 (by rw [r4 sp (by decide), v3sp])
    (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by rw [r4 a2 (by decide), v3a2])
    (by rw [r4 a3 (by decide), v3a3]) hcW (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x1C + 8) (by decide)))
  rw [mem4] at w5 f5
  have fr5 : ∀ y, Sep G 0x80 y 1 → Sep out 48 y 1 → m5.mem y = m.mem y := fun y hy ho => by
    rw [f5 y (inK hy) ho, frSv y hy]
  have hc5 : CodeIn m5.mem P unwrapOr384Code := fun k hk => by
    rw [fr5 _ (sGC.subR (c := k) (l := 1) (by omega)) ((rs env.sOC (by decide)).subR (c := k) (l := 1) (by omega))]
    exact env.cod k hk
  have u5 : St m5.mem P m5 (0x1C + 8) (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have kk : ∀ q, q.val ∈ [8, 9, 18, 19] → reg m5 q = reg m3 q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    have hr : q ≠ ra := by revert hq; revert q; decide
    rw [k5 q hq', r4 q hr]
  -- the second coordinate
  obtain ⟨m6, c6, u6⟩ := St.block [.aluImm .add a1 (18 : Fin 32) 0x30, .aluImm .add a2 (9 : Fin 32) 0x30,
    .aluImm .add a0 (19 : Fin 32) 0x30, .alu .add a3 x0 (8 : Fin 32)] u5 hc5 (off' := 0x32) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u6
  have k6 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg m6 q = reg m5 q := fun q hv h0 h1 h2 h3 => by
    rw [u6.regs, upd_ne hv h3, upd_ne hv h0, upd_ne hv h2, upd_ne hv h1]
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6.self.callRa hc5 uo4_at_32 uo4_at_36 (cb := P + 0x1070C)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x1070C (by decide))
  have r7 := PEnv.reg1 regs7 u6.self.zero
  have fr5c : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x80 b code'.length →
      Sep out 0x61 b code'.length → CodeIn m5.mem b code' := fun hc hs ho i hi => by
    rw [fr5 _ (hs.subR (c := i) (l := 1) (by omega)) ((rs ho (by decide)).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have env2 : CSEnv m7.mem (P + 0x1070C) F (out + 0x30) (d + 0x30) (s + 0x30) := by
    rw [mem7]
    exact ⟨even_at P env.hP 0x1070C (by decide), fr5c env.cs sGK env.sOK, fr5c env.stub sGS env.sOU,
      fr5c env.body sGB env.sOB, fr5c env.cta sGT env.sOT, fr5c env.sca sGA env.sOA, hFa, by omega,
      aligned_add env.hs (by decide),
      by rw [e30, BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.hdw; omega,
      by rw [e30, BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.how; omega,
      inK sGK, inK sGS, inK sGB, inK sGT, inK sGA, env.sOK.sub (c := 0x30) (l := 48) (by decide),
      env.sOB.sub (c := 0x30) (l := 48) (by decide), inK' (sOG.sub (c := 0x30) (l := 48) (by decide)),
      inK' (sDG.sub (c := 0x30) (l := 48) (by decide)), inK' (sSG.sub (c := 0x30) (l := 48) (by decide))⟩
  obtain ⟨m8, c8, pc8, sp8, w8, k8, f8⟩ := condSelect384_correct m7 env2 pc7
    (by rw [r7 sp (by decide), k6 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp5])
    (by rw [r7 a0 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kk 19 (by decide), v319, ev_add])
    (by rw [r7 a1 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kk 18 (by decide), v318, ev_add])
    (by rw [r7 a2 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kk 9 (by decide), v39, ev_add])
    (by rw [r7 a3 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kk 8 (by decide), v38, ev_add]; exact zw _) hcW
    (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x32 + 8) (by decide)))
  rw [mem7] at w8 f8
  have kk8 : ∀ q, q.val ∈ [8, 9, 18, 19] → reg m8 q = reg m3 q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    obtain ⟨hr, hv, h0, h1, h2, h3⟩ : q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 := by
      clear hq'; revert hq; revert q; decide
    rw [k8 q hq', r7 q hr, k6 q hv h0 h1 h2 h3, kk q hq]
  have fr8 : ∀ y, Sep G 0x80 y 1 → Sep out 0x61 y 1 → m8.mem y = m.mem y := fun y hy ho => by
    rw [f8 y (inK hy) (ho.sub (c := 0x30) (l := 48) (by decide)), fr5 y hy (rs ho (by decide))]
  have hc8 : CodeIn m8.mem P unwrapOr384Code := fun k hk => by
    rw [fr8 _ (sGC.subR (c := k) (l := 1) (by omega)) (env.sOC.subR (c := k) (l := 1) (by omega))]
    exact env.cod k hk
  have u8 : St m8.mem P m8 (0x32 + 8) (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  -- the identity byte
  obtain ⟨m9, c9, u9⟩ := St.block [.lbu a0 (18 : Fin 32) 0x60, .lbu a1 (9 : Fin 32) 0x60, .alu .sub a2 x0 (8 : Fin 32),
    .alu .xor a1 a1 a0, .alu .and a1 a1 a2, .alu .xor a0 a0 a1] u8 hc8 (off' := 0x4C) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u9
  have dv : m8.mem (d + 0x60) = m.mem (d + 0x60) :=
    fr8 _ (by rw [e60]; exact (sDG.sub (c := 0x60) (l := 1) (by decide)).symm)
      (by rw [e60]; exact env.sOD.subR (c := 0x60) (l := 1) (by decide))
  have sv : m8.mem (s + 0x60) = m.mem (s + 0x60) :=
    fr8 _ (by rw [e60]; exact (sSG.sub (c := 0x60) (l := 1) (by decide)).symm)
      (by rw [e60]; exact env.sOS.subR (c := 0x60) (l := 1) (by decide))
  have a09 : reg m9 a0 = aluEval .xor ((m.mem (d + 0x60)).zeroExtend 32)
      (aluEval .and (aluEval .xor ((m.mem (s + 0x60)).zeroExtend 32) ((m.mem (d + 0x60)).zeroExtend 32))
        (aluEval .sub 0 (cb.zeroExtend 32))) := by
    rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [kk8 18 (by decide), v318, kk8 9 (by decide), v39, kk8 8 (by decide), v38, dv, sv]
  have k9 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m9 q = reg m8 q := fun q hv h0 h1 h2 => by
    rw [u9.regs, upd_ne hv h0, upd_ne hv h1, upd_ne hv h1, upd_ne hv h2, upd_ne hv h1, upd_ne hv h0]
  have r9_19 : reg m9 19 = out := by
    rw [k9 19 (by decide) (by decide) (by decide) (by decide), kk8 19 (by decide), v319]
  obtain ⟨m10, d10, u10⟩ := u9.self.sb hc8 uo4_at_4c (off' := 0x50) (by decide)
  rw [r9_19, a09, uo_sel _ hcW, uite] at u10
  obtain ⟨M10, hM10⟩ : ∃ M10, memStore8 m8.mem (out + 0x60)
      (if cb = 1 then m.mem (s + 0x60) else m.mem (d + 0x60)) = M10 := ⟨_, rfl⟩
  rw [hM10] at u10
  have hc10 : CodeIn M10 P unwrapOr384Code := by
    rw [← hM10]; exact hc8.store8 (env.sOC.sub (c := 0x60) (l := 1) (by decide))
  have slotM : ∀ k, 0x6C ≤ k → k < 0x80 → M10 (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    have hK : Sep (F + 0xFFFFFFA0) 0x60 (G + BitVec.ofNat 32 k) 1 := by
      rw [eK]; exact offs (.inl (by omega)) (by decide) (by omega)
    rw [← hM10, memStore8_ne (a := out + 0x60) (fun e => sOG 0x60 (by decide) k (by omega) e.symm),
      f8 _ hK ((sOG.sub (c := 0x30) (l := 48) (by decide)).subR (c := k) (l := 1) (by omega)),
      f5 _ hK ((rs sOG (by decide)).subR (c := k) (l := 1) (by omega))]
  have slotW : ∀ r o, (r, o) ∈ uoPs → memLoad32 M10 (F + o) = reg m r := fun r o h => by
    have ho : 0xC ≤ o.toNat ∧ o.toNat + 4 ≤ 0x20 := by
      simp only [uoPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, eFk, slotM _ (by omega) (by omega)]
  have sp9 : reg m9 sp = F := by
    rw [k9 sp (by decide) (by decide) (by decide) (by decide), sp8]
  have hpsp : ∀ p ∈ uoPs, p.1 ≠ sp := by decide
  obtain ⟨n1, e1, w1⟩ := St.block (restoreBlock uoPs) u10 hc10 uoRestore_end
    (restoreBlock_ok M10 F uoPs (reg m9) sp9 hpsp fun q hq => by
      simp only [uoPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run M10 F uoPs (reg m9) sp9 hpsp] at w1
  have rsp1 : restoreRegs M10 F (reg m9) uoPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp9
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M10 F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ uoPs → restoreRegs M10 F (reg m9) uoPs r = reg m r := fun r o hm => by
    simp only [uoPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, e2, w2⟩ := w1.aluImm hc10 uo4_at_5a (off' := 0x5C) (by decide)
  obtain ⟨n3, e3, pc3, mem3, regs3⟩ := w2.jalr hc10 uo4_at_5c
  have kfin : ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg m9 q = reg m q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    obtain ⟨hv, h0, h1, h2, h3, h8, h9, h18, h19, hs, hr⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧
        q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧ q ≠ sp ∧ q ≠ ra := by
      clear hq'; revert hq; revert q; decide
    rw [k9 q hv h0 h1 h2, k8 q hq', r7 q hr, k6 q hv h0 h1 h2 h3, k5 q hq', r4 q hr, k3 q hv h1 h2 h3 h8 h9 h18 h19,
      r2 q hs]
  have neq : ∀ k, k < 0x60 → out + BitVec.ofNat 32 k ≠ out + 0x60 := fun k hk =>
    add_ofNat_ne out (c := k) (d := 0x60) (by omega) (by decide) (by omega)
  have outG : ∀ k, k < 0x61 → Sep (F + 0xFFFFFFA0) 0x60 (out + BitVec.ofNat 32 k) 1 := fun k hk =>
    inK (sOG.symm.subR (c := k) (l := 1) (by omega))
  have ow : out.toNat + 0x61 ≤ 2 ^ 32 := by have := env.how; omega
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (.cons d10 (e1.trans (.cons e2 (.single e3)))))))))))), ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_,
    fun q hq => ?_, fun y hy ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x1C (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
  · have e : memLoad32 M10 (out + BitVec.ofNat 32 (4 * i)) = memLoad32 m5.mem (out + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, ← hM10, memStore8_ne (a := out + 0x60) (neq _ (by omega)),
          f8 _ (outG _ (by omega)) (sep_offsets out (c := 0x30) (n := 48) (d := 4 * i + j) (k := 1)
            (.inr (by omega)) (by omega) (by omega))]
    have es : memLoad32 Msv (s + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (s + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frSv _ (sSG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    have ed : memLoad32 Msv (d + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (d + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frSv _ (sDG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    rw [mem3, e, w5 i hi, uite, es, ed]
  · have e : memLoad32 M10 (out + 0x30 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m8.mem (out + 0x30 + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [e30, add_ofNat_assoc, add_ofNat_assoc, ← hM10, memStore8_ne (a := out + 0x60) (neq _ (by omega))]
    have es : memLoad32 m5.mem (s + 0x30 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (s + 0x30 + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [e30, add_ofNat_assoc, add_ofNat_assoc]
        exact fr5 _ (sSG.sub (c := 0x30 + (4 * i + j)) (l := 1) (by omega)).symm
          ((rs env.sOS (by decide)).subR (c := 0x30 + (4 * i + j)) (l := 1) (by omega))
    have ed : memLoad32 m5.mem (d + 0x30 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (d + 0x30 + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [e30, add_ofNat_assoc, add_ofNat_assoc]
        exact fr5 _ (sDG.sub (c := 0x30 + (4 * i + j)) (l := 1) (by omega)).symm
          ((rs env.sOD (by decide)).subR (c := 0x30 + (4 * i + j)) (l := 1) (by omega))
    rw [mem3, e, w8 i hi, uite, es, ed]
  · rw [mem3, ← hM10, memStore8_same]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        (q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ uoPs, p.1 ≠ q)) := by
      decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x1C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x18 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x14 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x10 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xC (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kfin q h1
  · have hne : y ≠ out + 0x60 := fun e => ho 0x60 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)
    rw [mem3, ← hM10, memStore8_ne hne, fr8 y hy ho]

abbrev uo2Ps : List (Fin 32 × Word) :=
  [(ra, 0x1C), ((8 : Fin 32), 0x18), ((9 : Fin 32), 0x14), ((18 : Fin 32), 0x10), ((19 : Fin 32), 0xC)]

section
set_option maxRecDepth 20000
theorem uo2Save_end : blockEnd unwrapOr256Code 2 (saveBlock uo2Ps) = some 0xC := by decide
theorem uo2Restore_end : blockEnd unwrapOr256Code 0x50 (restoreBlock uo2Ps) = some 0x5A := by decide
end

/-- Where `CtOption<AffinePoint<NistP256>>::unwrap_or` runs: its code and its
callees', the 0x70 bytes of stack below `sp0`, the result `out`, the option
`s`, and the default `d`. -/
structure UO2Env (M : Word → BitVec 8) (P sp0 out s d : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P unwrapOr256Code
  cs : CodeIn M (P + 0xE460) condSelect256Code
  stub : CodeIn M (P + 0xE460 + 0x323E) memcpyStubCode
  body : CodeIn M (P + 0xE460 + 0x323E + 8) memcpyBodyCode
  sca : CodeIn M (P + 0xE460 + 0xFFFFC076) sliceCtAssignCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x70 ≤ sp0.toNat
  hs : s.toNat % 4 = 0
  hsw : s.toNat + 0x45 < 2 ^ 32
  hdw : d.toNat + 0x41 < 2 ^ 32
  how : out.toNat + 0x41 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF90) 0x70 P unwrapOr256Code.length
  sGK : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xE460) condSelect256Code.length
  sGS : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xE460 + 0x323E) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xE460 + 0x323E + 8) memcpyBodyCode.length
  sGA : Sep (sp0 + 0xFFFFFF90) 0x70 (P + 0xE460 + 0xFFFFC076) sliceCtAssignCode.length
  sOC : Sep out 0x41 P unwrapOr256Code.length
  sOK : Sep out 0x41 (P + 0xE460) condSelect256Code.length
  sOB : Sep out 0x41 (P + 0xE460 + 0x323E + 8) memcpyBodyCode.length
  sOU : Sep out 0x41 (P + 0xE460 + 0x323E) memcpyStubCode.length
  sOA : Sep out 0x41 (P + 0xE460 + 0xFFFFC076) sliceCtAssignCode.length
  sOG : Sep out 0x41 (sp0 + 0xFFFFFF90) 0x70
  sSG : Sep s 0x45 (sp0 + 0xFFFFFF90) 0x70
  sDG : Sep d 0x41 (sp0 + 0xFFFFFF90) 0x70
  sOS : Sep out 0x41 s 0x45
  sOD : Sep out 0x41 d 0x41

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `CtOption<AffinePoint<NistP256>>::unwrap_or`**: with the
option's choice byte at `s + 0x44`, it stores at `out` the point at `s` when
the choice is 1 and the point at `d` when it is 0: both 32-byte coordinates
and the identity byte at `0x40`. -/
theorem unwrapOr256_correct (m : Machine) {P sp0 out s d retAddr : Word} (env : UO2Env m.mem P sp0 out s d)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = s) (ha2 : reg m a2 = d)
    (hc : m.mem (s + 0x44) = 0 ∨ m.mem (s + 0x44) = 1)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 8 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if m.mem (s + 0x44) = 1 then memLoad32 m.mem (s + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem (d + BitVec.ofNat 32 (4 * i))) ∧
      (∀ i, i < 8 → memLoad32 m'.mem (out + 0x20 + BitVec.ofNat 32 (4 * i)) =
        if m.mem (s + 0x44) = 1 then memLoad32 m.mem (s + 0x20 + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem (d + 0x20 + BitVec.ofNat 32 (4 * i))) ∧
      m'.mem (out + 0x40) = (if m.mem (s + 0x44) = 1 then m.mem (s + 0x40) else m.mem (d + 0x40)) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF90) 0x70 y 1 → Sep out 0x41 y 1 → m'.mem y = m.mem y := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF90 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGK := env.sGK; have sGS := env.sGS; have sGB := env.sGB
  have sGA := env.sGA; have sOG := env.sOG; have sSG := env.sSG; have sDG := env.sDG
  rw [hG] at sGC sGK sGS sGB sGA sOG sSG sDG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF90) (by decide)
  have hGw : G.toNat + 0x70 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF90 : Word).toNat = 4294967184 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0x50 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0x50) (by decide)
  have hFn : F.toNat = G.toNat + 0x50 := by rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x50 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eK : F + 0xFFFFFFB0 = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0x70 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x70 → d + k ≤ 0x70 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x70 b code'.length → (∀ y, Sep G 0x70 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inK : ∀ {b : Word} {l : Nat}, Sep G 0x70 b l → Sep (F + 0xFFFFFFB0) 0x50 b l := fun h => by
    rw [eK]; exact h.sub (c := 0) (l := 0x50) (by decide)
  have inK' : ∀ {b : Word} {l : Nat}, Sep b l G 0x70 → Sep b l (F + 0xFFFFFFB0) 0x50 := fun h => by
    rw [eK]; exact h.subR (c := 0) (l := 0x50) (by decide)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod uo2_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have slotC : ∀ (o : Word), 0xC ≤ o.toNat → o.toNat + 4 ≤ 0x20 → ∀ {b : Word} {l : Nat}, Sep G 0x70 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x50 + o.toNat) (l := 4) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock uo2Ps) u1 env.cod uo2Save_end (saveBlock_ok _ uo2Ps _ fun p hp => by
    rw [sp1]
    simp only [uo2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) uo2Ps = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep G 0x70 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside uo2Ps fun p hp => by
      simp only [uo2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) (by decide) hy
  have hslv : ∀ r o, (r, o) ∈ uo2Ps → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [uo2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hc2 : CodeIn Msv P unwrapOr256Code := cIn env.cod sGC frSv
  have rs : ∀ {a b : Word} {n k l : Nat}, Sep a n b k → l ≤ n → Sep a l b k := fun {a b n k l} h hl => by
    have := h.sub (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this
  have e20 : ∀ a : Word, a + 0x20 = a + BitVec.ofNat 32 0x20 := fun _ => rfl
  have e40 : ∀ a : Word, a + 0x40 = a + BitVec.ofNat 32 0x40 := fun _ => rfl
  have e44 : ∀ a : Word, a + 0x44 = a + BitVec.ofNat 32 0x44 := fun _ => rfl
  obtain ⟨cb, hcb⟩ : ∃ cb, m.mem (s + 0x44) = cb := ⟨_, rfl⟩
  rw [hcb] at hc ⊢
  have hcW := (uo_choice hc).1
  have hcE := (uo_choice hc).2
  have uite : ∀ {α : Type} (X Y : α), (if cb.zeroExtend 32 = 1 then X else Y) = (if cb = 1 then X else Y) :=
    fun X Y => by
      by_cases h : cb = 1
      · rw [ite_eq_left (hcE.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun h' => h (hcE.mp h')), ite_eq_right h]
  -- the first coordinate
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (18 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1,
    .lbu (8 : Fin 32) a1 0x44, .alu .add (19 : Fin 32) x0 a0, .alu .add a1 x0 a2, .alu .add a2 x0 (9 : Fin 32),
    .alu .add a3 x0 (8 : Fin 32)] u2.self hc2 (off' := 0x1C) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have z2 := u2.self.zero
  have k3 : ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
      q ≠ (19 : Fin 32) → reg m3 q = reg m2 q := fun q hv h1 h2 h3 h8 h9 h18 h19 => by
    rw [u3.regs, upd_ne hv h3, upd_ne hv h2, upd_ne hv h1, upd_ne hv h19, upd_ne hv h8, upd_ne hv h9, upd_ne hv h18]
  have cv : (Msv (s + 0x44)).zeroExtend 32 = cb.zeroExtend 32 := by
    rw [frSv _ (by rw [e44]; exact (env.sSG.sub (c := 0x44) (l := 1) (by decide)).symm |> fun h => by rwa [hG] at h),
      hcb]
  have v3 : reg m3 8 = cb.zeroExtend 32 ∧ reg m3 9 = s ∧ reg m3 18 = d ∧ reg m3 19 = out ∧ reg m3 a1 = d ∧
      reg m3 a2 = s ∧ reg m3 a3 = cb.zeroExtend 32 ∧ reg m3 a0 = out ∧ reg m3 sp = F := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [u3.regs] <;> simp +decide only [upd_app, ↓reduceIte]
    all_goals first
      | (rw [r2 a1 (by decide), ha1]; exact cv)
      | (rw [r2 a1 (by decide), ha1]; exact zw s)
      | (rw [r2 a2 (by decide), ha2]; exact zw d)
      | (rw [r2 a0 (by decide), ha0]; exact zw out)
      | (rw [r2 a2 (by decide), ha2]; exact zw d)
      | (rw [r2 a1 (by decide), ha1]; exact zw s)
      | (rw [r2 a0 (by decide), ha0])
      | exact sp2
      | (rw [r2 a1 (by decide), ha1, ev_add, ev_add, zw, zw])
      | (rw [r2 a1 (by decide), ha1, ev_add, zw, cv])
  obtain ⟨v38, v39, v318, v319, v3a1, v3a2, v3a3, v3a0, v3sp⟩ := v3
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hc2 uo2_at_1c uo2_at_20 (cb := P + 0xE460)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xE460 (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have env1 : CS2Env m4.mem (P + 0xE460) F out d s := by
    rw [mem4]
    exact ⟨even_at P env.hP 0xE460 (by decide), cIn env.cs sGK frSv, cIn env.stub sGS frSv, cIn env.body sGB frSv,
      cIn env.sca sGA frSv, hFa, by omega, env.hs, by have := env.hdw; omega,
      by have := env.how; omega, inK sGK, inK sGS, inK sGB, inK sGA, rs env.sOK (by decide),
      rs env.sOB (by decide), inK' (rs sOG (by decide)), inK' (rs sDG (by decide)), inK' (rs sSG (by decide))⟩
  obtain ⟨m5, c5, pc5, sp5, w5, k5, f5⟩ := condSelect256_correct m4 env1 pc4 (by rw [r4 sp (by decide), v3sp])
    (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by rw [r4 a2 (by decide), v3a2])
    (by rw [r4 a3 (by decide), v3a3]) hcW (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x1C + 8) (by decide)))
  rw [mem4] at w5 f5
  have fr5 : ∀ y, Sep G 0x70 y 1 → Sep out 32 y 1 → m5.mem y = m.mem y := fun y hy ho => by
    rw [f5 y (inK hy) ho, frSv y hy]
  have hc5 : CodeIn m5.mem P unwrapOr256Code := fun k hk => by
    rw [fr5 _ (sGC.subR (c := k) (l := 1) (by omega)) ((rs env.sOC (by decide)).subR (c := k) (l := 1) (by omega))]
    exact env.cod k hk
  have u5 : St m5.mem P m5 (0x1C + 8) (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have kk : ∀ q, q.val ∈ [8, 9, 18, 19] → reg m5 q = reg m3 q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    have hr : q ≠ ra := by revert hq; revert q; decide
    rw [k5 q hq', r4 q hr]
  -- the second coordinate
  obtain ⟨m6, c6, u6⟩ := St.block [.aluImm .add a1 (18 : Fin 32) 0x20, .aluImm .add a2 (9 : Fin 32) 0x20,
    .aluImm .add a0 (19 : Fin 32) 0x20, .alu .add a3 x0 (8 : Fin 32)] u5 hc5 (off' := 0x32) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u6
  have k6 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg m6 q = reg m5 q := fun q hv h0 h1 h2 h3 => by
    rw [u6.regs, upd_ne hv h3, upd_ne hv h0, upd_ne hv h2, upd_ne hv h1]
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6.self.callRa hc5 uo2_at_32 uo2_at_36 (cb := P + 0xE460)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xE460 (by decide))
  have r7 := PEnv.reg1 regs7 u6.self.zero
  have fr5c : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x70 b code'.length →
      Sep out 0x41 b code'.length → CodeIn m5.mem b code' := fun hc hs ho i hi => by
    rw [fr5 _ (hs.subR (c := i) (l := 1) (by omega)) ((rs ho (by decide)).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have env2 : CS2Env m7.mem (P + 0xE460) F (out + 0x20) (d + 0x20) (s + 0x20) := by
    rw [mem7]
    exact ⟨even_at P env.hP 0xE460 (by decide), fr5c env.cs sGK env.sOK, fr5c env.stub sGS env.sOU,
      fr5c env.body sGB env.sOB, fr5c env.sca sGA env.sOA, hFa, by omega,
      aligned_add env.hs (by decide),
      by rw [e20, BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.hdw; omega,
      by rw [e20, BitVec.toNat_add, BitVec.toNat_ofNat]; have := env.how; omega,
      inK sGK, inK sGS, inK sGB, inK sGA, env.sOK.sub (c := 0x20) (l := 32) (by decide),
      env.sOB.sub (c := 0x20) (l := 32) (by decide), inK' (sOG.sub (c := 0x20) (l := 32) (by decide)),
      inK' (sDG.sub (c := 0x20) (l := 32) (by decide)), inK' (sSG.sub (c := 0x20) (l := 32) (by decide))⟩
  obtain ⟨m8, c8, pc8, sp8, w8, k8, f8⟩ := condSelect256_correct m7 env2 pc7
    (by rw [r7 sp (by decide), k6 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp5])
    (by rw [r7 a0 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kk 19 (by decide), v319, ev_add])
    (by rw [r7 a1 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kk 18 (by decide), v318, ev_add])
    (by rw [r7 a2 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kk 9 (by decide), v39, ev_add])
    (by rw [r7 a3 (by decide), u6.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kk 8 (by decide), v38, ev_add]; exact zw _) hcW
    (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x32 + 8) (by decide)))
  rw [mem7] at w8 f8
  have kk8 : ∀ q, q.val ∈ [8, 9, 18, 19] → reg m8 q = reg m3 q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    obtain ⟨hr, hv, h0, h1, h2, h3⟩ : q ≠ ra ∧ q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 := by
      clear hq'; revert hq; revert q; decide
    rw [k8 q hq', r7 q hr, k6 q hv h0 h1 h2 h3, kk q hq]
  have fr8 : ∀ y, Sep G 0x70 y 1 → Sep out 0x41 y 1 → m8.mem y = m.mem y := fun y hy ho => by
    rw [f8 y (inK hy) (ho.sub (c := 0x20) (l := 32) (by decide)), fr5 y hy (rs ho (by decide))]
  have hc8 : CodeIn m8.mem P unwrapOr256Code := fun k hk => by
    rw [fr8 _ (sGC.subR (c := k) (l := 1) (by omega)) (env.sOC.subR (c := k) (l := 1) (by omega))]
    exact env.cod k hk
  have u8 : St m8.mem P m8 (0x32 + 8) (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  -- the identity byte
  obtain ⟨m9, c9, u9⟩ := St.block [.lbu a0 (18 : Fin 32) 0x40, .lbu a1 (9 : Fin 32) 0x40, .alu .sub a2 x0 (8 : Fin 32),
    .alu .xor a1 a1 a0, .alu .and a1 a1 a2, .alu .xor a0 a0 a1] u8 hc8 (off' := 0x4C) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u9
  have dv : m8.mem (d + 0x40) = m.mem (d + 0x40) :=
    fr8 _ (by rw [e40]; exact (sDG.sub (c := 0x40) (l := 1) (by decide)).symm)
      (by rw [e40]; exact env.sOD.subR (c := 0x40) (l := 1) (by decide))
  have sv : m8.mem (s + 0x40) = m.mem (s + 0x40) :=
    fr8 _ (by rw [e40]; exact (sSG.sub (c := 0x40) (l := 1) (by decide)).symm)
      (by rw [e40]; exact env.sOS.subR (c := 0x40) (l := 1) (by decide))
  have a09 : reg m9 a0 = aluEval .xor ((m.mem (d + 0x40)).zeroExtend 32)
      (aluEval .and (aluEval .xor ((m.mem (s + 0x40)).zeroExtend 32) ((m.mem (d + 0x40)).zeroExtend 32))
        (aluEval .sub 0 (cb.zeroExtend 32))) := by
    rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [kk8 18 (by decide), v318, kk8 9 (by decide), v39, kk8 8 (by decide), v38, dv, sv]
  have k9 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m9 q = reg m8 q := fun q hv h0 h1 h2 => by
    rw [u9.regs, upd_ne hv h0, upd_ne hv h1, upd_ne hv h1, upd_ne hv h2, upd_ne hv h1, upd_ne hv h0]
  have r9_19 : reg m9 19 = out := by
    rw [k9 19 (by decide) (by decide) (by decide) (by decide), kk8 19 (by decide), v319]
  obtain ⟨m10, d10, u10⟩ := u9.self.sb hc8 uo2_at_4c (off' := 0x50) (by decide)
  rw [r9_19, a09, uo_sel _ hcW, uite] at u10
  obtain ⟨M10, hM10⟩ : ∃ M10, memStore8 m8.mem (out + 0x40)
      (if cb = 1 then m.mem (s + 0x40) else m.mem (d + 0x40)) = M10 := ⟨_, rfl⟩
  rw [hM10] at u10
  have hc10 : CodeIn M10 P unwrapOr256Code := by
    rw [← hM10]; exact hc8.store8 (env.sOC.sub (c := 0x40) (l := 1) (by decide))
  have slotM : ∀ k, 0x5C ≤ k → k < 0x70 → M10 (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    have hK : Sep (F + 0xFFFFFFB0) 0x50 (G + BitVec.ofNat 32 k) 1 := by
      rw [eK]; exact offs (.inl (by omega)) (by decide) (by omega)
    rw [← hM10, memStore8_ne (a := out + 0x40) (fun e => sOG 0x40 (by decide) k (by omega) e.symm),
      f8 _ hK ((sOG.sub (c := 0x20) (l := 32) (by decide)).subR (c := k) (l := 1) (by omega)),
      f5 _ hK ((rs sOG (by decide)).subR (c := k) (l := 1) (by omega))]
  have slotW : ∀ r o, (r, o) ∈ uo2Ps → memLoad32 M10 (F + o) = reg m r := fun r o h => by
    have ho : 0xC ≤ o.toNat ∧ o.toNat + 4 ≤ 0x20 := by
      simp only [uo2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, eFk, slotM _ (by omega) (by omega)]
  have sp9 : reg m9 sp = F := by
    rw [k9 sp (by decide) (by decide) (by decide) (by decide), sp8]
  have hpsp : ∀ p ∈ uo2Ps, p.1 ≠ sp := by decide
  obtain ⟨n1, e1, w1⟩ := St.block (restoreBlock uo2Ps) u10 hc10 uo2Restore_end
    (restoreBlock_ok M10 F uo2Ps (reg m9) sp9 hpsp fun q hq => by
      simp only [uo2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run M10 F uo2Ps (reg m9) sp9 hpsp] at w1
  have rsp1 : restoreRegs M10 F (reg m9) uo2Ps sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp9
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M10 F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ uo2Ps → restoreRegs M10 F (reg m9) uo2Ps r = reg m r := fun r o hm => by
    simp only [uo2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, e2, w2⟩ := w1.aluImm hc10 uo2_at_5a (off' := 0x5C) (by decide)
  obtain ⟨n3, e3, pc3, mem3, regs3⟩ := w2.jalr hc10 uo2_at_5c
  have kfin : ∀ q, q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] → reg m9 q = reg m q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    obtain ⟨hv, h0, h1, h2, h3, h8, h9, h18, h19, hs, hr⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧
        q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧ q ≠ sp ∧ q ≠ ra := by
      clear hq'; revert hq; revert q; decide
    rw [k9 q hv h0 h1 h2, k8 q hq', r7 q hr, k6 q hv h0 h1 h2 h3, k5 q hq', r4 q hr, k3 q hv h1 h2 h3 h8 h9 h18 h19,
      r2 q hs]
  have neq : ∀ k, k < 0x40 → out + BitVec.ofNat 32 k ≠ out + 0x40 := fun k hk =>
    add_ofNat_ne out (c := k) (d := 0x40) (by omega) (by decide) (by omega)
  have outG : ∀ k, k < 0x41 → Sep (F + 0xFFFFFFB0) 0x50 (out + BitVec.ofNat 32 k) 1 := fun k hk =>
    inK (sOG.symm.subR (c := k) (l := 1) (by omega))
  have ow : out.toNat + 0x41 ≤ 2 ^ 32 := by have := env.how; omega
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (.cons d10 (e1.trans (.cons e2 (.single e3)))))))))))), ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_,
    fun q hq => ?_, fun y hy ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x1C (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
  · have e : memLoad32 M10 (out + BitVec.ofNat 32 (4 * i)) = memLoad32 m5.mem (out + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, ← hM10, memStore8_ne (a := out + 0x40) (neq _ (by omega)),
          f8 _ (outG _ (by omega)) (sep_offsets out (c := 0x20) (n := 32) (d := 4 * i + j) (k := 1)
            (.inr (by omega)) (by omega) (by omega))]
    have es : memLoad32 Msv (s + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (s + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frSv _ (sSG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    have ed : memLoad32 Msv (d + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (d + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frSv _ (sDG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    rw [mem3, e, w5 i hi, uite, es, ed]
  · have e : memLoad32 M10 (out + 0x20 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m8.mem (out + 0x20 + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [e20, add_ofNat_assoc, add_ofNat_assoc, ← hM10, memStore8_ne (a := out + 0x40) (neq _ (by omega))]
    have es : memLoad32 m5.mem (s + 0x20 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (s + 0x20 + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [e20, add_ofNat_assoc, add_ofNat_assoc]
        exact fr5 _ (sSG.sub (c := 0x20 + (4 * i + j)) (l := 1) (by omega)).symm
          ((rs env.sOS (by decide)).subR (c := 0x20 + (4 * i + j)) (l := 1) (by omega))
    have ed : memLoad32 m5.mem (d + 0x20 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (d + 0x20 + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [e20, add_ofNat_assoc, add_ofNat_assoc]
        exact fr5 _ (sDG.sub (c := 0x20 + (4 * i + j)) (l := 1) (by omega)).symm
          ((rs env.sOD (by decide)).subR (c := 0x20 + (4 * i + j)) (l := 1) (by omega))
    rw [mem3, e, w8 i hi, uite, es, ed]
  · rw [mem3, ← hM10, memStore8_same]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
        (q.val ∈ [3, 4, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ uo2Ps, p.1 ≠ q)) := by
      decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x1C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x18 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x14 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x10 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xC (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kfin q h1
  · have hne : y ≠ out + 0x40 := fun e => ho 0x40 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)
    rw [mem3, ← hM10, memStore8_ne hne, fr8 y hy ho]

section
set_option maxRecDepth 20000
theorem cmSave_end : blockEnd ctMap384Code 2 (saveBlock cs4Ps) = some 0xA := by decide
theorem cmRestore_end : blockEnd ctMap384Code 0x36 (restoreBlock cs4Ps) = some 0x3E := by decide
end

/-- Where `CtOption<MontyFieldElement<p384>>::map` runs: its code and its
callees', the 0xA0 bytes of stack below `sp0`, the result `out`, and the option
`x`. -/
structure CMEnv (M : Word → BitVec 8) (P sp0 out x : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P ctMap384Code
  mset : CodeIn M (P + 0xEC6) memsetCode
  cs : CodeIn M (P + 0xFFFFFF14) condSelect384Code
  stub : CodeIn M (P + 0xFFFFFF14 + 0x101A) memcpyStubCode
  body : CodeIn M (P + 0xFFFFFF14 + 0x101A + 8) memcpyBodyCode
  cta : CodeIn M (P + 0xFFFFFF14 + 0x2EC) uint12CtAssignCode
  sca : CodeIn M (P + 0xFFFFFF14 + 0x2EC + 0xFFFF9B66) sliceCtAssignCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xA0 ≤ sp0.toNat
  hx : x.toNat % 4 = 0
  how : out.toNat + 0x31 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF60) 0xA0 P ctMap384Code.length
  sGM : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xEC6) memsetCode.length
  sGK : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFF14) condSelect384Code.length
  sGS : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFF14 + 0x101A) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFF14 + 0x101A + 8) memcpyBodyCode.length
  sGT : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFF14 + 0x2EC) uint12CtAssignCode.length
  sGA : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFFF14 + 0x2EC + 0xFFFF9B66) sliceCtAssignCode.length
  sOC : Sep out 0x31 P ctMap384Code.length
  sOK : Sep out 0x31 (P + 0xFFFFFF14) condSelect384Code.length
  sOB : Sep out 0x31 (P + 0xFFFFFF14 + 0x101A + 8) memcpyBodyCode.length
  sOG : Sep out 0x31 (sp0 + 0xFFFFFF60) 0xA0
  sXG : Sep x 0x31 (sp0 + 0xFFFFFF60) 0xA0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `CtOption<MontyFieldElement<p384>>::map`** to `FieldElement`:
with the option's choice byte at `x + 0x30`, it stores at `out` the 12 limbs at
`x` when the choice is 1 and zeros when it is 0, and the choice after them. -/
theorem ctMap384_correct (m : Machine) {P sp0 out x retAddr : Word} (env : CMEnv m.mem P sp0 out x)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = x)
    (hc : m.mem (x + 0x30) = 0 ∨ m.mem (x + 0x30) = 1)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 12 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if m.mem (x + 0x30) = 1 then memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) else 0) ∧
      m'.mem (out + 0x30) = m.mem (x + 0x30) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF60) 0xA0 y 1 → Sep out 0x31 y 1 → m'.mem y = m.mem y := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF60 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGM := env.sGM; have sGK := env.sGK; have sGS := env.sGS; have sGB := env.sGB
  have sGT := env.sGT; have sGA := env.sGA; have sOG := env.sOG; have sXG := env.sXG
  rw [hG] at sGC sGM sGK sGS sGB sGT sGA sOG sXG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFC0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF60) (by decide)
  have hGw : G.toNat + 0xA0 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF60 : Word).toNat = 4294967136 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0x60 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0x60) (by decide)
  have hFn : F.toNat = G.toNat + 0x60 := by rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x40 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x60 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eK : F + 0xFFFFFFA0 = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0xA0 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0xA0 → d + k ≤ 0xA0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0xA0 b code'.length → (∀ y, Sep G 0xA0 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inK : ∀ {b : Word} {l : Nat}, Sep G 0xA0 b l → Sep (F + 0xFFFFFFA0) 0x60 b l := fun h => by
    rw [eK]; exact h.sub (c := 0) (l := 0x60) (by decide)
  have inK' : ∀ {b : Word} {l : Nat}, Sep b l G 0xA0 → Sep b l (F + 0xFFFFFFA0) 0x60 := fun h => by
    rw [eK]; exact h.subR (c := 0) (l := 0x60) (by decide)
  have rs : ∀ {a b : Word} {n k l : Nat}, Sep a n b k → l ≤ n → Sep a l b k := fun {a b n k l} h hl => by
    have := h.sub (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this
  have e30 : ∀ a : Word, a + 0x30 = a + BitVec.ofNat 32 0x30 := fun _ => rfl
  obtain ⟨cb, hcb⟩ : ∃ cb, m.mem (x + 0x30) = cb := ⟨_, rfl⟩
  rw [hcb] at hc ⊢
  have hcW := (uo_choice hc).1
  have hcE := (uo_choice hc).2
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod cm4_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have slotC : ∀ (o : Word), 0x30 ≤ o.toNat → o.toNat + 4 ≤ 0x40 → ∀ {b : Word} {l : Nat}, Sep G 0xA0 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x60 + o.toNat) (l := 4) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock cs4Ps) u1 env.cod cmSave_end (saveBlock_ok _ cs4Ps _ fun p hp => by
    rw [sp1]
    simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
    exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0)) cs4Ps = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep G 0xA0 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside cs4Ps fun p hp => by
      simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) (by decide) hy
  have hslv : ∀ r o, (r, o) ∈ cs4Ps → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hc2 : CodeIn Msv P ctMap384Code := cIn env.cod sGC frSv
  -- zero the frame array
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (8 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp,
    .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0] u2.self hc2 (off' := 0x16) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have z2 := u2.self.zero
  obtain ⟨m4, c4, u4, _, k4⟩ := u3.self.memsetW (B := P + 0xEC6) (w := 12) (dst := F)
    (even_at P env.hP 0xEC6 (by decide)) hc2 (cIn env.mset sGM frSv) cm4_at_16 cm4_at_1a
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x16 + 8) (by decide)) (by decide)
    (by omega) (by decide) hFa (by rw [← eGF]; exact sGM.sub (c := 0x60) (l := 48) (by decide))
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact zw F)
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Msv F 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have frZ : ∀ y, Sep G 0xA0 y 1 → Mz y = m.mem y := fun y hy => by
    rw [← hMz, fillWords_outside 12 (by rw [← eGF]; exact hy.sub (c := 0x60) (l := 48) (by decide)), frSv y hy]
  have hc4 : CodeIn Mz P ctMap384Code := cIn env.cod sGC frZ
  have v4_8 : reg m4 8 = x := by
    rw [k4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [z2, r2 a1 (by decide), ha1]; exact zw x
  have v4_18 : reg m4 18 = out := by
    rw [k4 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw out
  have v4sp : reg m4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact sp2
  have K4 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m4 q = reg m q := fun q hq => by
    obtain ⟨h2, h3, h4, h5, h6, hr, h0, h1, h8, h18, hs, hv⟩ : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧
      q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (8 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ sp ∧ q.val ≠ 0 := by revert hq; revert q; decide
    rw [k4 q h2 h3 h4 h5 h6 hr, u3.regs, upd_ne hv h1, upd_ne hv h2, upd_ne hv h0, upd_ne hv h18, upd_ne hv h8,
      r2 q hs]
  -- select
  obtain ⟨m5, c5, u5⟩ := St.block [.lbu (9 : Fin 32) (8 : Fin 32) 0x30, .alu .add a1 x0 sp, .alu .add a0 x0 (18 : Fin 32),
    .alu .add a2 x0 (8 : Fin 32), .alu .add a3 x0 (9 : Fin 32)] u4 hc4 (off' := 0x2A) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u5
  have cz : (Mz (x + 0x30)).zeroExtend 32 = cb.zeroExtend 32 := by
    rw [frZ _ (by rw [e30]; exact (sXG.sub (c := 0x30) (l := 1) (by decide)).symm), hcb]
  have k5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (9 : Fin 32) → reg m5 q = reg m4 q :=
    fun q hv h0 h1 h2 h3 h9 => by
      rw [u5.regs, upd_ne hv h3, upd_ne hv h2, upd_ne hv h0, upd_ne hv h1, upd_ne hv h9]
  have v5_9 : reg m5 9 = cb.zeroExtend 32 := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_8, cz]
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5.self.callRa hc4 cm4_at_2a cm4_at_2e (cb := P + 0xFFFFFF14)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFF14 (by decide))
  have r6 := PEnv.reg1 regs6 u5.self.zero
  have env1 : CSEnv m6.mem (P + 0xFFFFFF14) F out F x := by
    rw [mem6]
    exact ⟨even_at P env.hP 0xFFFFFF14 (by decide), cIn env.cs sGK frZ, cIn env.stub sGS frZ, cIn env.body sGB frZ,
      cIn env.cta sGT frZ, cIn env.sca sGA frZ, hFa, by omega, env.hx, by omega, by have := env.how; omega,
      inK sGK, inK sGS, inK sGB, inK sGT, inK sGA, rs env.sOK (by decide), rs env.sOB (by decide),
      inK' (rs sOG (by decide)), by rw [eK, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide),
      inK' (rs sXG (by decide))⟩
  obtain ⟨m7, c7, pc7, sp7, w7, k7, f7⟩ := condSelect384_correct m6 env1 pc6
    (by rw [r6 sp (by decide), k5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v4sp])
    (by rw [r6 a0 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_18]; exact zw out)
    (by rw [r6 a1 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4sp]; exact zw F)
    (by rw [r6 a2 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_8]; exact zw x)
    (by rw [r6 a3 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_8, cz]; exact zw _) hcW
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x2A + 8) (by decide)))
  rw [mem6] at w7 f7
  have fr7 : ∀ y, Sep G 0xA0 y 1 → Sep out 48 y 1 → m7.mem y = m.mem y := fun y hy ho => by
    rw [f7 y (inK hy) ho, frZ y hy]
  have hc7 : CodeIn m7.mem P ctMap384Code := fun k hk => by
    rw [fr7 _ (sGC.subR (c := k) (l := 1) (by omega)) ((rs env.sOC (by decide)).subR (c := k) (l := 1) (by omega))]
    exact env.cod k hk
  have u7 : St m7.mem P m7 (0x2A + 8) (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  have kk7 : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m7 q = reg m5 q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    have hr : q ≠ ra := by clear hq'; revert hq; revert q; decide
    rw [k7 q hq', r6 q hr]
  have v7_18 : reg m7 18 = out := by
    rw [kk7 18 (by decide), k5 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v4_18]
  have v7_9 : reg m7 9 = cb.zeroExtend 32 := by rw [kk7 9 (by decide), v5_9]
  obtain ⟨m8, d8, u8⟩ := u7.sb hc7 cm4_at_32 (off' := 0x36) (by decide)
  rw [v7_18, v7_9, uo_ext_zext] at u8
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore8 m7.mem (out + 0x30) cb = M8 := ⟨_, rfl⟩
  rw [hM8] at u8
  have hc8 : CodeIn M8 P ctMap384Code := by
    rw [← hM8]; exact hc7.store8 (env.sOC.sub (c := 0x30) (l := 1) (by decide))
  have slotM : ∀ k, 0x90 ≤ k → k < 0xA0 → M8 (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    rw [← hM8, memStore8_ne (a := out + 0x30) (fun e => sOG 0x30 (by decide) k (by omega) e.symm),
      f7 _ (by rw [eK]; exact offs (.inl (by omega)) (by decide) (by omega))
        ((rs sOG (by decide)).subR (c := k) (l := 1) (by omega)),
      ← hMz, fillWords_outside 12 (by rw [← eGF]; exact offs (.inl (by omega)) (by decide) (by omega))]
  have slotW : ∀ r o, (r, o) ∈ cs4Ps → memLoad32 M8 (F + o) = reg m r := fun r o h => by
    have ho : 0x30 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x40 := by
      simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, eFk, slotM _ (by omega) (by omega)]
  have hpsp : ∀ p ∈ cs4Ps, p.1 ≠ sp := by decide
  have sp7' : reg m7 sp = F := sp7
  obtain ⟨n1, e1, w1⟩ := St.block (restoreBlock cs4Ps) u8 hc8 cmRestore_end
    (restoreBlock_ok M8 F cs4Ps (reg m7) sp7' hpsp fun q hq => by
      simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run M8 F cs4Ps (reg m7) sp7' hpsp] at w1
  have rsp1 : restoreRegs M8 F (reg m7) cs4Ps sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp7'
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M8 F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ cs4Ps → restoreRegs M8 F (reg m7) cs4Ps r = reg m r := fun r o hm => by
    simp only [cs4Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, e2, w2⟩ := w1.aluImm hc8 cm4_at_3e (off' := 0x40) (by decide)
  obtain ⟨n3, e3, pc3, mem3, regs3⟩ := w2.jalr hc8 cm4_at_40
  have kfin : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m7 q = reg m q := fun q hq => by
    have hq' : q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    obtain ⟨hv, h0, h1, h2, h3, h9⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ (9 : Fin 32) := by
      clear hq'; revert hq; revert q; decide
    rw [kk7 q hq', k5 q hv h0 h1 h2 h3 h9]; exact K4 q hq
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 (e1.trans (.cons e2
    (.single e3)))))))))), ?_, ?_, fun i hi => ?_, ?_, fun q hq => ?_, fun y hy ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x3C (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
  · have e : memLoad32 M8 (out + BitVec.ofNat 32 (4 * i)) = memLoad32 m7.mem (out + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, ← hM8, memStore8_ne (a := out + 0x30)
          (add_ofNat_ne out (c := 4 * i + j) (d := 0x30) (by omega) (by decide) (by omega))]
    have ex : memLoad32 Mz (x + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frZ _ (sXG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    have ez : memLoad32 Mz (F + BitVec.ofNat 32 (4 * i)) = 0 := by
      rw [← hMz]; exact fillWords_load 12 i hi (by omega)
    rw [mem3, e, w7 i hi, ex, ez, uite_gen hcE]
  · rw [mem3, ← hM8, memStore8_same]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        (q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ cs4Ps, p.1 ≠ q)) := by
      decide
    rcases key q hq with rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x3C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x38 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x34 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x30 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kfin q h1
  · have hne : y ≠ out + 0x30 := fun e => ho 0x30 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)
    rw [mem3, ← hM8, memStore8_ne hne, fr7 y hy (rs ho (by decide))]

section
set_option maxRecDepth 20000
theorem cm2Save_end : blockEnd ctMap256Code 2 (saveBlock cs2Ps) = some 0xA := by decide
theorem cm2Restore_end : blockEnd ctMap256Code 0x36 (restoreBlock cs2Ps) = some 0x3E := by decide
end

/-- Where `CtOption<MontyFieldElement<p256>>::map` runs: its code and its
callees', the 0x80 bytes of stack below `sp0`, the result `out`, and the option
`x`. -/
structure CM2Env (M : Word → BitVec 8) (P sp0 out x : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P ctMap256Code
  mset : CodeIn M (P + 0x2DF0) memsetCode
  cs : CodeIn M (P + 0xFFFFFC1A) condSelect256Code
  stub : CodeIn M (P + 0xFFFFFC1A + 0x323E) memcpyStubCode
  body : CodeIn M (P + 0xFFFFFC1A + 0x323E + 8) memcpyBodyCode
  sca : CodeIn M (P + 0xFFFFFC1A + 0xFFFFC076) sliceCtAssignCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x80 ≤ sp0.toNat
  hx : x.toNat % 4 = 0
  how : out.toNat + 0x21 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF80) 0x80 P ctMap256Code.length
  sGM : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0x2DF0) memsetCode.length
  sGK : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFFC1A) condSelect256Code.length
  sGS : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFFC1A + 0x323E) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFFC1A + 0x323E + 8) memcpyBodyCode.length
  sGA : Sep (sp0 + 0xFFFFFF80) 0x80 (P + 0xFFFFFC1A + 0xFFFFC076) sliceCtAssignCode.length
  sOC : Sep out 0x21 P ctMap256Code.length
  sOK : Sep out 0x21 (P + 0xFFFFFC1A) condSelect256Code.length
  sOB : Sep out 0x21 (P + 0xFFFFFC1A + 0x323E + 8) memcpyBodyCode.length
  sOG : Sep out 0x21 (sp0 + 0xFFFFFF80) 0x80
  sXG : Sep x 0x21 (sp0 + 0xFFFFFF80) 0x80

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `CtOption<MontyFieldElement<p256>>::map`** to `FieldElement`:
with the option's choice byte at `x + 0x20`, it stores at `out` the 8 limbs at
`x` when the choice is 1 and zeros when it is 0, and the choice after them. -/
theorem ctMap256_correct (m : Machine) {P sp0 out x retAddr : Word} (env : CM2Env m.mem P sp0 out x)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = x)
    (hc : m.mem (x + 0x20) = 0 ∨ m.mem (x + 0x20) = 1)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 8 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if m.mem (x + 0x20) = 1 then memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) else 0) ∧
      m'.mem (out + 0x20) = m.mem (x + 0x20) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF80) 0x80 y 1 → Sep out 0x21 y 1 → m'.mem y = m.mem y := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF80 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGM := env.sGM; have sGK := env.sGK; have sGS := env.sGS; have sGB := env.sGB
  have sGA := env.sGA; have sOG := env.sOG; have sXG := env.sXG
  rw [hG] at sGC sGM sGK sGS sGB sGA sOG sXG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFD0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF80) (by decide)
  have hGw : G.toNat + 0x80 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF80 : Word).toNat = 4294967168 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0x50 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0x50) (by decide)
  have hFn : F.toNat = G.toNat + 0x50 := by rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x30 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x50 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eK : F + 0xFFFFFFB0 = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0x80 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x80 → d + k ≤ 0x80 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x80 b code'.length → (∀ y, Sep G 0x80 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inK : ∀ {b : Word} {l : Nat}, Sep G 0x80 b l → Sep (F + 0xFFFFFFB0) 0x50 b l := fun h => by
    rw [eK]; exact h.sub (c := 0) (l := 0x50) (by decide)
  have inK' : ∀ {b : Word} {l : Nat}, Sep b l G 0x80 → Sep b l (F + 0xFFFFFFB0) 0x50 := fun h => by
    rw [eK]; exact h.subR (c := 0) (l := 0x50) (by decide)
  have rs : ∀ {a b : Word} {n k l : Nat}, Sep a n b k → l ≤ n → Sep a l b k := fun {a b n k l} h hl => by
    have := h.sub (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this
  have e20 : ∀ a : Word, a + 0x20 = a + BitVec.ofNat 32 0x20 := fun _ => rfl
  obtain ⟨cb, hcb⟩ : ∃ cb, m.mem (x + 0x20) = cb := ⟨_, rfl⟩
  rw [hcb] at hc ⊢
  have hcW := (uo_choice hc).1
  have hcE := (uo_choice hc).2
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod cm2_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have slotC : ∀ (o : Word), 0x20 ≤ o.toNat → o.toNat + 4 ≤ 0x30 → ∀ {b : Word} {l : Nat}, Sep G 0x80 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x50 + o.toNat) (l := 4) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock cs2Ps) u1 env.cod cm2Save_end (saveBlock_ok _ cs2Ps _ fun p hp => by
    rw [sp1]
    simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
    exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) cs2Ps = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep G 0x80 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside cs2Ps fun p hp => by
      simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) (by decide) hy
  have hslv : ∀ r o, (r, o) ∈ cs2Ps → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hc2 : CodeIn Msv P ctMap256Code := cIn env.cod sGC frSv
  -- zero the frame array
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (8 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp,
    .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0] u2.self hc2 (off' := 0x16) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have z2 := u2.self.zero
  obtain ⟨m4, c4, u4, _, k4⟩ := u3.self.memsetW (B := P + 0x2DF0) (w := 8) (dst := F)
    (even_at P env.hP 0x2DF0 (by decide)) hc2 (cIn env.mset sGM frSv) cm2_at_16 cm2_at_1a
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x16 + 8) (by decide)) (by decide)
    (by omega) (by decide) hFa (by rw [← eGF]; exact sGM.sub (c := 0x50) (l := 32) (by decide))
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact zw F)
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Msv F 0 8 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have frZ : ∀ y, Sep G 0x80 y 1 → Mz y = m.mem y := fun y hy => by
    rw [← hMz, fillWords_outside 8 (by rw [← eGF]; exact hy.sub (c := 0x50) (l := 32) (by decide)), frSv y hy]
  have hc4 : CodeIn Mz P ctMap256Code := cIn env.cod sGC frZ
  have v4_8 : reg m4 8 = x := by
    rw [k4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [z2, r2 a1 (by decide), ha1]; exact zw x
  have v4_18 : reg m4 18 = out := by
    rw [k4 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw out
  have v4sp : reg m4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact sp2
  have K4 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m4 q = reg m q := fun q hq => by
    obtain ⟨h2, h3, h4, h5, h6, hr, h0, h1, h8, h18, hs, hv⟩ : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧
      q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (8 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ sp ∧ q.val ≠ 0 := by revert hq; revert q; decide
    rw [k4 q h2 h3 h4 h5 h6 hr, u3.regs, upd_ne hv h1, upd_ne hv h2, upd_ne hv h0, upd_ne hv h18, upd_ne hv h8,
      r2 q hs]
  -- select
  obtain ⟨m5, c5, u5⟩ := St.block [.lbu (9 : Fin 32) (8 : Fin 32) 0x20, .alu .add a1 x0 sp, .alu .add a0 x0 (18 : Fin 32),
    .alu .add a2 x0 (8 : Fin 32), .alu .add a3 x0 (9 : Fin 32)] u4 hc4 (off' := 0x2A) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u5
  have cz : (Mz (x + 0x20)).zeroExtend 32 = cb.zeroExtend 32 := by
    rw [frZ _ (by rw [e20]; exact (sXG.sub (c := 0x20) (l := 1) (by decide)).symm), hcb]
  have k5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (9 : Fin 32) → reg m5 q = reg m4 q :=
    fun q hv h0 h1 h2 h3 h9 => by
      rw [u5.regs, upd_ne hv h3, upd_ne hv h2, upd_ne hv h0, upd_ne hv h1, upd_ne hv h9]
  have v5_9 : reg m5 9 = cb.zeroExtend 32 := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_8, cz]
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5.self.callRa hc4 cm2_at_2a cm2_at_2e (cb := P + 0xFFFFFC1A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFC1A (by decide))
  have r6 := PEnv.reg1 regs6 u5.self.zero
  have env1 : CS2Env m6.mem (P + 0xFFFFFC1A) F out F x := by
    rw [mem6]
    exact ⟨even_at P env.hP 0xFFFFFC1A (by decide), cIn env.cs sGK frZ, cIn env.stub sGS frZ, cIn env.body sGB frZ,
      cIn env.sca sGA frZ, hFa, by omega, env.hx, by omega, by have := env.how; omega,
      inK sGK, inK sGS, inK sGB, inK sGA, rs env.sOK (by decide), rs env.sOB (by decide),
      inK' (rs sOG (by decide)), by rw [eK, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide),
      inK' (rs sXG (by decide))⟩
  obtain ⟨m7, c7, pc7, sp7, w7, k7, f7⟩ := condSelect256_correct m6 env1 pc6
    (by rw [r6 sp (by decide), k5 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v4sp])
    (by rw [r6 a0 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_18]; exact zw out)
    (by rw [r6 a1 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4sp]; exact zw F)
    (by rw [r6 a2 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_8]; exact zw x)
    (by rw [r6 a3 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_8, cz]; exact zw _) hcW
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x2A + 8) (by decide)))
  rw [mem6] at w7 f7
  have fr7 : ∀ y, Sep G 0x80 y 1 → Sep out 32 y 1 → m7.mem y = m.mem y := fun y hy ho => by
    rw [f7 y (inK hy) ho, frZ y hy]
  have hc7 : CodeIn m7.mem P ctMap256Code := fun k hk => by
    rw [fr7 _ (sGC.subR (c := k) (l := 1) (by omega)) ((rs env.sOC (by decide)).subR (c := k) (l := 1) (by omega))]
    exact env.cod k hk
  have u7 : St m7.mem P m7 (0x2A + 8) (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  have kk7 : ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m7 q = reg m5 q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    have hr : q ≠ ra := by clear hq'; revert hq; revert q; decide
    rw [k7 q hq', r6 q hr]
  have v7_18 : reg m7 18 = out := by
    rw [kk7 18 (by decide), k5 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v4_18]
  have v7_9 : reg m7 9 = cb.zeroExtend 32 := by rw [kk7 9 (by decide), v5_9]
  obtain ⟨m8, d8, u8⟩ := u7.sb hc7 cm2_at_32 (off' := 0x36) (by decide)
  rw [v7_18, v7_9, uo_ext_zext] at u8
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore8 m7.mem (out + 0x20) cb = M8 := ⟨_, rfl⟩
  rw [hM8] at u8
  have hc8 : CodeIn M8 P ctMap256Code := by
    rw [← hM8]; exact hc7.store8 (env.sOC.sub (c := 0x20) (l := 1) (by decide))
  have slotM : ∀ k, 0x70 ≤ k → k < 0x80 → M8 (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    rw [← hM8, memStore8_ne (a := out + 0x20) (fun e => sOG 0x20 (by decide) k (by omega) e.symm),
      f7 _ (by rw [eK]; exact offs (.inl (by omega)) (by decide) (by omega))
        ((rs sOG (by decide)).subR (c := k) (l := 1) (by omega)),
      ← hMz, fillWords_outside 8 (by rw [← eGF]; exact offs (.inl (by omega)) (by decide) (by omega))]
  have slotW : ∀ r o, (r, o) ∈ cs2Ps → memLoad32 M8 (F + o) = reg m r := fun r o h => by
    have ho : 0x20 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x30 := by
      simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, eFk, slotM _ (by omega) (by omega)]
  have hpsp : ∀ p ∈ cs2Ps, p.1 ≠ sp := by decide
  have sp7' : reg m7 sp = F := sp7
  obtain ⟨n1, e1, w1⟩ := St.block (restoreBlock cs2Ps) u8 hc8 cm2Restore_end
    (restoreBlock_ok M8 F cs2Ps (reg m7) sp7' hpsp fun q hq => by
      simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run M8 F cs2Ps (reg m7) sp7' hpsp] at w1
  have rsp1 : restoreRegs M8 F (reg m7) cs2Ps sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp7'
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M8 F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ cs2Ps → restoreRegs M8 F (reg m7) cs2Ps r = reg m r := fun r o hm => by
    simp only [cs2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, e2, w2⟩ := w1.aluImm hc8 cm2_at_3e (off' := 0x40) (by decide)
  obtain ⟨n3, e3, pc3, mem3, regs3⟩ := w2.jalr hc8 cm2_at_40
  have kfin : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m7 q = reg m q := fun q hq => by
    have hq' : q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    obtain ⟨hv, h0, h1, h2, h3, h9⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ (9 : Fin 32) := by
      clear hq'; revert hq; revert q; decide
    rw [kk7 q hq', k5 q hv h0 h1 h2 h3 h9]; exact K4 q hq
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 (e1.trans (.cons e2
    (.single e3)))))))))), ?_, ?_, fun i hi => ?_, ?_, fun q hq => ?_, fun y hy ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x2C (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
  · have e : memLoad32 M8 (out + BitVec.ofNat 32 (4 * i)) = memLoad32 m7.mem (out + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, ← hM8, memStore8_ne (a := out + 0x20)
          (add_ofNat_ne out (c := 4 * i + j) (d := 0x20) (by omega) (by decide) (by omega))]
    have ex : memLoad32 Mz (x + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frZ _ (sXG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    have ez : memLoad32 Mz (F + BitVec.ofNat 32 (4 * i)) = 0 := by
      rw [← hMz]; exact fillWords_load 8 i hi (by omega)
    rw [mem3, e, w7 i hi, ex, ez, uite_gen hcE]
  · rw [mem3, ← hM8, memStore8_same]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        (q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ cs2Ps, p.1 ≠ q)) := by
      decide
    rcases key q hq with rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x2C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x28 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x24 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x20 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kfin q h1
  · have hne : y ≠ out + 0x20 := fun e => ho 0x20 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)
    rw [mem3, ← hM8, memStore8_ne hne, fr7 y hy (rs ho (by decide))]

end C3.RV32
