import C3BootProofs.Proofs.CondNeg12
import C3BootProofs.Proofs.AbsSign2
import C3BootProofs.Proofs.WideMul12x2
import C3BootProofs.Proofs.MontMul12Main
import C3BootProofs.Proofs.ShrWide12

/-!
# `safegcd`'s `SignedInt<12>::lincomb_int::<2>`, as compiled

Bernstein-Yang inversion keeps signed 384-bit values as a magnitude and a
sign byte, and this function computes `a * c + b * d` for two of them and two
signed 64-bit `Int<2>` values `c` and `d`. The compiled code takes `c`'s and
`d`'s absolute values and signs with `Int<2>::abs_sign`, forms the 448-bit
products `|a| |c|` and `|b| |d|` with `widening_mul_fixed::<12, 2>`, negates
the second one when the two products have the same sign, subtracts it from
the first with 14 calls to `borrowing_sub`, and negates the difference when
the subtraction borrowed and the signs differed. It writes the 448-bit
magnitude and a sign byte to `out`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem lc12_at_0 : fetchRel lincomb12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF00, 2) := by decide
theorem lc12_at_2 : fetchRel lincomb12Code 0x2 = some (.store .sw sp ra 0xFC, 2) := by decide
theorem lc12_at_4 : fetchRel lincomb12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0xF8, 2) := by decide
theorem lc12_at_6 : fetchRel lincomb12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0xF4, 2) := by decide
theorem lc12_at_8 : fetchRel lincomb12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0xF0, 2) := by decide
theorem lc12_at_a : fetchRel lincomb12Code 0xA = some (.store .sw sp (19 : Fin 32) 0xEC, 2) := by decide
theorem lc12_at_c : fetchRel lincomb12Code 0xC = some (.store .sw sp (20 : Fin 32) 0xE8, 2) := by decide
theorem lc12_at_e : fetchRel lincomb12Code 0xE = some (.store .sw sp (21 : Fin 32) 0xE4, 2) := by decide
theorem lc12_at_10 : fetchRel lincomb12Code 0x10 = some (.store .sw sp (22 : Fin 32) 0xE0, 2) := by decide
theorem lc12_at_12 : fetchRel lincomb12Code 0x12 = some (.store .sw sp (23 : Fin 32) 0xDC, 2) := by decide
theorem lc12_at_14 : fetchRel lincomb12Code 0x14 = some (.store .sw sp (24 : Fin 32) 0xD8, 2) := by decide
theorem lc12_at_16 : fetchRel lincomb12Code 0x16 = some (.alu .add (8 : Fin 32) x0 a4, 2) := by decide
theorem lc12_at_18 : fetchRel lincomb12Code 0x18 = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem lc12_at_1a : fetchRel lincomb12Code 0x1A = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem lc12_at_1c : fetchRel lincomb12Code 0x1C = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem lc12_at_1e : fetchRel lincomb12Code 0x1E = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem lc12_at_20 : fetchRel lincomb12Code 0x20 = some (.alu .add a1 x0 a3, 2) := by decide
theorem lc12_at_22 : fetchRel lincomb12Code 0x22 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem lc12_at_26 : fetchRel lincomb12Code 0x26 = some (.jalr ra ra 0x52C, 4) := by decide
theorem lc12_at_2a : fetchRel lincomb12Code 0x2A = some (.load .lbu (20 : Fin 32) sp 0x10, 4) := by decide
theorem lc12_at_2e : fetchRel lincomb12Code 0x2E = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem lc12_at_30 : fetchRel lincomb12Code 0x30 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem lc12_at_32 : fetchRel lincomb12Code 0x32 = some (.auipc ra 0xFFFFA000, 4) := by decide
theorem lc12_at_36 : fetchRel lincomb12Code 0x36 = some (.jalr ra ra 0x51C, 4) := by decide
theorem lc12_at_3a : fetchRel lincomb12Code 0x3A = some (.load .lbu (8 : Fin 32) sp 0x1C, 4) := by decide
theorem lc12_at_3e : fetchRel lincomb12Code 0x3E = some (.aluImm .add a0 sp 0x68, 2) := by decide
theorem lc12_at_40 : fetchRel lincomb12Code 0x40 = some (.aluImm .add a2 sp 0x8, 2) := by decide
theorem lc12_at_42 : fetchRel lincomb12Code 0x42 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem lc12_at_44 : fetchRel lincomb12Code 0x44 = some (.aluImm .add (22 : Fin 32) sp 0x68, 4) := by decide
theorem lc12_at_48 : fetchRel lincomb12Code 0x48 = some (.auipc ra 0x0, 4) := by decide
theorem lc12_at_4c : fetchRel lincomb12Code 0x4C = some (.jalr ra ra 0x350, 4) := by decide
theorem lc12_at_50 : fetchRel lincomb12Code 0x50 = some (.load .lw a0 sp 0x98, 2) := by decide
theorem lc12_at_52 : fetchRel lincomb12Code 0x52 = some (.load .lw a1 sp 0x9C, 2) := by decide
theorem lc12_at_54 : fetchRel lincomb12Code 0x54 = some (.load .lbu a2 (9 : Fin 32) 0x30, 4) := by decide
theorem lc12_at_58 : fetchRel lincomb12Code 0x58 = some (.store .sw sp a0 0x20, 2) := by decide
theorem lc12_at_5a : fetchRel lincomb12Code 0x5A = some (.store .sw sp a1 0x24, 2) := by decide
theorem lc12_at_5c : fetchRel lincomb12Code 0x5C = some (.alu .xor (20 : Fin 32) a2 (20 : Fin 32), 4) := by decide
theorem lc12_at_60 : fetchRel lincomb12Code 0x60 = some (.aluImm .add a0 sp 0x30, 2) := by decide
theorem lc12_at_62 : fetchRel lincomb12Code 0x62 = some (.aluImm .add a2 sp 0x14, 2) := by decide
theorem lc12_at_64 : fetchRel lincomb12Code 0x64 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem lc12_at_66 : fetchRel lincomb12Code 0x66 = some (.aluImm .add (23 : Fin 32) sp 0x30, 4) := by decide
theorem lc12_at_6a : fetchRel lincomb12Code 0x6A = some (.auipc ra 0x0, 4) := by decide
theorem lc12_at_6e : fetchRel lincomb12Code 0x6E = some (.jalr ra ra 0x32E, 4) := by decide
theorem lc12_at_72 : fetchRel lincomb12Code 0x72 = some (.load .lbu a0 (19 : Fin 32) 0x30, 4) := by decide
theorem lc12_at_76 : fetchRel lincomb12Code 0x76 = some (.load .lw a1 sp 0x60, 2) := by decide
theorem lc12_at_78 : fetchRel lincomb12Code 0x78 = some (.load .lw a2 sp 0x64, 2) := by decide
theorem lc12_at_7a : fetchRel lincomb12Code 0x7A = some (.alu .xor (19 : Fin 32) a0 (8 : Fin 32), 4) := by decide
theorem lc12_at_7e : fetchRel lincomb12Code 0x7E = some (.alu .xor (21 : Fin 32) (19 : Fin 32) (20 : Fin 32), 4) := by decide
theorem lc12_at_82 : fetchRel lincomb12Code 0x82 = some (.aluImm .xor a0 (21 : Fin 32) 0x1, 4) := by decide
theorem lc12_at_86 : fetchRel lincomb12Code 0x86 = some (.store .sw sp a1 0x28, 2) := by decide
theorem lc12_at_88 : fetchRel lincomb12Code 0x88 = some (.store .sw sp a2 0x2C, 2) := by decide
theorem lc12_at_8a : fetchRel lincomb12Code 0x8A = some (.aluImm .and a2 a0 0xFF, 4) := by decide
theorem lc12_at_8e : fetchRel lincomb12Code 0x8E = some (.aluImm .add a0 sp 0x30, 2) := by decide
theorem lc12_at_90 : fetchRel lincomb12Code 0x90 = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem lc12_at_92 : fetchRel lincomb12Code 0x92 = some (.auipc ra 0x0, 4) := by decide
theorem lc12_at_96 : fetchRel lincomb12Code 0x96 = some (.jalr ra ra 0x3F0, 4) := by decide
theorem lc12_at_9a : fetchRel lincomb12Code 0x9A = some (.aluImm .add a0 sp 0xA8, 2) := by decide
theorem lc12_at_9c : fetchRel lincomb12Code 0x9C = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lc12_at_a0 : fetchRel lincomb12Code 0xA0 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem lc12_at_a2 : fetchRel lincomb12Code 0xA2 = some (.aluImm .add (8 : Fin 32) sp 0xA8, 2) := by decide
theorem lc12_at_a4 : fetchRel lincomb12Code 0xA4 = some (.auipc ra 0x2000, 4) := by decide
theorem lc12_at_a8 : fetchRel lincomb12Code 0xA8 = some (.jalr ra ra 0xFFFFF804, 4) := by decide
theorem lc12_at_ac : fetchRel lincomb12Code 0xAC = some (.aluImm .add (24 : Fin 32) x0 0x0, 2) := by decide
theorem lc12_at_ae : fetchRel lincomb12Code 0xAE = some (.aluImm .add (9 : Fin 32) x0 0xC, 2) := by decide
theorem lc12_at_b0 : fetchRel lincomb12Code 0xB0 = some (.branch .beq (9 : Fin 32) x0 0x22, 2) := by decide
theorem lc12_at_b2 : fetchRel lincomb12Code 0xB2 = some (.load .lw a0 (22 : Fin 32) 0x0, 4) := by decide
theorem lc12_at_b6 : fetchRel lincomb12Code 0xB6 = some (.load .lw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem lc12_at_ba : fetchRel lincomb12Code 0xBA = some (.alu .add a2 x0 (24 : Fin 32), 2) := by decide
theorem lc12_at_bc : fetchRel lincomb12Code 0xBC = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem lc12_at_c0 : fetchRel lincomb12Code 0xC0 = some (.jalr ra ra 0x326, 4) := by decide
theorem lc12_at_c4 : fetchRel lincomb12Code 0xC4 = some (.alu .add (24 : Fin 32) x0 a1, 2) := by decide
theorem lc12_at_c6 : fetchRel lincomb12Code 0xC6 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x4, 2) := by decide
theorem lc12_at_c8 : fetchRel lincomb12Code 0xC8 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem lc12_at_ca : fetchRel lincomb12Code 0xCA = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem lc12_at_cc : fetchRel lincomb12Code 0xCC = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem lc12_at_ce : fetchRel lincomb12Code 0xCE = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lc12_at_d0 : fetchRel lincomb12Code 0xD0 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem lc12_at_d2 : fetchRel lincomb12Code 0xD2 = some (.aluImm .add a0 sp 0x68, 2) := by decide
theorem lc12_at_d4 : fetchRel lincomb12Code 0xD4 = some (.aluImm .add a1 sp 0xA8, 2) := by decide
theorem lc12_at_d6 : fetchRel lincomb12Code 0xD6 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lc12_at_da : fetchRel lincomb12Code 0xDA = some (.auipc ra 0x2000, 4) := by decide
theorem lc12_at_de : fetchRel lincomb12Code 0xDE = some (.jalr ra ra 0xFFFFF836, 4) := by decide
theorem lc12_at_e2 : fetchRel lincomb12Code 0xE2 = some (.store .sw sp x0 0xA0, 2) := by decide
theorem lc12_at_e4 : fetchRel lincomb12Code 0xE4 = some (.store .sw sp x0 0xA4, 2) := by decide
theorem lc12_at_e6 : fetchRel lincomb12Code 0xE6 = some (.aluImm .add (22 : Fin 32) sp 0x20, 4) := by decide
theorem lc12_at_ea : fetchRel lincomb12Code 0xEA = some (.aluImm .add (23 : Fin 32) sp 0x28, 4) := by decide
theorem lc12_at_ee : fetchRel lincomb12Code 0xEE = some (.aluImm .add (8 : Fin 32) sp 0xA0, 2) := by decide
theorem lc12_at_f0 : fetchRel lincomb12Code 0xF0 = some (.aluImm .add (9 : Fin 32) x0 0x2, 2) := by decide
theorem lc12_at_f2 : fetchRel lincomb12Code 0xF2 = some (.branch .beq (9 : Fin 32) x0 0x22, 2) := by decide
theorem lc12_at_f4 : fetchRel lincomb12Code 0xF4 = some (.load .lw a0 (22 : Fin 32) 0x0, 4) := by decide
theorem lc12_at_f8 : fetchRel lincomb12Code 0xF8 = some (.load .lw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem lc12_at_fc : fetchRel lincomb12Code 0xFC = some (.alu .add a2 x0 (24 : Fin 32), 2) := by decide
theorem lc12_at_fe : fetchRel lincomb12Code 0xFE = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem lc12_at_102 : fetchRel lincomb12Code 0x102 = some (.jalr ra ra 0x2E4, 4) := by decide
theorem lc12_at_106 : fetchRel lincomb12Code 0x106 = some (.alu .add (24 : Fin 32) x0 a1, 2) := by decide
theorem lc12_at_108 : fetchRel lincomb12Code 0x108 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x4, 2) := by decide
theorem lc12_at_10a : fetchRel lincomb12Code 0x10A = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem lc12_at_10c : fetchRel lincomb12Code 0x10C = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem lc12_at_10e : fetchRel lincomb12Code 0x10E = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem lc12_at_110 : fetchRel lincomb12Code 0x110 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem lc12_at_112 : fetchRel lincomb12Code 0x112 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE2, 2) := by decide
theorem lc12_at_114 : fetchRel lincomb12Code 0x114 = some (.load .lw a0 sp 0xA0, 2) := by decide
theorem lc12_at_116 : fetchRel lincomb12Code 0x116 = some (.load .lw a1 sp 0xA4, 2) := by decide
theorem lc12_at_118 : fetchRel lincomb12Code 0x118 = some (.store .sw sp a0 0x20, 2) := by decide
theorem lc12_at_11a : fetchRel lincomb12Code 0x11A = some (.store .sw sp a1 0x24, 2) := by decide
theorem lc12_at_11c : fetchRel lincomb12Code 0x11C = some (.store .sw sp (24 : Fin 32) 0xA0, 2) := by decide
theorem lc12_at_11e : fetchRel lincomb12Code 0x11E = some (.aluImm .add a0 sp 0xA0, 2) := by decide
theorem lc12_at_120 : fetchRel lincomb12Code 0x120 = some (.load .lw a0 sp 0xA0, 2) := by decide
theorem lc12_at_122 : fetchRel lincomb12Code 0x122 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem lc12_at_126 : fetchRel lincomb12Code 0x126 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem lc12_at_128 : fetchRel lincomb12Code 0x128 = some (.alu .and (8 : Fin 32) (21 : Fin 32) a0, 4) := by decide
theorem lc12_at_12c : fetchRel lincomb12Code 0x12C = some (.aluImm .and (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem lc12_at_12e : fetchRel lincomb12Code 0x12E = some (.aluImm .add a0 sp 0x68, 2) := by decide
theorem lc12_at_130 : fetchRel lincomb12Code 0x130 = some (.aluImm .add a1 sp 0x20, 2) := by decide
theorem lc12_at_132 : fetchRel lincomb12Code 0x132 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem lc12_at_134 : fetchRel lincomb12Code 0x134 = some (.auipc ra 0x0, 4) := by decide
theorem lc12_at_138 : fetchRel lincomb12Code 0x138 = some (.jalr ra ra 0x34E, 4) := by decide
theorem lc12_at_13c : fetchRel lincomb12Code 0x13C = some (.load .lw (9 : Fin 32) sp 0x20, 2) := by decide
theorem lc12_at_13e : fetchRel lincomb12Code 0x13E = some (.load .lw (21 : Fin 32) sp 0x24, 2) := by decide
theorem lc12_at_140 : fetchRel lincomb12Code 0x140 = some (.aluImm .xor a0 (8 : Fin 32) 0x1, 4) := by decide
theorem lc12_at_144 : fetchRel lincomb12Code 0x144 = some (.alu .and a0 a0 (20 : Fin 32), 4) := by decide
theorem lc12_at_148 : fetchRel lincomb12Code 0x148 = some (.alu .and a1 (8 : Fin 32) (19 : Fin 32), 4) := by decide
theorem lc12_at_14c : fetchRel lincomb12Code 0x14C = some (.alu .or (8 : Fin 32) a0 a1, 4) := by decide
theorem lc12_at_150 : fetchRel lincomb12Code 0x150 = some (.aluImm .add a1 sp 0x68, 2) := by decide
theorem lc12_at_152 : fetchRel lincomb12Code 0x152 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem lc12_at_156 : fetchRel lincomb12Code 0x156 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem lc12_at_158 : fetchRel lincomb12Code 0x158 = some (.auipc ra 0x1000, 4) := by decide
theorem lc12_at_15c : fetchRel lincomb12Code 0x15C = some (.jalr ra ra 0x7B8, 4) := by decide
theorem lc12_at_160 : fetchRel lincomb12Code 0x160 = some (.store .sw (18 : Fin 32) (9 : Fin 32) 0x30, 4) := by decide
theorem lc12_at_164 : fetchRel lincomb12Code 0x164 = some (.store .sw (18 : Fin 32) (21 : Fin 32) 0x34, 4) := by decide
theorem lc12_at_168 : fetchRel lincomb12Code 0x168 = some (.store .sb (18 : Fin 32) (8 : Fin 32) 0x38, 4) := by decide
theorem lc12_at_16c : fetchRel lincomb12Code 0x16C = some (.load .lw ra sp 0xFC, 2) := by decide
theorem lc12_at_16e : fetchRel lincomb12Code 0x16E = some (.load .lw (8 : Fin 32) sp 0xF8, 2) := by decide
theorem lc12_at_170 : fetchRel lincomb12Code 0x170 = some (.load .lw (9 : Fin 32) sp 0xF4, 2) := by decide
theorem lc12_at_172 : fetchRel lincomb12Code 0x172 = some (.load .lw (18 : Fin 32) sp 0xF0, 2) := by decide
theorem lc12_at_174 : fetchRel lincomb12Code 0x174 = some (.load .lw (19 : Fin 32) sp 0xEC, 2) := by decide
theorem lc12_at_176 : fetchRel lincomb12Code 0x176 = some (.load .lw (20 : Fin 32) sp 0xE8, 2) := by decide
theorem lc12_at_178 : fetchRel lincomb12Code 0x178 = some (.load .lw (21 : Fin 32) sp 0xE4, 2) := by decide
theorem lc12_at_17a : fetchRel lincomb12Code 0x17A = some (.load .lw (22 : Fin 32) sp 0xE0, 2) := by decide
theorem lc12_at_17c : fetchRel lincomb12Code 0x17C = some (.load .lw (23 : Fin 32) sp 0xDC, 2) := by decide
theorem lc12_at_17e : fetchRel lincomb12Code 0x17E = some (.load .lw (24 : Fin 32) sp 0xD8, 2) := by decide
theorem lc12_at_180 : fetchRel lincomb12Code 0x180 = some (.aluImm .add sp sp 0x100, 2) := by decide
theorem lc12_at_182 : fetchRel lincomb12Code 0x182 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `borrowing_sub`'s offset from `lincomb_int`. -/
abbrev lcBsub (P : Word) : Word := P + 0xFFFEF3E2

/-- The start of one limb of the difference: load the limbs and the borrow. -/
def lcHead : List BInstr := [.lw a0 (22 : Fin 32) 0x0, .lw a1 (23 : Fin 32) 0x0, .alu .add a2 x0 (24 : Fin 32)]

/-- The end of one limb of the difference: keep the borrow, store the limb,
and step the pointers and the count. -/
def lcTail : List BInstr :=
  [.alu .add (24 : Fin 32) x0 a1, .aluImm .add (22 : Fin 32) (22 : Fin 32) 0x4, .sw (8 : Fin 32) a0 0x0,
   .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

/-- Where one of the function's two subtraction loops sits: its head at `o`,
and the call to `borrowing_sub` at `o + 0xA`. -/
structure LcLoopAt (o : Nat) (imm jo : Word) : Prop where
  hHead : blockEnd lincomb12Code o lcHead = some (o + 0xA)
  h1 : fetchRel lincomb12Code (o + 0xA) = some (.auipc ra imm, 4)
  h2 : fetchRel lincomb12Code (o + 0xA + 4) = some (.jalr ra ra jo, 4)
  hcb : BitVec.ofNat 32 (o + 0xA) + imm + jo = 0xFFFEF3E2
  hTail : blockEnd lincomb12Code (o + 0xA + 8) lcTail = some (o + 0x1E)
  hBr : fetchRel lincomb12Code (o + 0x1E) = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE2, 2)
  hBt : BitVec.ofNat 32 (o + 0x1E) + 0xFFFFFFE2 = BitVec.ofNat 32 o
  hev : o % 2 = 0
  hlt : o + 0x20 < 2 ^ 32

section
set_option maxRecDepth 20000
theorem lcLoop1 : LcLoopAt 0xB2 0xFFFEF000 0x326 :=
  ⟨by decide, lc12_at_bc, lc12_at_c0, by decide, by decide, lc12_at_d0, by decide, by decide,
    by decide⟩
theorem lcLoop2 : LcLoopAt 0xF4 0xFFFEF000 0x2E4 :=
  ⟨by decide, lc12_at_fe, lc12_at_102, by decide, by decide, lc12_at_112, by decide,
    by decide, by decide⟩
end

/-- The registers one limb of the difference leaves alone. -/
def lcSubKeep (q : Fin 32) : Bool := q.val ∉ [0, 1, 8, 9, 10, 11, 12, 13, 14, 22, 23, 24]

theorem lc_cnt_dec {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    BitVec.ofNat 32 (N - i) + 0xFFFFFFFF = BitVec.ofNat 32 (N - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega)]
  show (N - i + 4294967295) % 2 ^ 32 = N - (i + 1); omega

theorem lc_cnt_ne {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    (BitVec.ofNat 32 (N - (i + 1)) != 0) = decide (i + 1 < N) := by
  by_cases h : i + 1 < N
  · rw [decide_eq_true h]; simp only [bne_iff_ne, ne_eq]; intro e
    have := congrArg BitVec.toNat e; rw [ofNat_tn (by omega)] at this
    exact absurd this (by show N - (i + 1) ≠ 0; omega)
  · rw [decide_eq_false h, show N - (i + 1) = 0 by omega]; rfl


set_option maxRecDepth 20000 in
theorem lcHead_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lcHead (M, f)).1 = M ∧
    (runBlock lcHead (M, f)).2 a0 = memLoad32 M (f 22 + 0) ∧
    (runBlock lcHead (M, f)).2 a1 = memLoad32 M (f 23 + 0) ∧
    (runBlock lcHead (M, f)).2 a2 = f 24 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → (runBlock lcHead (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, lcHead, upd_app, ↓reduceIte]
  refine ⟨trivial, trivial, trivial, BitVec.zero_add _, fun q q0 q1 q2 => ?_⟩
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp [h0, q0, q1, q2]

set_option maxRecDepth 20000 in
theorem lcHead_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h22 : (f 22 + 0).toNat % 4 = 0) (h23 : (f 23 + 0).toNat % 4 = 0) : BlockOk base len lcHead (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lcHead, upd_app, ↓reduceIte, and_true]
  exact ⟨h22, h23⟩

set_option maxRecDepth 20000 in
theorem lcTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock lcTail (M, f)).1 = memStore32 M (f 8 + 0) (f a0) ∧
    (runBlock lcTail (M, f)).2 24 = f a1 ∧
    (runBlock lcTail (M, f)).2 22 = f 22 + 4 ∧
    (runBlock lcTail (M, f)).2 23 = f 23 + 4 ∧
    (runBlock lcTail (M, f)).2 8 = f 8 + 4 ∧
    (runBlock lcTail (M, f)).2 9 = f 9 + 0xFFFFFFFF ∧
    ∀ q, q ≠ (24 : Fin 32) → q ≠ (22 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) →
      (runBlock lcTail (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, lcTail, upd_app, ↓reduceIte]
  refine ⟨trivial, ?_, rfl, rfl, rfl, rfl, fun q q24 q22 q23 q8 q9 => ?_⟩
  · rw [hz]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp [h0, q24, q22, q23, q8, q9]

set_option maxRecDepth 20000 in
theorem lcTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f 8 + 0).toNat % 4 = 0) (hs : Sep (f 8 + 0) 4 base len) : BlockOk base len lcTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, lcTail, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One limb of the difference**, from the loop head at `o`: subtract
limb `i` of the right operand and the borrow from limb `i` of the left
operand, and store the difference at limb `i` of `D`. `borrowing_sub` also
writes the word below `sp`. -/
theorem lc_sub_iter {M : Word → BitVec 8} {P F lp rp D b imm jo : Word} {n : Machine} {o N i : Nat}
    (L : LcLoopAt o imm jo) (s : St M P n o (reg n)) (hc : CodeIn M P lincomb12Code)
    (hb : CodeIn M (lcBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < N) (hN : N ≤ 12) (hF : F.toNat % 4 = 0) (hlp : lp.toNat % 4 = 0)
    (hrp : rp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (lcBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P lincomb12Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P lincomb12Code.length)
    (rsp : reg n sp = F) (r22 : reg n 22 = lp + BitVec.ofNat 32 (4 * i))
    (r23 : reg n 23 = rp + BitVec.ofNat 32 (4 * i)) (r8 : reg n 8 = D + BitVec.ofNat 32 (4 * i))
    (r9 : reg n 9 = BitVec.ofNat 32 (N - i)) (r24 : reg n 24 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < N then o else o + 0x20) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' 24 = bsubB (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' 22 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' 23 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 8 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' 9 = BitVec.ofNat 32 (N - (i + 1)) ∧
      ∀ q, lcSubKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨E1, Ea0, Ea1, Ea2, Ek⟩ := lcHead_run (M := M) (f := reg n) hz
  obtain ⟨n1, c1, u1⟩ := St.block lcHead s hc L.hHead
    (lcHead_ok (by rw [r22, add_lit_zero]; exact aligned_add hlp (by omega))
      (by rw [r23, add_lit_zero]; exact aligned_add hrp (by omega)))
  rw [E1] at u1
  rw [r22, add_lit_zero] at Ea0
  rw [r23, add_lit_zero] at Ea1
  rw [r24] at Ea2
  have g1 : ∀ q, reg n1 q = (runBlock lcHead (M, reg n)).2 q := u1.regs
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u1.self.bsubCall hc hb (even_at P hP 0xFFFEF3E2 (by decide))
    L.h1 L.h2 (by rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (BitVec.ofNat 32 (o + 0xA)), L.hcb]) (even_at P hP (o + 0xA + 8) (by
      have := L.hev; omega))
    (by rw [g1, Ek sp (by decide) (by decide) (by decide), rsp]) hF sFB
  simp only [g1] at a03 a13
  rw [Ea0, Ea1, Ea2] at a03 a13
  have hc3 : CodeIn n3.mem P lincomb12Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q :=
    fun q q0 q1 q2 q3 q4 qr => by rw [fr3 q q0 q1 q2 q3 q4 qr, g1, Ek q q0 q1 q2]
  have e8 : reg n3 8 + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block lcTail u3 hc3 L.hTail
    (lcTail_ok (by rw [e8]; exact aligned_add hD (by omega)) (by rw [e8]; exact sDC))
  obtain ⟨em4, t24, t22, t23, t8, t9, tk⟩ := lcTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, e8, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock lcTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (lp + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (rp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have k3' : ∀ r, r = (22 : Fin 32) ∨ r = (23 : Fin 32) ∨ r = (8 : Fin 32) ∨ r = (9 : Fin 32) → reg n3 r = reg n r :=
    fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
      exact k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e9 : reg n4 9 = BitVec.ofNat 32 (N - (i + 1)) := by
    rw [g4, t9, k3' 9 (by decide), r9, lc_cnt_dec hi (by omega)]
  have hb4 : branchTaken .bne (reg n4 9) (reg n4 x0) = decide (i + 1 < N) := by
    rw [e9, u4'.zero]; exact lc_cnt_ne hi (by omega)
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 24 = bsubB (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M (rp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 22 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 23 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n5 8 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 9 = BitVec.ofNat 32 (N - (i + 1)) ∧
      ∀ q, lcSubKeep q = true → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t24, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      by rw [h5, g4, t22, k3' 22 (by decide), r22, ptr4], by rw [h5, g4, t23, k3' 23 (by decide), r23, ptr4],
      by rw [h5, g4, t8, k3' 8 (by decide), r8, ptr4], by rw [h5, e9], fun q hq => ?_⟩
    rw [h5, g4, tk q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl),
      k3 q (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl) (pkeep_ne hq rfl)]
  have hlt := L.hlt
  by_cases hl : i + 1 < N
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 o L.hBr L.hBt (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, c1.trans (c3.trans (c4.trans (.single d5))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 (o + 0x20) L.hBr (by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega)]
      show (o + 0x1E + 2) % 2 ^ 32 = o + 0x20; omega) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, c1.trans (c3.trans (c4.trans (.single d5))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩


/-- **A subtraction loop**, from limb `i` to the loop's exit at `o + 0x20`:
`D` gets the left operand minus the right one and the borrow `b0` the loop
started with, and `s8` the borrow out as a mask. -/
theorem lc_sub_loop {P F lp rp D imm jo b0 : Word} {M0 : Word → BitVec 8} {o N : Nat} (L : LcLoopAt o imm jo)
    (hN : N ≤ 12) (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hlp : lp.toNat % 4 = 0) (hrp : rp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 4 * N ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 lp (4 * N)) (sFN : Sep (F + 0xFFFFFFFC) 4 rp (4 * N))
    (sFD : Sep (F + 0xFFFFFFFC) 4 D (4 * N))
    (sDA : Sep D (4 * N) lp (4 * N)) (sDN : Sep D (4 * N) rp (4 * N))
    (sFB : Sep (F + 0xFFFFFFFC) 4 (lcBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P lincomb12Code.length)
    (sDB : Sep D (4 * N) (lcBsub P) borrowingSubCode.length) (sDC : Sep D (4 * N) P lincomb12Code.length) :
    ∀ m i, i + m + 1 = N → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n o (reg n) → CodeIn M P lincomb12Code → CodeIn M (lcBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D (4 * N) x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 lp i + 2 ^ (32 * i) * maskBit b = maskBit b0 + accV M0 rp i + accV M D i →
      reg n sp = F → reg n 22 = lp + BitVec.ofNat 32 (4 * i) → reg n 23 = rp + BitVec.ofNat 32 (4 * i) →
      reg n 8 = D + BitVec.ofNat 32 (4 * i) → reg n 9 = BitVec.ofNat 32 (N - i) → reg n 24 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (o + 0x20) (reg n') ∧ CodeIn M' P lincomb12Code ∧
        CodeIn M' (lcBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D (4 * N) x 1 → M' x = M0 x) ∧
        (reg n' 24 = 0 ∨ reg n' 24 = 0xFFFFFFFF) ∧
        accV M0 lp N + 2 ^ (32 * N) * maskBit (reg n' 24) = maskBit b0 + accV M0 rp N + accV M' D N ∧
        reg n' sp = F ∧ ∀ q, lcSubKeep q = true → reg n' q = reg n q := by
  have step : ∀ i, i < N → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n o (reg n) → CodeIn M P lincomb12Code → CodeIn M (lcBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D (4 * N) x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 lp i + 2 ^ (32 * i) * maskBit b = maskBit b0 + accV M0 rp i + accV M D i →
      reg n sp = F → reg n 22 = lp + BitVec.ofNat 32 (4 * i) → reg n 23 = rp + BitVec.ofNat 32 (4 * i) →
      reg n 8 = D + BitVec.ofNat 32 (4 * i) → reg n 9 = BitVec.ofNat 32 (N - i) → reg n 24 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < N then o else o + 0x20) (reg n') ∧
        CodeIn M' P lincomb12Code ∧ CodeIn M' (lcBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D (4 * N) x 1 → M' x = M0 x) ∧
        (reg n' 24 = 0 ∨ reg n' 24 = 0xFFFFFFFF) ∧
        accV M0 lp (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' 24) =
          maskBit b0 + accV M0 rp (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' 22 = lp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' 23 = rp + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' 8 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' 9 = BitVec.ofNat 32 (N - (i + 1)) ∧
        ∀ q, lcSubKeep q = true → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r22 r23 r8 r9 r24
    obtain ⟨n1, Mb, c1, u1, hMb, e24, esp, e22, e23, e8, e9, fr⟩ := lc_sub_iter (i := i) L s hc hb hP hi hN hF hlp
      hrp hD sFB sFC (sDC.sub (by omega)) rsp r22 r23 r8 r9 r24
    have eA : memLoad32 M (lp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (lp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFA.subR (by omega)) (sDA.subR (by omega))
    have eN : memLoad32 M (rp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (rp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    rw [eA, eN] at u1 e24
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (rp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (lcBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P lincomb12Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e24]; exact bm, ?_, esp, e22, e23, e8, e9, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (lp + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (rp + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (rp + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e24]
      have := sub_arith hv bv
      rw [← Nat.add_assoc] at this
      omega
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp r22 r23 r8 r9 r24
    have iN : i + 1 = N := by omega
    subst iN
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step i (by omega) s hc hb hfr hbm hv rsp r22 r23 r8 r9 r24
    rw [ite_eq_right (by omega)] at u1
    exact ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r22 r23 r8 r9 r24
    have hl : i + 1 < N := by omega
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e22, e23, e8, e9, fr⟩ :=
      step i (by omega) s hc hb hfr hbm hv rsp r22 r23 r8 r9 r24
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hb', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (by omega) u1 hc1 hb1 hf1 hm1 hv1 sp1 e22 e23 e8 e9 rfl
    exact ⟨n', M', c1.trans c', u', hc', hb', hf', hm', hv', sp', fun q hq => by rw [fr' q hq, fr q hq]⟩


/-- A call from `lincomb_int` to `Int<2>::abs_sign` at `P + 0xFFFFA54E`, with
`sp` at `F`. -/
theorem lc_callAbs {M : Word → BitVec 8} {P F out xp : Word} {n : Machine} {off : Nat} {imm o : Word}
    (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P lincomb12Code)
    (hab : CodeIn M (P + 0xFFFFA54E) absSign2Code)
    (h1 : fetchRel lincomb12Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel lincomb12Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFA54E) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = F) (r10 : reg n a0 = out) (r11 : reg n a1 = xp)
    (hF : F.toNat % 4 = 0) (h32 : 0x20 ≤ F.toNat) (hxp : xp.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (sFC : Sep (F + 0xFFFFFFE0) 0x20 (P + 0xFFFFA54E) absSign2Code.length)
    (sOC : Sep out 9 (P + 0xFFFFA54E) absSign2Code.length) (sXF : Sep xp 8 (F + 0xFFFFFFE0) 0x20) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 8) (reg n') ∧ reg n' sp = F ∧
      (∀ q, q.val ∉ [1, 5, 6, 11, 12, 13, 14, 15, 16, 17] → reg n' q = reg n q) ∧
      limbVal (wordsAt n'.mem out 2) =
        (if limbVal (wordsAt M xp 2) < 2 ^ 63 then limbVal (wordsAt M xp 2) else 2 ^ 64 - limbVal (wordsAt M xp 2)) ∧
      (n'.mem (out + 8)).toNat = (if limbVal (wordsAt M xp 2) < 2 ^ 63 then 0 else 1) ∧
      ∀ x, Sep (F + 0xFFFFFFE0) 0x20 x 1 → Sep out 9 x 1 → n'.mem x = M x := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb (even_at P hP 0xFFFFA54E (by decide))
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, sp2, k2, w2, b2, f2⟩ := absSign2_correct m1 (by rw [mem1]; exact hab) pc1
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), r10]) (by rw [r1 a1 (by decide), r11])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) hF h32 hxp hout sFC sOC sXF
  rw [mem1] at w2 b2 f2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, w2, b2, f2⟩
  have hr : q ≠ ra := fun e => hq (by rw [e]; decide)
  rw [k2 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)), r1 q hr]

/-- A call from `lincomb_int` to `widening_mul_fixed::<12, 2>` at `P + 0x398`,
with `sp` at `F`. -/
theorem lc_callWide {M : Word → BitVec 8} {P F out xp yp : Word} {n : Machine} {off : Nat} {imm o : Word}
    (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P lincomb12Code)
    (env : K12Env M (P + 0x398) (F + 0xFFFFFF90) out xp yp)
    (h1 : fetchRel lincomb12Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel lincomb12Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x398) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = F) (r10 : reg n a0 = out) (r11 : reg n a1 = xp) (r12 : reg n a2 = yp) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 8) (reg n') ∧ reg n' sp = F ∧
      (∀ q, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] → reg n' q = reg n q) ∧
      accV n'.mem out 14 = accV M xp 12 * accV M yp 2 ∧
      ∀ x, Sep (F + 0xFFFFFF90) 0x70 x 1 → Sep out 56 x 1 → n'.mem x = M x := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb (even_at P hP 0x398 (by decide))
  have r1 := PEnv.reg1 regs1 s.zero
  have hG : F + 0xFFFFFF90 + 0x70 = F := by rw [BitVec.add_assoc]; exact BitVec.add_zero F
  obtain ⟨m2, c2, pc2, sp2, k2, w2, f2⟩ := wideMul12x2_correct m1 (by rw [mem1]; exact env) pc1
    (by rw [r1 a0 (by decide), r10]) (by rw [r1 a1 (by decide), r11]) (by rw [r1 a2 (by decide), r12])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [r1 sp (by decide), rsp, hG])
  rw [mem1] at w2 f2
  rw [hG] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, w2, f2⟩
  have hr : q ≠ ra := fun e => hq (by rw [e]; decide)
  rw [k2 q (by simp only [feMKeep, decide_eq_true_eq]; intro h; apply hq
               simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega), r1 q hr]

/-- A call from `lincomb_int` to `conditional_negate_in_place_wide::<12, 2>`
at `P + 0x482`, with `sp` at `F`. -/
theorem lc_callNeg {M : Word → BitVec 8} {P F lo hi fl : Word} {n : Machine} {off : Nat} {imm o : Word}
    (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P lincomb12Code)
    (env : CNEnv M (P + 0x482) F lo hi)
    (h1 : fetchRel lincomb12Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel lincomb12Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x482) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = F) (r10 : reg n a0 = lo) (r11 : reg n a1 = hi) (r12 : reg n a2 = fl) (hfl : fl = 0 ∨ fl = 1) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 8) (reg n') ∧ reg n' sp = F ∧
      (∀ q, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17] → reg n' q = reg n q) ∧
      accV n'.mem lo 12 + 2 ^ 384 * accV n'.mem hi 2 =
        (if fl = 1 then (2 ^ 448 - (accV M lo 12 + 2 ^ 384 * accV M hi 2)) % 2 ^ 448
         else accV M lo 12 + 2 ^ 384 * accV M hi 2) ∧
      ∀ x, Sep (cnR F) 0xE0 x 1 → Sep lo 48 x 1 → Sep hi 8 x 1 → n'.mem x = M x := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb (even_at P hP 0x482 (by decide))
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, sp2, k2, w2, f2⟩ := condNeg12_correct m1 (by rw [mem1]; exact env) pc1
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 a0 (by decide), r10]) (by rw [r1 a1 (by decide), r11])
    (by rw [r1 a2 (by decide), r12]) hfl (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
  rw [mem1] at w2 f2
  simp only [limbVal_wordsAt] at w2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, w2, f2⟩
  have hr : q ≠ ra := fun e => hq (by rw [e]; decide)
  rw [k2 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)), r1 q hr]


/-- The function's region: its 0x100-byte frame and the 0xE0 bytes below it
that its callees use. -/
abbrev lcR (sp0 : Word) : Word := sp0 + 0xFFFFFE20

/-- The function's frame: its `sp` while it runs. -/
abbrev lcF (sp0 : Word) : Word := sp0 + 0xFFFFFF00

theorem lcR_F (sp0 : Word) : lcR sp0 + BitVec.ofNat 32 0xE0 = lcF sp0 := by
  rw [BitVec.add_assoc]; rfl

theorem lcR_al {sp0 : Word} (h : sp0.toNat % 4 = 0) : (lcR sp0).toNat % 4 = 0 :=
  aligned_add h (k := 0xFFFFFE20) (by decide)

theorem lcR_w {sp0 : Word} (h : 0x1E0 ≤ sp0.toNat) : (lcR sp0).toNat + 0x1E0 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFE20 : Word).toNat = 4294966816 := rfl
  have := sp0.isLt
  omega

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev lcPs : List (Fin 32 × Word) :=
  [(ra, 0xFC), ((8 : Fin 32), 0xF8), ((9 : Fin 32), 0xF4), ((18 : Fin 32), 0xF0), ((19 : Fin 32), 0xEC),
   ((20 : Fin 32), 0xE8), ((21 : Fin 32), 0xE4), ((22 : Fin 32), 0xE0), ((23 : Fin 32), 0xDC), ((24 : Fin 32), 0xD8)]

set_option maxRecDepth 20000 in
theorem lcPs_range : ∀ p ∈ lcPs, p.2.toNat % 4 = 0 ∧ 0xD8 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x100 := by decide

theorem lcPs_sp : ∀ p ∈ lcPs, p.1 ≠ sp := by decide

/-- From 0x16 to 0x22: keep the arguments, and `abs_sign(c)`'s arguments. -/
def lcPro : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a4, .alu .add (19 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1,
   .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0x8, .alu .add a1 x0 a3]

/-- From 0x2A to 0x32: `c`'s sign, and `abs_sign(d)`'s arguments. -/
def lcB : List BInstr := [.lbu (20 : Fin 32) sp 0x10, .aluImm .add a0 sp 0x14, .alu .add a1 x0 (8 : Fin 32)]

/-- From 0x3A to 0x48: `d`'s sign, and the arguments of `|a| * |c|`. -/
def lcC : List BInstr :=
  [.lbu (8 : Fin 32) sp 0x1C, .aluImm .add a0 sp 0x68, .aluImm .add a2 sp 0x8, .alu .add a1 x0 (9 : Fin 32),
   .aluImm .add (22 : Fin 32) sp 0x68]

/-- From 0x50 to 0x6A: keep the product's high words, `x_neg`, and the
arguments of `|b| * |d|`. -/
def lcD : List BInstr :=
  [.lw a0 sp 0x98, .lw a1 sp 0x9C, .lbu a2 (9 : Fin 32) 0x30, .sw sp a0 0x20, .sw sp a1 0x24,
   .alu .xor (20 : Fin 32) a2 (20 : Fin 32), .aluImm .add a0 sp 0x30, .aluImm .add a2 sp 0x14,
   .alu .add a1 x0 (19 : Fin 32), .aluImm .add (23 : Fin 32) sp 0x30]

/-- From 0x72 to 0x92: `y_neg`, `odd_neg`, keep the second product's high
words, and the arguments of the first conditional negation. -/
def lcE : List BInstr :=
  [.lbu a0 (19 : Fin 32) 0x30, .lw a1 sp 0x60, .lw a2 sp 0x64, .alu .xor (19 : Fin 32) a0 (8 : Fin 32),
   .alu .xor (21 : Fin 32) (19 : Fin 32) (20 : Fin 32), .aluImm .xor a0 (21 : Fin 32) 0x1, .sw sp a1 0x28,
   .sw sp a2 0x2C, .aluImm .and a2 a0 0xFF, .aluImm .add a0 sp 0x30, .aluImm .add a1 sp 0x28]

/-- From 0x9A to 0xA4: `memset`'s arguments for the low difference. -/
def lcF6 : List BInstr :=
  [.aluImm .add a0 sp 0xA8, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .aluImm .add (8 : Fin 32) sp 0xA8]

/-- From 0xAC to 0xB0: the borrow and the count of the low difference. -/
def lcG : List BInstr := [.aluImm .add (24 : Fin 32) x0 0x0, .aluImm .add (9 : Fin 32) x0 0xC]

/-- From 0xD2 to 0xDA: copy the low difference over the first product. -/
def lcH : List BInstr := [.aluImm .add a0 sp 0x68, .aluImm .add a1 sp 0xA8, .aluImm .add a2 x0 0x30]

/-- From 0xE2 to 0xF2: the high difference's buffer, pointers, and count. -/
def lcI : List BInstr :=
  [.sw sp x0 0xA0, .sw sp x0 0xA4, .aluImm .add (22 : Fin 32) sp 0x20, .aluImm .add (23 : Fin 32) sp 0x28,
   .aluImm .add (8 : Fin 32) sp 0xA0, .aluImm .add (9 : Fin 32) x0 0x2]

/-- From 0x114 to 0x134: the high difference to `F + 0x20`, the final borrow,
`swap`, and the arguments of the second conditional negation. -/
def lcJ : List BInstr :=
  [.lw a0 sp 0xA0, .lw a1 sp 0xA4, .sw sp a0 0x20, .sw sp a1 0x24, .sw sp (24 : Fin 32) 0xA0,
   .aluImm .add a0 sp 0xA0, .lw a0 sp 0xA0, .aluImm .sltu a0 a0 0x1, .aluImm .add a0 a0 0xFFFFFFFF,
   .alu .and (8 : Fin 32) (21 : Fin 32) a0, .aluImm .and (8 : Fin 32) (8 : Fin 32) 0x1, .aluImm .add a0 sp 0x68,
   .aluImm .add a1 sp 0x20, .alu .add a2 x0 (8 : Fin 32)]

/-- From 0x13C to 0x158: the high words, the sign, and the copy of the low
words to `out`. -/
def lcK : List BInstr :=
  [.lw (9 : Fin 32) sp 0x20, .lw (21 : Fin 32) sp 0x24, .aluImm .xor a0 (8 : Fin 32) 0x1,
   .alu .and a0 a0 (20 : Fin 32), .alu .and a1 (8 : Fin 32) (19 : Fin 32), .alu .or (8 : Fin 32) a0 a1,
   .aluImm .add a1 sp 0x68, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]

/-- From 0x160 to 0x16C: the high words and the sign byte to `out`. -/
def lcL : List BInstr :=
  [.sw (18 : Fin 32) (9 : Fin 32) 0x30, .sw (18 : Fin 32) (21 : Fin 32) 0x34, .sb (18 : Fin 32) (8 : Fin 32) 0x38]

section
set_option maxRecDepth 20000
theorem lcB_end : blockEnd lincomb12Code 0x2A lcB = some 0x32 := by decide
theorem lcC_end : blockEnd lincomb12Code 0x3A lcC = some 0x48 := by decide
theorem lcD_end : blockEnd lincomb12Code 0x50 lcD = some 0x6A := by decide
theorem lcE_end : blockEnd lincomb12Code 0x72 lcE = some 0x92 := by decide
theorem lcF6_end : blockEnd lincomb12Code 0x9A lcF6 = some 0xA4 := by decide
theorem lcG_end : blockEnd lincomb12Code 0xAC lcG = some 0xB0 := by decide
theorem lcH_end : blockEnd lincomb12Code 0xD2 lcH = some 0xDA := by decide
theorem lcI_end : blockEnd lincomb12Code 0xE2 lcI = some 0xF2 := by decide
theorem lcJ_end : blockEnd lincomb12Code 0x114 lcJ = some 0x134 := by decide
theorem lcK_end : blockEnd lincomb12Code 0x13C lcK = some 0x158 := by decide
theorem lcL_end : blockEnd lincomb12Code 0x160 lcL = some 0x16C := by decide
theorem lcRestore_end : blockEnd lincomb12Code 0x16C (restoreBlock lcPs) = some 0x180 := by decide
theorem lcSave_end : blockEnd lincomb12Code 2 (saveBlock lcPs) = some 0x16 := by decide
theorem lcPro_end : blockEnd lincomb12Code 0x16 lcPro = some 0x22 := by decide
end

/-- Where `SignedInt<12>::lincomb_int::<2>` runs: its code and its callees'
at their offsets, its region below `sp0`, and the arguments: `out` (57
bytes), `a` and `b` (48-byte magnitudes and a sign byte each), and `c` and
`d` (8 bytes each), aligned and apart from the region and the code. -/
structure LCEnv (M : Word → BitVec 8) (P sp0 out ap bp cp dp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P lincomb12Code
  abs : CodeIn M (P + 0xFFFFA54E) absSign2Code
  wide : CodeIn M (P + 0x398) wideMul12x2Code
  neg : CodeIn M (P + 0x482) condNeg12Code
  mset : CodeIn M (P + 0x18A8) memsetCode
  stub : CodeIn M (P + 0x1910) memcpyStubCode
  body : CodeIn M (P + 0x1918) memcpyBodyCode
  bsub : CodeIn M (lcBsub P) borrowingSubCode
  sel2 : CodeIn M (P + 0x592) uintSelect2Code
  sel12 : CodeIn M (P + 0xFFFFFF2A) uintSelect12Code
  zero : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  hsp : sp0.toNat % 4 = 0
  hS : 0x1E0 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hcp : cp.toNat % 4 = 0
  hdp : dp.toNat % 4 = 0
  hwo : out.toNat + 57 < 2 ^ 32
  hwa : ap.toNat + 49 < 2 ^ 32
  hwb : bp.toNat + 49 < 2 ^ 32
  sC : Sep (lcR sp0) 0x1E0 P lincomb12Code.length
  sA : Sep (lcR sp0) 0x1E0 (P + 0xFFFFA54E) absSign2Code.length
  sW : Sep (lcR sp0) 0x1E0 (P + 0x398) wideMul12x2Code.length
  sN : Sep (lcR sp0) 0x1E0 (P + 0x482) condNeg12Code.length
  sM : Sep (lcR sp0) 0x1E0 (P + 0x18A8) memsetCode.length
  sU : Sep (lcR sp0) 0x1E0 (P + 0x1910) memcpyStubCode.length
  sB : Sep (lcR sp0) 0x1E0 (P + 0x1918) memcpyBodyCode.length
  sBs : Sep (lcR sp0) 0x1E0 (lcBsub P) borrowingSubCode.length
  s2 : Sep (lcR sp0) 0x1E0 (P + 0x592) uintSelect2Code.length
  s12 : Sep (lcR sp0) 0x1E0 (P + 0xFFFFFF2A) uintSelect12Code.length
  sZ : Sep (lcR sp0) 0x1E0 (BitVec.ofNat 32 u2ZeroAddress) 8
  sO : Sep (lcR sp0) 0x1E0 (BitVec.ofNat 32 u2OneAddress) 8
  oR : Sep out 57 (lcR sp0) 0x1E0
  aR : Sep ap 49 (lcR sp0) 0x1E0
  bR : Sep bp 49 (lcR sp0) 0x1E0
  cR : Sep cp 8 (lcR sp0) 0x1E0
  dR : Sep dp 8 (lcR sp0) 0x1E0
  oC : Sep out 57 P lincomb12Code.length
  oB : Sep out 57 (P + 0x1918) memcpyBodyCode.length

theorem lc_in {sp0 b : Word} {c l k : Nat} (h : c + l ≤ 0x1E0) (hx : Sep (lcR sp0) 0x1E0 b k) :
    Sep (lcR sp0 + BitVec.ofNat 32 c) l b k := hx.sub h

theorem lcF_in {sp0 b : Word} {c l k : Nat} (h : c + l ≤ 0x100) (hx : Sep (lcR sp0) 0x1E0 b k) :
    Sep (lcF sp0 + BitVec.ofNat 32 c) l b k := by
  rw [← lcR_F, add_ofNat_assoc]; exact hx.sub (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The prologue, from entry to the first call of `abs_sign` at 0x22: save
the registers and keep the arguments. -/
theorem lc_pro (m : Machine) {P sp0 out ap bp cp dp : Word} (env : LCEnv m.mem P sp0 out ap bp cp dp)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) (ha3 : reg m a3 = cp) (ha4 : reg m a4 = dp) :
    ∃ n M, Steps m n ∧ St M P n 0x22 (reg n) ∧
      (∀ x, Sep (lcF sp0) 0x100 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ lcPs → memLoad32 M (lcF sp0 + o) = reg m r) ∧
      reg n sp = lcF sp0 ∧ reg n 8 = dp ∧ reg n 19 = bp ∧ reg n 9 = ap ∧ reg n 18 = out ∧
      reg n a0 = lcF sp0 + BitVec.ofNat 32 8 ∧ reg n a1 = cp ∧
      ∀ q, q.val ∉ [1, 2, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 24] → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hRw := lcR_w env.hS
  have hFa : (lcF sp0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF00) (by decide)
  have sFC : Sep (lcF sp0) 0x100 P lincomb12Code.length := by
    have := lcF_in (c := 0) (l := 0x100) (by decide) env.sC; rwa [add_ofNat_zero] at this
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code lc12_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF00) sp = lcF sp0 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock lcPs) u1 env.code lcSave_end (saveBlock_ok _ lcPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (lcPs_range p hp).1, frm_sep' sFC (by have := lcPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem (lcF sp0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF00)) lcPs = Msv := ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (lcF sp0) 0x100 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside lcPs fun p hp => frm_sep' hx (by have := lcPs_range p hp; omega)
  have hcv : CodeIn Msv P lincomb12Code := fun i hi => by
    rw [frSv _ (sFC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  obtain ⟨m3, c3, u3⟩ := St.block lcPro u2.self hcv lcPro_end (by simp [BlockOk, BInstr.ok, lcPro])
  simp only [runBlock, BInstr.run, lcPro] at u3
  have r2 : ∀ q, reg m2 q = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF00) q := u2.regs
  have g3 : ∀ q, reg m3 q = _ := u3.regs
  refine ⟨m3, Msv, .cons d1 (c2.trans c3), u3.self, frSv, fun r o h => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun q hq => ?_⟩
  · rw [← hMsv]
    simp only [lcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  rotate_right
  · have nq : ∀ r : Fin 32, r.val ∈ [1, 2, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 24] → q ≠ r :=
      fun r hr e => hq (e ▸ hr)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u3.self.zero, hz]
    rw [g3]
    simp only [upd_app, h0, nq a1 (by decide), nq a0 (by decide), nq 18 (by decide), nq 9 (by decide),
      nq 19 (by decide), nq 8 (by decide), ite_false]
    rw [r2]; simp only [upd_app, h0, nq sp (by decide), ite_false]
  all_goals first
    | (rw [g3]; simp +decide only [upd_app, ↓reduceIte, r2, ev_add, zw]; done)
    | (rw [g3]; simp +decide only [upd_app, ↓reduceIte, r2, ev_add, zw, hsp, ha0, ha1, ha2, ha3, ha4, hz]; done)
    | (rw [g3]; simp +decide only [upd_app, ↓reduceIte, r2, ev_add, zw, hsp, ha0, ha1, ha2, ha3, ha4, hz]; rfl)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The epilogue, from 0x16C: restore the saved registers and `sp`, and
return. -/
theorem lc_epi {M : Word → BitVec 8} {P F : Word} {v : Fin 32 → Word} {n : Machine}
    (st : St M P n 0x16C (reg n)) (hc : CodeIn M P lincomb12Code) (hFa : F.toNat % 4 = 0) (rsp : reg n sp = F)
    (hsl : ∀ r o, (r, o) ∈ lcPs → memLoad32 M (F + o) = v r) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧ reg n' sp = F + 0x100 ∧ n'.mem = M ∧
      (∀ r o, (r, o) ∈ lcPs → reg n' r = v r) ∧
      ∀ q, q.val ∉ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24] → q ≠ sp → reg n' q = reg n q := by
  obtain ⟨n4, c4, u4⟩ := St.block (restoreBlock lcPs) st hc lcRestore_end
    (restoreBlock_ok M _ lcPs (reg n) rsp lcPs_sp fun p hp => fr_al' hFa (lcPs_range p hp).1)
  simp only [restoreBlock_run M _ lcPs (reg n) rsp lcPs_sp] at u4
  have rsp4 : restoreRegs M F (reg n) lcPs sp = F := by rw [restoreRegs_sp _ _ _ _ lcPs_sp]; exact rsp
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc lc12_at_180 (off' := 0x182) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc lc12_at_182
  refine ⟨n6, c4.trans (.cons d5 (.single d6)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, hsl ra 0xFC (by decide)]
  · rw [regs6]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp4]; try rfl
  · exact mem6
  · intro r o h
    rw [regs6]
    simp only [lcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hsl _ _ (by decide)
  · intro q hq hs
    have ne : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24] → q ≠ w := fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n6 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    rw [regs6]
    simp only [upd_app, h0, hs, ite_false]
    simp only [restoreRegs]
    simp only [upd_app, h0, ne ra (by decide), ne 8 (by decide), ne 9 (by decide), ne 18 (by decide),
      ne 19 (by decide), ne 20 (by decide), ne 21 (by decide), ne 22 (by decide), ne 23 (by decide),
      ne 24 (by decide), ite_false]

/-- A 64-bit two's complement value. -/
def i64Val (c : Nat) : Int := if c < 2 ^ 63 then (c : Int) else (c : Int) - 2 ^ 64

/-- A magnitude with a sign byte: negative when the byte is 1. -/
def sgnVal (s v : Nat) : Int := if s = 1 then -(v : Int) else (v : Int)

/-- **The sign logic**: subtracting `y`, negated when the signs agree, from
`x`, and negating the difference when it borrowed and the signs differ,
gives `±x ± y`. -/
theorem lc_math {x y Rraw b2 xn yn : Nat} (hx : x < 2 ^ 447) (hy : y < 2 ^ 447) (hxn : xn ≤ 1) (hyn : yn ≤ 1)
    (hR : Rraw < 2 ^ 448) (hb : b2 ≤ 1)
    (hloop : x + 2 ^ 448 * b2 = (if xn = yn then (2 ^ 448 - y) % 2 ^ 448 else y) + Rraw) :
    sgnVal (if xn ≠ yn ∧ b2 = 1 then yn else xn) (if xn ≠ yn ∧ b2 = 1 then (2 ^ 448 - Rraw) % 2 ^ 448 else Rraw) =
      sgnVal xn x + sgnVal yn y := by
  unfold sgnVal
  rcases (by omega : xn = 0 ∨ xn = 1) with rfl | rfl <;> rcases (by omega : yn = 0 ∨ yn = 1) with rfl | rfl <;>
    rcases (by omega : b2 = 0 ∨ b2 = 1) with rfl | rfl <;> simp +decide only [↓reduceIte] at hloop ⊢ <;> omega

/-- A product of a signed magnitude and `abs_sign`'s output. -/
theorem lc_sgn {A C sa : Nat} (hsa : sa ≤ 1) (hC : C < 2 ^ 64) :
    sgnVal ((sa + (if C < 2 ^ 63 then 0 else 1)) % 2) (A * (if C < 2 ^ 63 then C else 2 ^ 64 - C)) =
      sgnVal sa A * i64Val C := by
  unfold sgnVal i64Val
  by_cases h : C < 2 ^ 63
  · simp only [h, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt (show sa < 2 by omega)]
    split <;> push_cast <;> simp [Int.neg_mul]
  · simp only [h, ↓reduceIte]
    have e : ((2 ^ 64 - C : Nat) : Int) = 2 ^ 64 - (C : Int) := by omega
    rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl
    · simp +decide only [↓reduceIte]; push_cast; rw [e, Int.mul_sub, Int.mul_sub]; omega
    · simp +decide only [↓reduceIte]; push_cast; rw [e, Int.neg_mul, Int.mul_sub, Int.mul_sub]; omega

theorem lcF_m20 (sp0 : Word) : lcF sp0 + 0xFFFFFFE0 = lcR sp0 + BitVec.ofNat 32 0xC0 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1

theorem lcF_m70 (sp0 : Word) : lcF sp0 + 0xFFFFFF90 = lcR sp0 + BitVec.ofNat 32 0x70 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1

theorem lcF_m4 (sp0 : Word) : lcF sp0 + 0xFFFFFFFC = lcR sp0 + BitVec.ofNat 32 0xDC := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1

theorem lcF_cnR (sp0 : Word) : cnR (lcF sp0) = lcR sp0 := by
  show sp0 + 0xFFFFFF00 + 0xFFFFFF20 = sp0 + 0xFFFFFE20
  rw [BitVec.add_assoc]; rfl

theorem lcF_ofs (sp0 : Word) (c : Nat) : lcF sp0 + BitVec.ofNat 32 c = lcR sp0 + BitVec.ofNat 32 (0xE0 + c) := by
  rw [← lcR_F, add_ofNat_assoc]

theorem xor01 {a b : Word} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    aluEval .xor a b = 0 ∨ aluEval .xor a b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem flag01 {a : Word} (ha : a = 0 ∨ a = 1) :
    (aluEval .and (aluEval .xor a 1) 0xFF = 0 ∨ aluEval .and (aluEval .xor a 1) 0xFF = 1) ∧
    (aluEval .and (aluEval .xor a 1) 0xFF = 1 ↔ a = 0) := by
  rcases ha with rfl | rfl <;> decide

theorem swap01 {on b : Word} (ho : on = 0 ∨ on = 1) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    aluEval .and (aluEval .and on (aluEval .add (aluEval .sltu b 1) 0xFFFFFFFF)) 1 =
      if on = 1 ∧ b = 0xFFFFFFFF then 1 else 0 := by
  rcases ho with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem signw {sw xn yn : Word} (hs : sw = 0 ∨ sw = 1) (hx : xn = 0 ∨ xn = 1) (hy : yn = 0 ∨ yn = 1) :
    aluEval .or (aluEval .and (aluEval .xor sw 1) xn) (aluEval .and sw yn) = if sw = 1 then yn else xn := by
  rcases hs with rfl | rfl <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem lc_pt {F : Word} {M M' : Word → BitVec 8} {c : Nat} (n : Nat)
    (h : ∀ t, t < 4 * n → M (F + BitVec.ofNat 32 (c + t)) = M' (F + BitVec.ofNat 32 (c + t))) :
    accV M (F + BitVec.ofNat 32 c) n = accV M' (F + BitVec.ofNat 32 c) n :=
  (accV_congr n fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc, add_ofNat_assoc]; exact (h _ (by omega)).symm).symm

theorem xor_bits {a b : BitVec 8} (ha : a.toNat ≤ 1) (hb : b.toNat ≤ 1) :
    (aluEval .xor (a.zeroExtend 32) (b.zeroExtend 32)).toNat = (a.toNat + b.toNat) % 2 := by
  have ea : a = 0 ∨ a = 1 := by
    rcases (by omega : a.toNat = 0 ∨ a.toNat = 1) with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  have eb : b = 0 ∨ b = 1 := by
    rcases (by omega : b.toNat = 0 ∨ b.toNat = 1) with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  rcases ea with rfl | rfl <;> rcases eb with rfl | rfl <;> decide

theorem lc_addc {P : Word} {a b c : Nat} (h : a + b = c) :
    P + BitVec.ofNat 32 a + BitVec.ofNat 32 b = P + BitVec.ofNat 32 c := by
  rw [add_ofNat_assoc, h]

/-- The environment `widening_mul_fixed::<12, 2>` needs, called with `sp` at
the frame, the product at `F + oc`, `xp` an argument, and `yp` at `F + yc`. -/
theorem lc_k12 {M : Word → BitVec 8} {P sp0 out ap bp cp dp : Word} (env : LCEnv M P sp0 out ap bp cp dp)
    {M' : Word → BitVec 8} (hM : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M' x = M x) {xp : Word} {oc yc : Nat}
    (hxp : xp.toNat % 4 = 0) (sX : Sep xp 48 (lcR sp0) 0x1E0) (ho : oc + 56 ≤ 0x100) (hy : yc + 8 ≤ 0x100)
    (hoa : oc % 4 = 0) (hya : yc % 4 = 0) :
    K12Env M' (P + 0x398) (lcF sp0 + 0xFFFFFF90) (lcF sp0 + BitVec.ofNat 32 oc) xp
      (lcF sp0 + BitVec.ofNat 32 yc) := by
  have hRw := lcR_w env.hS
  have hFa : (lcF sp0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF00) (by decide)
  have hFv : (lcF sp0).toNat = (lcR sp0).toNat + 0xE0 := by
    rw [← lcR_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have cIn : ∀ {b : Word} {code : List Nat}, CodeIn M b code → Sep (lcR sp0) 0x1E0 b code.length →
      CodeIn M' b code := fun hc hs i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have e : ∀ c, P + 0x398 + BitVec.ofNat 32 c = P + BitVec.ofNat 32 (0x398 + c) := fun c => lc_addc rfl
  rw [lcF_m70, lcF_ofs, lcF_ofs]
  exact {
    hP := even_at P env.hP 0x398 (by decide)
    code := cIn env.wide env.sW
    ms := by rw [show (0x1510 : Word) = BitVec.ofNat 32 0x1510 from rfl, e]; exact cIn env.mset env.sM
    mcS := by rw [show (0x1578 : Word) = BitVec.ofNat 32 0x1578 from rfl, e]; exact cIn env.stub env.sU
    mcB := by rw [show (0x1580 : Word) = BitVec.ofNat 32 0x1580 from rfl, e]; exact cIn env.body env.sB
    hG := aligned_add (lcR_al env.hsp) (by decide)
    hGt := by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega
    hx := hxp
    hy := aligned_add (lcR_al env.hsp) (by omega)
    hout := aligned_add (lcR_al env.hsp) (by omega)
    hot := by rw [BitVec.toNat_add, ofNat_tn (by omega)]; omega
    sGC := env.sW.sub (by decide)
    sGM := by rw [show (0x1510 : Word) = BitVec.ofNat 32 0x1510 from rfl, e]; exact env.sM.sub (by decide)
    sGS := by rw [show (0x1578 : Word) = BitVec.ofNat 32 0x1578 from rfl, e]; exact env.sU.sub (by decide)
    sGB := by rw [show (0x1580 : Word) = BitVec.ofNat 32 0x1580 from rfl, e]; exact env.sB.sub (by decide)
    sOC := env.sW.sub (by omega)
    sOB := by rw [show (0x1580 : Word) = BitVec.ofNat 32 0x1580 from rfl, e]; exact env.sB.sub (by omega)
    sOG := sep_offsets _ (.inr (by omega)) (by omega) (by omega)
    sXG := sX.subR (by decide)
    sYG := sep_offsets _ (.inr (by omega)) (by omega) (by omega) }

/-- The environment `conditional_negate_in_place_wide::<12, 2>` needs, called
with `sp` at the frame, `lo` at `F + lc`, and `hi` at `F + hc`. -/
theorem lc_cn {M : Word → BitVec 8} {P sp0 out ap bp cp dp : Word} (env : LCEnv M P sp0 out ap bp cp dp)
    {M' : Word → BitVec 8} (hM : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M' x = M x) {lc hc : Nat}
    (hl : lc + 48 ≤ 0x100) (hh : hc + 8 ≤ 0x100) (hla : lc % 4 = 0) (hha : hc % 4 = 0)
    (hlh : lc + 48 ≤ hc ∨ hc + 8 ≤ lc) :
    CNEnv M' (P + 0x482) (lcF sp0) (lcF sp0 + BitVec.ofNat 32 lc) (lcF sp0 + BitVec.ofNat 32 hc) := by
  have hRw := lcR_w env.hS
  have hFv : (lcF sp0).toNat = (lcR sp0).toNat + 0xE0 := by
    rw [← lcR_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have cIn : ∀ {b : Word} {code : List Nat}, CodeIn M b code → Sep (lcR sp0) 0x1E0 b code.length →
      CodeIn M' b code := fun hc hs i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have cIn' : ∀ {b : Word} {d : List Nat} {k : Nat}, CodeIn M b d → Sep (lcR sp0) 0x1E0 b k → d.length ≤ k →
      CodeIn M' b d := fun hc hs hk i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have e : ∀ c, P + 0x482 + BitVec.ofNat 32 c = P + BitVec.ofNat 32 (0x482 + c) := fun c => lc_addc rfl
  have e2 : P + 0x482 + 0xFFFFFAA8 = P + 0xFFFFFF2A := by rw [BitVec.add_assoc]; rfl
  have zl : u2ZeroData.length = 8 := by decide
  have ol : u2OneData.length = 8 := by decide
  have hR : cnR (lcF sp0) = lcR sp0 := lcF_cnR sp0
  rw [lcF_ofs, lcF_ofs]
  exact {
    hP := even_at P env.hP 0x482 (by decide)
    code := cIn env.neg env.sN
    mset := by rw [show (0x1426 : Word) = BitVec.ofNat 32 0x1426 from rfl, e]; exact cIn env.mset env.sM
    stub := by rw [show (0x148E : Word) = BitVec.ofNat 32 0x148E from rfl, e]; exact cIn env.stub env.sU
    body := by rw [show (0x1496 : Word) = BitVec.ofNat 32 0x1496 from rfl, e]; exact cIn env.body env.sB
    sel2 := by rw [show (0x110 : Word) = BitVec.ofNat 32 0x110 from rfl, e]; exact cIn env.sel2 env.s2
    sel12 := by rw [e2]; exact cIn env.sel12 env.s12
    zero := cIn' env.zero env.sZ (by rw [zl]; exact Nat.le_refl _)
    one := cIn' env.one env.sO (by rw [ol]; exact Nat.le_refl _)
    hsp := aligned_add env.hsp (k := 0xFFFFFF00) (by decide)
    hS := by omega
    hlo := aligned_add (lcR_al env.hsp) (by omega)
    hhi := aligned_add (lcR_al env.hsp) (by omega)
    hwl := by rw [BitVec.toNat_add, ofNat_tn (by omega)]; omega
    hwh := by rw [BitVec.toNat_add, ofNat_tn (by omega)]; omega
    sRC := by rw [hR]; exact env.sN.sub (c := 0) (l := 0xE0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    sRM := by rw [hR, show (0x1426 : Word) = BitVec.ofNat 32 0x1426 from rfl, e]
              exact env.sM.sub (c := 0) (l := 0xE0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    sRU := by rw [hR, show (0x148E : Word) = BitVec.ofNat 32 0x148E from rfl, e]
              exact env.sU.sub (c := 0) (l := 0xE0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    sRB := by rw [hR, show (0x1496 : Word) = BitVec.ofNat 32 0x1496 from rfl, e]
              exact env.sB.sub (c := 0) (l := 0xE0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    sR2 := by rw [hR, show (0x110 : Word) = BitVec.ofNat 32 0x110 from rfl, e]
              exact env.s2.sub (c := 0) (l := 0xE0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    sRL := by rw [hR, e2]; exact env.s12.sub (c := 0) (l := 0xE0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    sRZ := by rw [hR]; exact env.sZ.sub (c := 0) (l := 0xE0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    sRO := by rw [hR]; exact env.sO.sub (c := 0) (l := 0xE0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h
    sLR := by
      rw [hR]; have := sep_offsets (lcR sp0) (c := 0xE0 + lc) (n := 48) (d := 0) (k := 0xE0) (.inr (by omega))
        (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    sHR := by
      rw [hR]; have := sep_offsets (lcR sp0) (c := 0xE0 + hc) (n := 8) (d := 0) (k := 0xE0) (.inr (by omega))
        (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    sLH := sep_offsets _ (by omega) (by omega) (by omega)
    sLC := env.sN.sub (by omega)
    sLB := by rw [show (0x1496 : Word) = BitVec.ofNat 32 0x1496 from rfl, e]; exact env.sB.sub (by omega)
    sL2 := by rw [show (0x110 : Word) = BitVec.ofNat 32 0x110 from rfl, e]; exact env.s2.sub (by omega)
    sHC := env.sN.sub (by omega) }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
set_option exponentiation.threshold 600 in
/-- **The compiled `SignedInt<12>::lincomb_int::<2>`**, called with `out`,
`a`, `b`, `c`, and `d`, where `a` and `b` have sign bytes 0 or 1. It returns
with `out` holding `a * c + b * d` as a 448-bit magnitude and a sign byte,
the callee-saved registers and `sp` restored, and memory changed only in
its region and `out`. -/
theorem lincomb12_correct (m : Machine) {P sp0 out ap bp cp dp retAddr : Word}
    (env : LCEnv m.mem P sp0 out ap bp cp dp) (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp) (ha3 : reg m a3 = cp) (ha4 : reg m a4 = dp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsa : (m.mem (ap + 0x30)).toNat ≤ 1) (hsb : (m.mem (bp + 0x30)).toNat ≤ 1) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] → reg m' q = reg m q) ∧
      (m'.mem (out + 0x38)).toNat ≤ 1 ∧
      sgnVal (m'.mem (out + 0x38)).toNat (accV m'.mem out 12 + 2 ^ 384 * accV m'.mem (out + 0x30) 2) =
        sgnVal (m.mem (ap + 0x30)).toNat (accV m.mem ap 12) * i64Val (accV m.mem cp 2) +
        sgnVal (m.mem (bp + 0x30)).toNat (accV m.mem bp 12) * i64Val (accV m.mem dp 2) ∧
      ∀ x, Sep (lcR sp0) 0x1E0 x 1 → Sep out 57 x 1 → m'.mem x = m.mem x := by
  have hRw := lcR_w env.hS
  have hFa : (lcF sp0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF00) (by decide)
  have hFv : (lcF sp0).toNat = (lcR sp0).toNat + 0xE0 := by
    rw [← lcR_F, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (lcR sp0) 0x1E0 b code.length → (∀ x, Sep (lcR sp0) 0x1E0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inF : ∀ {x : Word} {c l : Nat}, c + l ≤ 0x100 → Sep (lcR sp0) 0x1E0 x 1 →
      Sep (lcF sp0 + BitVec.ofNat 32 c) l x 1 := fun h hx => by
    rw [lcF_ofs]; exact hx.sub (by omega)
  have inR : ∀ {x : Word} {c l : Nat}, c + l ≤ 0x1E0 → Sep (lcR sp0) 0x1E0 x 1 →
      Sep (lcR sp0 + BitVec.ofNat 32 c) l x 1 := fun h hx => hx.sub h
  have fsep : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x100 → d + k ≤ 0x100 →
      Sep (lcF sp0 + BitVec.ofNat 32 c) n (lcF sp0 + BitVec.ofNat 32 d) k := fun h hc hd =>
    sep_offsets _ h (by omega) (by omega)
  have rsep : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x1E0 → d + k ≤ 0x1E0 →
      Sep (lcR sp0 + BitVec.ofNat 32 c) n (lcR sp0 + BitVec.ofNat 32 d) k := fun h hc hd =>
    sep_offsets _ h (by omega) (by omega)
  have aR48 : Sep ap 48 (lcR sp0) 0x1E0 := by
    have := env.aR.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
  have bR48 : Sep bp 48 (lcR sp0) 0x1E0 := by
    have := env.bR.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
  have fF : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → Sep (lcF sp0) 0x100 x 1 := fun x hx => by
    have := inF (c := 0) (l := 0x100) (by decide) hx; rwa [add_ofNat_zero] at this
  have zb : ∀ b : BitVec 8, b.toNat ≤ 1 → b.zeroExtend 32 = 0 ∨ b.zeroExtend 32 = 1 := fun b h => by
    rcases (by omega : b.toNat = 0 ∨ b.toNat = 1) with h | h
    · left; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, h]; rfl
    · right; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, h]; rfl
  -- the prologue
  obtain ⟨n0, M0, c0, s0, fr0, hsl0, sp0', r8_0, r19_0, r9_0, r18_0, ra0_0, ra1_0, k0⟩ :=
    lc_pro m env hpc hsp ha0 ha1 ha2 ha3 ha4
  have frR0 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M0 x = m.mem x := fun x hx => fr0 x (by
    have := inF (c := 0) (l := 0x100) (by decide) hx; rwa [add_ofNat_zero] at this)
  -- `abs_sign(c)` into `F + 8`
  obtain ⟨n1, c1, s1, sp1, k1, v1, b1, f1⟩ := lc_callAbs env.hP s0 (cIn env.code env.sC frR0)
    (cIn env.abs env.sA frR0) lc12_at_22 lc12_at_26 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P env.hP (0x22 + 8) (by decide)) sp0' ra0_0 ra1_0 hFa (by omega) env.hcp (aligned_add hFa (by decide))
    (by rw [lcF_m20]; exact env.sA.sub (by decide))
    (by rw [lcF_ofs]; exact env.sA.sub (by decide)) (by rw [lcF_m20]; exact env.cR.subR (by decide))
  have frR1 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → n1.mem x = m.mem x := fun x hx => by
    rw [f1 x (by rw [lcF_m20]; exact inR (by decide) hx) (inF (by decide) hx), frR0 x hx]
  -- `abs_sign(d)` into `F + 0x14`
  obtain ⟨n2, c2, s2⟩ := St.block lcB s1 (cIn env.code env.sC frR1) lcB_end (by simp [BlockOk, BInstr.ok, lcB])
  simp only [runBlock, BInstr.run, lcB] at s2
  have g2 : ∀ q, reg n2 q = _ := s2.regs
  have k01 : ∀ q : Fin 32, q.val ∉ [1, 2, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] →
      reg n1 q = reg m q := fun q hq => by
    rw [k1 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)),
      k0 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega))]
  have sp2 : reg n2 sp = lcF sp0 := by rw [g2]; simp +decide only [upd_app, ↓reduceIte]; exact sp1
  have r8_1 : reg n1 8 = dp := by rw [k1 8 (by decide), r8_0]
  obtain ⟨n3, c3, s3, sp3, k3, v3, b3, f3⟩ := lc_callAbs env.hP s2.self (cIn env.code env.sC frR1) (cIn env.abs env.sA frR1)
    lc12_at_32 lc12_at_36 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P env.hP (0x32 + 8) (by decide)) sp2 (by rw [g2]; simp +decide only [upd_app, ↓reduceIte]; rw [sp1]; rfl)
    (by rw [g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r8_1]; exact zw _) hFa (by omega) env.hdp
    (aligned_add hFa (by decide)) (by rw [lcF_m20]; exact env.sA.sub (by decide))
    (by rw [lcF_ofs]; exact env.sA.sub (by decide)) (by rw [lcF_m20]; exact env.dR.subR (by decide))
  have frR3 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → n3.mem x = m.mem x := fun x hx => by
    rw [f3 x (by rw [lcF_m20]; exact inR (by decide) hx) (inF (by decide) hx), frR1 x hx]
  -- `|a| * |c|` into `F + 0x68`
  obtain ⟨n4, c4, s4⟩ := St.block lcC s3 (cIn env.code env.sC frR3) lcC_end (by simp [BlockOk, BInstr.ok, lcC])
  simp only [runBlock, BInstr.run, lcC] at s4
  have g4 : ∀ q, reg n4 q = _ := s4.regs
  have r9_3 : reg n3 9 = ap := by
    rw [k3 9 (by decide), g2]; simp +decide only [upd_app, ↓reduceIte]; rw [k1 9 (by decide), r9_0]
  have sp4 : reg n4 sp = lcF sp0 := by rw [g4]; simp +decide only [upd_app, ↓reduceIte]; exact sp3
  obtain ⟨n5, c5, s5, sp5, k5, v5, f5⟩ := lc_callWide env.hP s4.self (cIn env.code env.sC frR3)
    (lc_k12 env frR3 (oc := 0x68) (yc := 8) env.hap aR48 (by decide) (by decide) (by decide)
      (by decide))
    lc12_at_48 lc12_at_4c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x48 + 8) (by decide))
    sp4 (by rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [r9_3]; exact zw _)
    (by rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [sp3]; rfl)
  have frR5 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → n5.mem x = m.mem x := fun x hx => by
    rw [f5 x (by rw [lcF_m70]; exact inR (by decide) hx) (inF (by decide) hx), frR3 x hx]
  -- keep `x_hi`, `x_neg`, and `|b| * |d|` into `F + 0x30`
  have k45 : ∀ q : Fin 32, q.val ∉ [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 22, 28, 29, 30, 31] →
      reg n5 q = reg n3 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 22, 28, 29, 30, 31] → q ≠ r :=
      fun r hr e => hq (e ▸ hr)
    rw [k5 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)), g4]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s3.zero.symm
    simp only [upd_app, h0, nq 22 (by decide), nq a1 (by decide), nq a2 (by decide), nq a0 (by decide),
      nq 8 (by decide), ite_false]
  have r9_5 : reg n5 9 = ap := by rw [k45 9 (by decide), r9_3]
  have r19_5 : reg n5 19 = bp := by
    rw [k45 19 (by decide), k3 19 (by decide), g2]; simp +decide only [upd_app, ↓reduceIte]
    rw [k1 19 (by decide), r19_0]
  obtain ⟨n6, c6, s6⟩ := St.block lcD s5 (cIn env.code env.sC frR5) lcD_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lcD, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp5]
    exact ⟨aligned_add hFa (by decide), aligned_add hFa (by decide), ⟨aligned_add hFa (by decide),
      lcF_in (by decide) env.sC⟩, aligned_add hFa (by decide), lcF_in (by decide) env.sC⟩)
  simp only [runBlock, BInstr.run, lcD] at s6
  have g6 : ∀ q, reg n6 q = _ := s6.regs
  simp +decide only [upd_app, ↓reduceIte, sp5, r9_5] at s6
  obtain ⟨M6, hM6⟩ : ∃ M6, memStore32 (memStore32 n5.mem (lcF sp0 + 32) (memLoad32 n5.mem (lcF sp0 + 152)))
      (lcF sp0 + 36) (memLoad32 n5.mem (lcF sp0 + 156)) = M6 := ⟨_, rfl⟩
  rw [hM6] at s6
  have frR6 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M6 x = m.mem x := fun x hx => by
    rw [← hM6, memStore32_get_sep (frm_sep' (fF x hx) (c := 36) (by decide)),
      memStore32_get_sep (frm_sep' (fF x hx) (c := 32) (by decide)), frR5 x hx]
  have sp6 : reg n6 sp = lcF sp0 := by rw [g6]; simp +decide only [upd_app, ↓reduceIte]; exact sp5
  obtain ⟨n7, c7, s7, sp7, k7, v7, f7⟩ := lc_callWide env.hP s6.self (cIn env.code env.sC frR6)
    (lc_k12 env frR6 (oc := 0x30) (yc := 0x14) env.hbp bR48 (by decide) (by decide) (by decide) (by decide))
    lc12_at_6a lc12_at_6e (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x6A + 8) (by decide))
    sp6 (by rw [g6]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [g6]; simp +decide only [upd_app, ↓reduceIte]; rw [r19_5]; exact zw _)
    (by rw [g6]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]; rfl)
  have frR7 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → n7.mem x = m.mem x := fun x hx => by
    rw [f7 x (by rw [lcF_m70]; exact inR (by decide) hx) (inF (by decide) hx), frR6 x hx]
  have k67 : ∀ q : Fin 32, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 20, 23, 28, 29, 30, 31] →
      reg n7 q = reg n5 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 20, 23, 28, 29, 30, 31] → q ≠ r :=
      fun r hr e => hq (e ▸ hr)
    rw [k7 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)), g6]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s5.zero.symm
    simp only [upd_app, h0, nq 23 (by decide), nq a1 (by decide), nq a2 (by decide), nq a0 (by decide),
      nq 20 (by decide), ite_false]
  -- `y_neg`, `odd_neg`, keep `y_hi`, and negate `y` unless the signs differ
  have sp7' : reg n7 sp = lcF sp0 := sp7
  have r19_7 : reg n7 19 = bp := by rw [k67 19 (by decide), r19_5]
  obtain ⟨n8, c8, s8⟩ := St.block lcE s7 (cIn env.code env.sC frR7) lcE_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lcE, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp7]
    exact ⟨aligned_add hFa (by decide), aligned_add hFa (by decide), ⟨aligned_add hFa (by decide),
      lcF_in (by decide) env.sC⟩, aligned_add hFa (by decide), lcF_in (by decide) env.sC⟩)
  simp only [runBlock, BInstr.run, lcE] at s8
  have g8 : ∀ q, reg n8 q = _ := s8.regs
  simp +decide only [upd_app, ↓reduceIte, sp7, r19_7] at s8
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 (memStore32 n7.mem (lcF sp0 + 40) (memLoad32 n7.mem (lcF sp0 + 96)))
      (lcF sp0 + 44) (memLoad32 n7.mem (lcF sp0 + 100)) = M8 := ⟨_, rfl⟩
  rw [hM8] at s8
  have frR8 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M8 x = m.mem x := fun x hx => by
    rw [← hM8, memStore32_get_sep (frm_sep' (fF x hx) (c := 44) (by decide)),
      memStore32_get_sep (frm_sep' (fF x hx) (c := 40) (by decide)), frR7 x hx]
  -- the sign bits
  have e16 : lcF sp0 + BitVec.ofNat 32 8 + 8 = lcF sp0 + 16 := by rw [BitVec.add_assoc]; rfl
  have e28 : lcF sp0 + BitVec.ofNat 32 0x14 + 8 = lcF sp0 + 28 := by rw [BitVec.add_assoc]; rfl
  rw [e16] at b1
  rw [e28] at b3
  have hcs : (n1.mem (lcF sp0 + 16)).zeroExtend 32 = 0 ∨ (n1.mem (lcF sp0 + 16)).zeroExtend 32 = 1 :=
    zb _ (by rw [b1]; split <;> decide)
  have hds : (n3.mem (lcF sp0 + 28)).zeroExtend 32 = 0 ∨ (n3.mem (lcF sp0 + 28)).zeroExtend 32 = 1 :=
    zb _ (by rw [b3]; split <;> decide)
  have e48 : (48 : Word) = BitVec.ofNat 32 48 := rfl
  have ea : n5.mem (ap + 48) = m.mem (ap + 48) := by
    rw [e48]; exact frR5 _ (env.aR.symm.subR (c := 48) (l := 1) (by decide))
  have eb : n7.mem (bp + 48) = m.mem (bp + 48) := by
    rw [e48]; exact frR7 _ (env.bR.symm.subR (c := 48) (l := 1) (by decide))
  have has : (n5.mem (ap + 48)).zeroExtend 32 = 0 ∨ (n5.mem (ap + 48)).zeroExtend 32 = 1 :=
    zb _ (by rw [ea]; exact hsa)
  have hbs : (n7.mem (bp + 48)).zeroExtend 32 = 0 ∨ (n7.mem (bp + 48)).zeroExtend 32 = 1 :=
    zb _ (by rw [eb]; exact hsb)
  have r20_5 : reg n5 20 = (n1.mem (lcF sp0 + 16)).zeroExtend 32 := by
    rw [k45 20 (by decide), k3 20 (by decide), g2]; simp +decide only [upd_app, ↓reduceIte]; rw [sp1]
  have r8_5 : reg n5 8 = (n3.mem (lcF sp0 + 28)).zeroExtend 32 := by
    rw [k5 8 (by decide), g4]; simp +decide only [upd_app, ↓reduceIte]; rw [sp3]
  obtain ⟨xn, hxn⟩ : ∃ xn, aluEval .xor ((n5.mem (ap + 48)).zeroExtend 32) ((n1.mem (lcF sp0 + 16)).zeroExtend 32)
      = xn := ⟨_, rfl⟩
  obtain ⟨yn, hyn⟩ : ∃ yn, aluEval .xor ((n7.mem (bp + 48)).zeroExtend 32) ((n3.mem (lcF sp0 + 28)).zeroExtend 32)
      = yn := ⟨_, rfl⟩
  have hxn01 : xn = 0 ∨ xn = 1 := hxn ▸ xor01 has hcs
  have hyn01 : yn = 0 ∨ yn = 1 := hyn ▸ xor01 hbs hds
  have r20_7 : reg n7 20 = xn := by
    rw [k7 20 (by decide), g6]; simp +decide only [upd_app, ↓reduceIte]; rw [r9_5, r20_5, hxn]
  have r8_7 : reg n7 8 = (n3.mem (lcF sp0 + 28)).zeroExtend 32 := by rw [k67 8 (by decide), r8_5]
  have r19_8 : reg n8 19 = yn := by
    rw [g8]; simp +decide only [upd_app, ↓reduceIte]; rw [r19_7, r8_7, hyn]
  have r21_8 : reg n8 21 = aluEval .xor yn xn := by
    rw [g8]; simp +decide only [upd_app, ↓reduceIte]; rw [r19_7, r8_7, hyn, r20_7]
  obtain ⟨on, hon⟩ : ∃ on, aluEval .xor yn xn = on := ⟨_, rfl⟩
  have hon01 : on = 0 ∨ on = 1 := hon ▸ xor01 hyn01 hxn01
  rw [hon] at r21_8
  have ⟨hfl01, hfl1⟩ := flag01 hon01
  have sp8 : reg n8 sp = lcF sp0 := by rw [g8]; simp +decide only [upd_app, ↓reduceIte]; exact sp7
  obtain ⟨n9, c9, s9, sp9, k9, v9, f9⟩ := lc_callNeg env.hP s8.self (cIn env.code env.sC frR8)
    (lc_cn env frR8 (lc := 0x30) (hc := 0x28) (by decide) (by decide) (by decide) (by decide) (by decide))
    lc12_at_92 lc12_at_96 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x92 + 8) (by decide))
    sp8 (by rw [g8]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [g8]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [g8]; simp +decide only [upd_app, ↓reduceIte]; rw [r19_7, r8_7, hyn, r20_7, hon]) hfl01
  rw [lcF_cnR] at f9
  have frR9 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → n9.mem x = m.mem x := fun x hx => by
    rw [f9 x (by have := hx.sub (c := 0) (l := 0xE0) (by decide); rwa [add_ofNat_zero] at this)
      (inF (by decide) hx) (inF (by decide) hx), frR8 x hx]
  have k89 : ∀ q : Fin 32, q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21] → reg n9 q = reg n7 q :=
    fun q hq => by
      have nq : ∀ r : Fin 32, r.val ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21] → q ≠ r :=
        fun r hr e => hq (e ▸ hr)
      rw [k9 q (fun h => hq (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at h ⊢; omega)), g8]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact s7.zero.symm
      simp only [upd_app, h0, nq 19 (by decide), nq 21 (by decide), nq a1 (by decide), nq a2 (by decide),
        nq a0 (by decide), ite_false]
  have r19_9 : reg n9 19 = yn := by rw [k9 19 (by decide), r19_8]
  have r21_9 : reg n9 21 = on := by rw [k9 21 (by decide), r21_8]
  have r20_9 : reg n9 20 = xn := by rw [k89 20 (by decide), r20_7]
  -- zero the low difference
  obtain ⟨n10, c10, s10⟩ := St.block lcF6 s9 (cIn env.code env.sC frR9) lcF6_end (by simp [BlockOk, BInstr.ok, lcF6])
  simp only [runBlock, BInstr.run, lcF6] at s10
  have g10 : ∀ q, reg n10 q = _ := s10.regs
  obtain ⟨n11, c11, s11, -, k11⟩ := St.memsetW (B := P + 0x18A8) (w := 12) (dst := lcF sp0 + BitVec.ofNat 32 0xA8)
    (even_at P env.hP 0x18A8 (by decide)) s10.self (cIn env.code env.sC frR9) (cIn env.mset env.sM frR9)
    lc12_at_a4 lc12_at_a8 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0xA4 + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega) (by decide) (aligned_add hFa (by decide))
    (lcF_in (by decide) env.sM)
    (by rw [g10]; simp +decide only [upd_app, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [g10]; simp +decide only [upd_app, ↓reduceIte, aluEval])
    (by rw [g10]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  obtain ⟨M11, hM11⟩ : ∃ M11, fillWords n9.mem (lcF sp0 + BitVec.ofNat 32 0xA8) 0 12 = M11 := ⟨_, rfl⟩
  rw [hM11] at s11
  have frR11 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M11 x = m.mem x := fun x hx => by
    rw [← hM11, fillWords_outside 12 (inF (by decide) hx), frR9 x hx]
  have k911 : ∀ q : Fin 32, q.val ∉ [1, 8, 10, 11, 12, 13, 14, 15, 16] → reg n11 q = reg n9 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [1, 8, 10, 11, 12, 13, 14, 15, 16] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k11 q (nq a2 (by decide)) (nq a3 (by decide)) (nq a4 (by decide)) (nq a5 (by decide)) (nq a6 (by decide))
      (nq ra (by decide)), g10]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s9.zero.symm
    simp only [upd_app, h0, nq 8 (by decide), nq a1 (by decide), nq a2 (by decide), nq a0 (by decide), ite_false]
  have sp11 : reg n11 sp = lcF sp0 := by rw [k911 sp (by decide), sp9]
  have r8_11 : reg n11 8 = lcF sp0 + BitVec.ofNat 32 0xA8 := by
    rw [k11 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g10]
    simp +decide only [upd_app, ↓reduceIte]; rw [sp9]; rfl
  -- the low difference
  obtain ⟨n12, c12, s12⟩ := St.block lcG s11 (cIn env.code env.sC frR11) lcG_end (by simp [BlockOk, BInstr.ok, lcG])
  simp only [runBlock, BInstr.run, lcG] at s12
  have g12 : ∀ q, reg n12 q = _ := s12.regs
  obtain ⟨n13, d13, s13⟩ := s12.self.notTaken (cIn env.code env.sC frR11) 0xB2 lc12_at_b0 (by decide) (by
    rw [g12]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [show reg n12 x0 = 0 from s12.self.zero]; decide)
  have g13 : ∀ q, reg n13 q = reg n12 q := s13.regs
  have k1113 : ∀ q : Fin 32, q.val ∉ [9, 24] → reg n13 q = reg n11 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [9, 24] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [g13, g12]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s11.zero.symm
    simp only [upd_app, h0, nq 9 (by decide), nq 24 (by decide), ite_false]
  have r22_13 : reg n13 22 = lcF sp0 + BitVec.ofNat 32 0x68 + BitVec.ofNat 32 (4 * 0) := by
    rw [k1113 22 (by decide), k911 22 (by decide), k89 22 (by decide), k67 22 (by decide), k5 22 (by decide), g4]
    simp +decide only [upd_app, ↓reduceIte]; rw [sp3, add_ofNat_zero]; rfl
  have r23_13 : reg n13 23 = lcF sp0 + BitVec.ofNat 32 0x30 + BitVec.ofNat 32 (4 * 0) := by
    rw [k1113 23 (by decide), k911 23 (by decide), k89 23 (by decide), k7 23 (by decide), g6]
    simp +decide only [upd_app, ↓reduceIte]; rw [sp5, add_ofNat_zero]; rfl
  have r8_13 : reg n13 8 = lcF sp0 + BitVec.ofNat 32 0xA8 + BitVec.ofNat 32 (4 * 0) := by
    rw [k1113 8 (by decide), r8_11, add_ofNat_zero]
  have r9_13 : reg n13 9 = BitVec.ofNat 32 (12 - 0) := by
    rw [g13, g12]; simp +decide only [upd_app, ↓reduceIte, aluEval]
    try (rw [show reg n11 x0 = 0 from s11.zero]; first | done | rfl)
  have r24_13 : reg n13 24 = 0 := by
    rw [g13, g12]; simp +decide only [upd_app, ↓reduceIte, aluEval]
    try (rw [show reg n11 x0 = 0 from s11.zero]; first | done | rfl)
  have sp13 : reg n13 sp = lcF sp0 := by rw [k1113 sp (by decide), sp11]
  have fo : ∀ c, lcF sp0 + BitVec.ofNat 32 c = lcR sp0 + BitVec.ofNat 32 (0xE0 + c) := lcF_ofs sp0
  obtain ⟨n14, M14, c14, s14, hc14, hb14, f14, bm14, v14, sp14, k14⟩ :=
    lc_sub_loop (b0 := 0) (M0 := M11) (N := 12) (lp := lcF sp0 + BitVec.ofNat 32 0x68)
      (rp := lcF sp0 + BitVec.ofNat 32 0x30) (D := lcF sp0 + BitVec.ofNat 32 0xA8) lcLoop1 (by decide) env.hP hFa
      (aligned_add hFa (by decide)) (aligned_add hFa (by decide)) (aligned_add hFa (by decide))
      (by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega)
      (by rw [lcF_m4, fo]; exact rsep (by omega) (by omega) (by omega))
      (by rw [lcF_m4, fo]; exact rsep (by omega) (by omega) (by omega))
      (by rw [lcF_m4, fo]; exact rsep (by omega) (by omega) (by omega))
      (fsep (by omega) (by omega) (by omega)) (fsep (by omega) (by omega) (by omega))
      (by rw [lcF_m4]; exact env.sBs.sub (by decide)) (by rw [lcF_m4]; exact env.sC.sub (by decide))
      (lcF_in (by decide) env.sBs) (lcF_in (by decide) env.sC)
      11 0 rfl s13.self (cIn env.code env.sC frR11) (cIn env.bsub env.sBs frR11) (fun _ _ _ => rfl) (.inl rfl)
      (by simp [accV, maskBit]) sp13 r22_13 r23_13 r8_13 r9_13 r24_13
  have frR14 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M14 x = m.mem x := fun x hx => by
    rw [f14 x (by rw [lcF_m4]; exact inR (by decide) hx) (inF (by decide) hx), frR11 x hx]
  have k1314 : ∀ q : Fin 32, lcSubKeep q = true → reg n14 q = reg n13 q := k14
  -- copy the low difference over `x`
  obtain ⟨n15, c15, s15⟩ := St.block lcH s14 hc14 lcH_end (by simp [BlockOk, BInstr.ok, lcH])
  simp only [runBlock, BInstr.run, lcH] at s15
  have g15 : ∀ q, reg n15 q = _ := s15.regs
  have e8 : P + 0x1910 + 8 = P + 0x1918 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n16, c16, s16, -, k16⟩ := St.memcpyW (B := P + 0x1910) (w := 12) (dst := lcF sp0 + BitVec.ofNat 32 0x68)
    (src := lcF sp0 + BitVec.ofNat 32 0xA8)
    (even_at P env.hP 0x1910 (by decide)) s15.self hc14 (cIn env.stub env.sU frR14)
    (by rw [e8]; exact cIn env.body env.sB frR14)
    lc12_at_da lc12_at_de (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0xDA + 8) (by decide))
    (by decide) (by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega) (by decide) (aligned_add hFa (by decide))
    (aligned_add hFa (by decide)) (fsep (by omega) (by omega) (by omega)) (by rw [e8]; exact lcF_in (by decide) env.sB)
    (by rw [g15]; simp +decide only [upd_app, ↓reduceIte]; rw [sp14]; rfl)
    (by rw [g15]; simp +decide only [upd_app, ↓reduceIte]; rw [sp14]; rfl)
    (by rw [g15]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  obtain ⟨M16, hM16⟩ : ∃ M16, copyWords M14 (lcF sp0 + BitVec.ofNat 32 0x68) (lcF sp0 + BitVec.ofNat 32 0xA8) 12 = M16 :=
    ⟨_, rfl⟩
  rw [hM16] at s16
  have frR16 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M16 x = m.mem x := fun x hx => by
    rw [← hM16, copyWords_outside 12 (inF (by decide) hx), frR14 x hx]
  have k1416 : ∀ q : Fin 32, q.val ∉ [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → reg n16 q = reg n14 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [k16 q (nq a1 (by decide)) (nq a2 (by decide)) (nq a3 (by decide)) (nq a4 (by decide)) (nq a5 (by decide))
      (nq a6 (by decide)) (nq a7 (by decide)) (nq t0 (by decide)) (nq t1 (by decide)) (nq ra (by decide)), g15]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s14.zero.symm
    simp only [upd_app, h0, nq a0 (by decide), nq a1 (by decide), nq a2 (by decide), ite_false]
  have sp16 : reg n16 sp = lcF sp0 := by rw [k1416 sp (by decide), sp14]
  -- the high difference
  obtain ⟨n17, c17, s17⟩ := St.block lcI s16 (cIn env.code env.sC frR16) lcI_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lcI, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp16]
    exact ⟨⟨aligned_add hFa (by decide), lcF_in (by decide) env.sC⟩, aligned_add hFa (by decide),
      lcF_in (by decide) env.sC⟩)
  simp only [runBlock, BInstr.run, lcI] at s17
  have g17 : ∀ q, reg n17 q = _ := s17.regs
  simp +decide only [upd_app, ↓reduceIte, sp16, show reg n16 x0 = 0 from s16.zero] at s17
  obtain ⟨M17, hM17⟩ : ∃ M17, memStore32 (memStore32 M16 (lcF sp0 + 160) 0) (lcF sp0 + 164) 0 = M17 := ⟨_, rfl⟩
  rw [hM17] at s17
  have frR17 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M17 x = m.mem x := fun x hx => by
    rw [← hM17, memStore32_get_sep (frm_sep' (fF x hx) (c := 164) (by decide)),
      memStore32_get_sep (frm_sep' (fF x hx) (c := 160) (by decide)), frR16 x hx]
  have hc17 := cIn env.code env.sC frR17
  obtain ⟨n18, d18, s18⟩ := s17.self.notTaken hc17 0xF4 lc12_at_f2 (by decide) (by
    rw [g17]; simp +decide only [upd_app, ↓reduceIte, aluEval]
    try (rw [show reg n16 x0 = 0 from s16.zero]; first | done | decide)
    try (rw [show reg n17 x0 = 0 from s17.self.zero]; first | done | decide))
  have g18 : ∀ q, reg n18 q = reg n17 q := s18.regs
  have k1618 : ∀ q : Fin 32, q.val ∉ [8, 9, 22, 23] → reg n18 q = reg n16 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [8, 9, 22, 23] → q ≠ r := fun r hr e => hq (e ▸ hr)
    rw [g18, g17]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact s16.zero.symm
    simp only [upd_app, h0, nq 8 (by decide), nq 9 (by decide), nq 22 (by decide), nq 23 (by decide), ite_false]
  have r_18 : ∀ (r : Fin 32) (c : Nat), (r = 22 ∧ c = 0x20) ∨ (r = 23 ∧ c = 0x28) ∨ (r = 8 ∧ c = 0xA0) →
      reg n18 r = lcF sp0 + BitVec.ofNat 32 c + BitVec.ofNat 32 (4 * 0) := fun r c h => by
    rw [add_ofNat_zero]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [g18, g17]; simp +decide only [upd_app, ↓reduceIte]; rw [sp16]; rfl
  have r9_18 : reg n18 9 = BitVec.ofNat 32 (2 - 0) := by
    rw [g18, g17]; simp +decide only [upd_app, ↓reduceIte, aluEval]
    try (rw [show reg n16 x0 = 0 from s16.zero]; first | done | rfl)
  have r24_18 : reg n18 24 = reg n14 24 := by rw [k1618 24 (by decide), k1416 24 (by decide)]
  have sp18 : reg n18 sp = lcF sp0 := by rw [k1618 sp (by decide), sp16]
  obtain ⟨n19, M19, c19, s19, hc19, hb19, f19, bm19, v19, sp19, k19⟩ :=
    lc_sub_loop (b0 := reg n14 24) (M0 := M17) (N := 2) (lp := lcF sp0 + BitVec.ofNat 32 0x20)
      (rp := lcF sp0 + BitVec.ofNat 32 0x28) (D := lcF sp0 + BitVec.ofNat 32 0xA0) lcLoop2 (by decide) env.hP hFa
      (aligned_add hFa (by decide)) (aligned_add hFa (by decide)) (aligned_add hFa (by decide))
      (by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega)
      (by rw [lcF_m4, fo]; exact rsep (by omega) (by omega) (by omega))
      (by rw [lcF_m4, fo]; exact rsep (by omega) (by omega) (by omega))
      (by rw [lcF_m4, fo]; exact rsep (by omega) (by omega) (by omega))
      (fsep (by omega) (by omega) (by omega)) (fsep (by omega) (by omega) (by omega))
      (by rw [lcF_m4]; exact env.sBs.sub (by decide)) (by rw [lcF_m4]; exact env.sC.sub (by decide))
      (lcF_in (by decide) env.sBs) (lcF_in (by decide) env.sC)
      1 0 rfl s18.self hc17 (cIn env.bsub env.sBs frR17) (fun _ _ _ => rfl) bm14
      (by simp [accV]) sp18 (r_18 22 0x20 (.inl ⟨rfl, rfl⟩)) (r_18 23 0x28 (.inr (.inl ⟨rfl, rfl⟩)))
      (r_18 8 0xA0 (.inr (.inr ⟨rfl, rfl⟩))) r9_18 r24_18
  have frR19 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M19 x = m.mem x := fun x hx => by
    rw [f19 x (by rw [lcF_m4]; exact inR (by decide) hx) (inF (by decide) hx), frR17 x hx]
  have k1819 : ∀ q : Fin 32, lcSubKeep q = true → reg n19 q = reg n18 q := k19
  have r21_19 : reg n19 21 = on := by
    rw [k1819 21 rfl, k1618 21 (by decide), k1416 21 (by decide), k1314 21 rfl, k1113 21 (by decide),
      k911 21 (by decide), r21_9]
  -- the high difference to `F + 0x20`, and `swap`
  obtain ⟨n20, c20, s20⟩ := St.block lcJ s19 hc19 lcJ_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lcJ, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp19]
    exact ⟨aligned_add hFa (by decide), aligned_add hFa (by decide), ⟨aligned_add hFa (by decide),
      lcF_in (by decide) env.sC⟩, ⟨aligned_add hFa (by decide), lcF_in (by decide) env.sC⟩,
      ⟨aligned_add hFa (by decide), lcF_in (by decide) env.sC⟩, aligned_add hFa (by decide)⟩)
  simp only [runBlock, BInstr.run, lcJ] at s20
  have g20 : ∀ q, reg n20 q = _ := s20.regs
  simp +decide only [upd_app, ↓reduceIte, sp19] at s20
  obtain ⟨M20, hM20⟩ : ∃ M20, memStore32
      (memStore32 (memStore32 M19 (lcF sp0 + 32) (memLoad32 M19 (lcF sp0 + 160))) (lcF sp0 + 36)
        (memLoad32 M19 (lcF sp0 + 164))) (lcF sp0 + 160) (reg n19 24) = M20 := ⟨_, rfl⟩
  rw [hM20] at s20
  have frR20 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → M20 x = m.mem x := fun x hx => by
    rw [← hM20, memStore32_get_sep (frm_sep' (fF x hx) (c := 160) (by decide)),
      memStore32_get_sep (frm_sep' (fF x hx) (c := 36) (by decide)),
      memStore32_get_sep (frm_sep' (fF x hx) (c := 32) (by decide)), frR19 x hx]
  have hc20 := cIn env.code env.sC frR20
  have sp20 : reg n20 sp = lcF sp0 := by rw [g20]; simp +decide only [upd_app, ↓reduceIte]; exact sp19
  obtain ⟨b2, hb2⟩ : ∃ b2, reg n19 24 = b2 := ⟨_, rfl⟩
  rw [hb2] at bm19 v19
  have ld160 : memLoad32 (memStore32 (memStore32 (memStore32 M19 (lcF sp0 + 32) (memLoad32 M19 (lcF sp0 + 160)))
      (lcF sp0 + 36) (memLoad32 M19 (lcF sp0 + 164))) (lcF sp0 + 160) (reg n19 24)) (lcF sp0 + 160) = b2 := by
    rw [memLoad32_store32_same, hb2]
  have r8_20 : reg n20 8 = if on = 1 ∧ b2 = 0xFFFFFFFF then 1 else 0 := by
    rw [g20]; simp +decide only [upd_app, ↓reduceIte]; rw [sp19, r21_19, ld160]; exact swap01 hon01 bm19
  obtain ⟨sw, hsw⟩ : ∃ sw : Word, (if on = 1 ∧ b2 = 0xFFFFFFFF then 1 else 0) = sw := ⟨_, rfl⟩
  have hsw01 : sw = 0 ∨ sw = 1 := by rw [← hsw]; split <;> simp
  rw [hsw] at r8_20
  obtain ⟨n21, c21, s21, sp21, k21, v21, f21⟩ := lc_callNeg env.hP s20.self hc20
    (lc_cn env frR20 (lc := 0x68) (hc := 0x20) (by decide) (by decide) (by decide) (by decide) (by decide))
    lc12_at_134 lc12_at_138 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P env.hP (0x134 + 8) (by decide)) sp20
    (by rw [g20]; simp +decide only [upd_app, ↓reduceIte]; rw [sp19]; rfl)
    (by rw [g20]; simp +decide only [upd_app, ↓reduceIte]; rw [sp19]; rfl)
    (by rw [← r8_20, g20, g20]; simp +decide only [upd_app, ↓reduceIte]; exact zw _) hsw01
  rw [lcF_cnR] at f21
  have frR21 : ∀ x, Sep (lcR sp0) 0x1E0 x 1 → n21.mem x = m.mem x := fun x hx => by
    rw [f21 x (by have := hx.sub (c := 0) (l := 0xE0) (by decide); rwa [add_ofNat_zero] at this)
      (inF (by decide) hx) (inF (by decide) hx), frR20 x hx]
  have hc21 := cIn env.code env.sC frR21
  -- the registers that live from the prologue to here
  have kL : ∀ q : Fin 32, q.val ∈ [18, 19, 20] → reg n21 q = reg n9 q := fun q hq => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    have h1 : q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
    rw [k21 q h1, g20]
    have h0 : q.val ≠ 0 := by omega
    have nq : ∀ r : Fin 32, r.val ∈ [8, 10, 11, 12] → q ≠ r := fun r hr e => by
      subst e; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; omega
    simp only [upd_app, h0, nq 8 (by decide), nq a0 (by decide), nq a1 (by decide), nq a2 (by decide), ite_false]
    rw [k1819 q (by simp only [lcSubKeep, List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq]; omega),
      k1618 q (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega),
      k1416 q (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega),
      k1314 q (by simp only [lcSubKeep, List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq]; omega),
      k1113 q (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega),
      k911 q (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega)]
  have r18_21 : reg n21 18 = out := by
    rw [kL 18 (by decide), k9 18 (by decide), g8]; simp +decide only [upd_app, ↓reduceIte]
    rw [k67 18 (by decide), k45 18 (by decide), k3 18 (by decide), g2]; simp +decide only [upd_app, ↓reduceIte]
    rw [k1 18 (by decide), r18_0]
  have r19_21 : reg n21 19 = yn := by rw [kL 19 (by decide), r19_9]
  have r20_21 : reg n21 20 = xn := by rw [kL 20 (by decide), r20_9]
  have r8_21 : reg n21 8 = sw := by rw [k21 8 (by decide), r8_20]
  obtain ⟨n22, c22, s22⟩ := St.block lcK s21 hc21 lcK_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lcK, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp21]; exact ⟨aligned_add hFa (by decide), aligned_add hFa (by decide)⟩)
  simp only [runBlock, BInstr.run, lcK] at s22
  have g22 : ∀ q, reg n22 q = _ := s22.regs
  have oF : Sep out 48 (lcF sp0 + BitVec.ofNat 32 0x68) 48 := by
    rw [lcF_ofs]; have := env.oR.sub (c := 0) (l := 48) (by decide); rw [add_ofNat_zero] at this
    exact this.subR (by decide)
  obtain ⟨n23, c23, s23, -, k23⟩ := St.memcpyW (B := P + 0x1910) (w := 12) (dst := out)
    (src := lcF sp0 + BitVec.ofNat 32 0x68)
    (even_at P env.hP 0x1910 (by decide)) s22.self hc21 (cIn env.stub env.sU frR21)
    (by rw [e8]; exact cIn env.body env.sB frR21)
    lc12_at_158 lc12_at_15c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x158 + 8) (by decide))
    (by decide) (by have := env.hwo; omega) (by decide) env.hout (aligned_add hFa (by decide)) oF
    (by rw [e8]; have := env.oB.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this)
    (by rw [g22]; simp +decide only [upd_app, ↓reduceIte]; rw [r18_21]; exact zw _)
    (by rw [g22]; simp +decide only [upd_app, ↓reduceIte]; rw [sp21]; rfl)
    (by rw [g22]; simp +decide only [upd_app, ↓reduceIte, aluEval])
  have k2223 : ∀ q : Fin 32, q.val ∉ [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → reg n23 q = reg n22 q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∈ [1, 5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → q ≠ r := fun r hr e => hq (e ▸ hr)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [s23.zero]; exact s22.self.zero.symm
    exact k23 q (nq a1 (by decide)) (nq a2 (by decide)) (nq a3 (by decide)) (nq a4 (by decide)) (nq a5 (by decide))
      (nq a6 (by decide)) (nq a7 (by decide)) (nq t0 (by decide)) (nq t1 (by decide)) (nq ra (by decide)) |>.trans
      (by rfl)
  have r18_23 : reg n23 18 = out := by
    rw [k2223 18 (by decide), g22]; simp +decide only [upd_app, ↓reduceIte]; exact r18_21
  obtain ⟨M23, hM23⟩ : ∃ M23, copyWords n21.mem out (lcF sp0 + BitVec.ofNat 32 0x68) 12 = M23 := ⟨_, rfl⟩
  rw [hM23] at s23
  have oC48 : Sep out (4 * 12) P lincomb12Code.length := by
    have := env.oC.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
  have hc23 : CodeIn M23 P lincomb12Code := fun i hi => by
    rw [← hM23, copyWords_outside 12 (oC48.subR (c := i) (l := 1) (by omega))]; exact hc21 i hi
  obtain ⟨n24, c24, s24⟩ := St.block lcL s23 hc23 lcL_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, lcL, upd_app, ↓reduceIte, and_true, true_and]
    rw [r18_23]
    exact ⟨⟨aligned_add env.hout (by decide), env.oC.sub (by decide)⟩, ⟨aligned_add env.hout (by decide),
      env.oC.sub (by decide)⟩, env.oC.sub (by decide)⟩)
  simp only [runBlock, BInstr.run, lcL] at s24
  have g24 : ∀ q, reg n24 q = reg n23 q := s24.regs
  rw [r18_23] at s24
  -- the saved registers survive to the epilogue
  have hsl24 : ∀ r o, (r, o) ∈ lcPs → memLoad32 (memStore8 (memStore32 (memStore32 M23 (out + 48) (reg n23 9))
      (out + 52) (reg n23 21)) (out + 56) ((reg n23 8).extractLsb' 0 8)) (lcF sp0 + o) = reg m r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := lcPs_range (r, o) h
    dsimp only at ho1 ho2
    have e : lcF sp0 + o = lcF sp0 + BitVec.ofNat 32 o.toNat := by rw [ofNat_toNat_self]
    have eR : lcF sp0 + o = lcR sp0 + BitVec.ofNat 32 (0xE0 + o.toNat) := by rw [e, fo]
    have sF : ∀ c l, c + l ≤ o.toNat → Sep (lcF sp0 + BitVec.ofNat 32 c) l (lcF sp0 + o) 4 := fun c l hcl => by
      rw [e]; exact sep_offsets _ (.inl hcl) (by omega) (by omega)
    have sFw : ∀ c : Word, c.toNat + 4 ≤ o.toNat → Sep (lcF sp0 + c) 4 (lcF sp0 + o) 4 := fun c hc =>
      sep_word_offsets _ c o (.inl hc) (by omega) (by omega)
    have sRb : ∀ c l, c + l ≤ 0xE0 → Sep (lcR sp0 + BitVec.ofNat 32 c) l (lcF sp0 + o) 4 := fun c l hcl => by
      rw [eR]; exact sep_offsets _ (.inl (by omega)) (by omega) (by omega)
    have sR0 : Sep (lcR sp0) 0xE0 (lcF sp0 + o) 4 := by
      have := sRb 0 0xE0 (by decide); rwa [add_ofNat_zero] at this
    have sO : Sep out 57 (lcF sp0 + o) 4 := by rw [eR]; exact env.oR.subR (by omega)
    have s20 : Sep (lcF sp0 + 0xFFFFFFE0) 0x20 (lcF sp0 + o) 4 := by rw [lcF_m20]; exact sRb _ _ (by decide)
    have s70 : Sep (lcF sp0 + 0xFFFFFF90) 0x70 (lcF sp0 + o) 4 := by rw [lcF_m70]; exact sRb _ _ (by decide)
    have s4 : Sep (lcF sp0 + 0xFFFFFFFC) 4 (lcF sp0 + o) 4 := by rw [lcF_m4]; exact sRb _ _ (by decide)
    rw [show (56 : Word) = BitVec.ofNat 32 56 from rfl, show (52 : Word) = BitVec.ofNat 32 52 from rfl,
      show (48 : Word) = BitVec.ofNat 32 48 from rfl,
      memLoad32_store8_sep (sO.sub (c := 56) (l := 1) (by decide)),
      memLoad32_store32_sep (sO.sub (c := 52) (l := 4) (by decide)),
      memLoad32_store32_sep (sO.sub (c := 48) (l := 4) (by decide)),
      ← hM23, copyWords_load_sep (sO.sub (c := 0) (l := 4 * 12) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
      load_frame3 f21 sR0 (sF 0x68 48 (by omega)) (sF 0x20 8 (by omega)),
      ← hM20, memLoad32_store32_sep (sFw 160 (by show 160 + 4 ≤ o.toNat; omega)), memLoad32_store32_sep (sFw 36 (by show 36 + 4 ≤ o.toNat; omega)),
      memLoad32_store32_sep (sFw 32 (by show 32 + 4 ≤ o.toNat; omega)),
      load_frame2 f19 s4 (sF 0xA0 8 (by omega)),
      ← hM17, memLoad32_store32_sep (sFw 164 (by show 164 + 4 ≤ o.toNat; omega)), memLoad32_store32_sep (sFw 160 (by show 160 + 4 ≤ o.toNat; omega)),
      ← hM16, copyWords_load_sep (sF 0x68 (4 * 12) (by omega)),
      load_frame2 f14 s4 (sF 0xA8 (4 * 12) (by omega)),
      ← hM11, fillWords_load_sep (sF 0xA8 (4 * 12) (by omega)),
      load_frame3 f9 sR0 (sF 0x30 48 (by omega)) (sF 0x28 8 (by omega)),
      ← hM8, memLoad32_store32_sep (sFw 44 (by show 44 + 4 ≤ o.toNat; omega)), memLoad32_store32_sep (sFw 40 (by show 40 + 4 ≤ o.toNat; omega)),
      load_frame2 f7 s70 (sF 0x30 56 (by omega)),
      ← hM6, memLoad32_store32_sep (sFw 36 (by show 36 + 4 ≤ o.toNat; omega)), memLoad32_store32_sep (sFw 32 (by show 32 + 4 ≤ o.toNat; omega)),
      load_frame2 f5 s70 (sF 0x68 56 (by omega)),
      load_frame2 f3 s20 (sF 0x14 9 (by omega)),
      load_frame2 f1 s20 (sF 8 9 (by omega)), hsl0 r o h]
  have e48' : (48 : Word) = BitVec.ofNat 32 48 := rfl
  have e52 : (52 : Word) = BitVec.ofNat 32 52 := rfl
  have e56 : (56 : Word) = BitVec.ofNat 32 56 := rfl
  have hc24 : CodeIn (memStore8 (memStore32 (memStore32 M23 (out + 48) (reg n23 9))
      (out + 52) (reg n23 21)) (out + 56) ((reg n23 8).extractLsb' 0 8)) P lincomb12Code := by
    rw [e48', e52, e56]
    exact ((hc23.store32 (env.oC.sub (by decide))).store32 (env.oC.sub (by decide))).store8 (env.oC.sub (by decide))
  have sp24 : reg n24 sp = lcF sp0 := by
    rw [g24, k2223 sp (by decide), g22]; simp +decide only [upd_app, ↓reduceIte]; exact sp21
  obtain ⟨n25, c25, pc25, sp25, mem25, sv25, k25⟩ := lc_epi (v := reg m) s24.self hc24 hFa sp24 hsl24
  have hsp0 : lcF sp0 + 0x100 = sp0 := by
    show sp0 + 0xFFFFFF00 + 0x100 = sp0
    rw [BitVec.add_assoc, show (0xFFFFFF00 : Word) + 0x100 = 0 by decide, add_lit_zero]
  have hsave : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24] → ∃ o, (q, o) ∈ lcPs := fun q hq => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h | h | h | h | h | h | h | h <;> rw [show q = ⟨_, by decide⟩ from Fin.ext h]
    · exact ⟨0xF8, by decide⟩
    · exact ⟨0xF4, by decide⟩
    · exact ⟨0xF0, by decide⟩
    · exact ⟨0xEC, by decide⟩
    · exact ⟨0xE8, by decide⟩
    · exact ⟨0xE4, by decide⟩
    · exact ⟨0xE0, by decide⟩
    · exact ⟨0xDC, by decide⟩
    · exact ⟨0xD8, by decide⟩
  refine ⟨n25, c0.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (c11.trans (c12.trans (.cons d13 (c14.trans (c15.trans (c16.trans (c17.trans (.cons d18
    (c19.trans (c20.trans (c21.trans (c22.trans (c23.trans (c24.trans c25)))))))))))))))))))))))),
    by rw [pc25, hra, hret], by rw [sp25, hsp0], fun q hq => ?_, ?_, ?_, fun x hx ho => ?_⟩
  · by_cases hsv : q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24]
    · obtain ⟨o, ho⟩ := hsave q hsv
      exact sv25 q o ho
    by_cases hsp' : q = sp
    · subst hsp'; rw [sp25, hsp0, hsp]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n25 0 = 0 from rfl).trans (show reg m 0 = 0 from rfl).symm
    have hq' : q.val ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28, 29, 30,
        31] := by
      intro h; apply hsp'; apply Fin.ext
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at h hq hsv
      show q.val = 2; omega
    have nn : ∀ (l : List Nat), (∀ v ∈ l, v = 0 ∨ v ∈ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        20, 21, 22, 23, 24, 28, 29, 30, 31]) → q.val ∉ l := fun l hl hm => by
      rcases hl _ hm with h | h
      · exact h0 h
      · exact hq' h
    have nq : ∀ r : Fin 32, r.val ∈ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        28, 29, 30, 31] → q ≠ r := fun r hr e => hq' (e ▸ hr)
    rw [k25 q (nn _ (by decide)) hsp', g24, k2223 q (nn _ (by decide)), g22]
    simp only [upd_app, h0, nq 9 (by decide), nq 21 (by decide), nq a0 (by decide), nq a1 (by decide),
      nq 8 (by decide), nq a2 (by decide), ite_false]
    rw [k21 q (nn _ (by decide)), g20]
    simp only [upd_app, h0, nq 8 (by decide), nq a0 (by decide), nq a1 (by decide), nq a2 (by decide), ite_false]
    rw [k1819 q (by simp only [lcSubKeep, decide_eq_true_eq]; exact nn _ (by decide)),
      k1618 q (nn _ (by decide)), k1416 q (nn _ (by decide)),
      k1314 q (by simp only [lcSubKeep, decide_eq_true_eq]; exact nn _ (by decide)),
      k1113 q (nn _ (by decide)), k911 q (nn _ (by decide)), k89 q (nn _ (by decide)), k67 q (nn _ (by decide)),
      k45 q (nn _ (by decide)), k3 q (nn _ (by decide)), g2]
    simp only [upd_app, h0, nq 20 (by decide), nq a0 (by decide), nq a1 (by decide), ite_false]
    rw [k1 q (nn _ (by decide)), k0 q (nn _ (by decide))]
  · have hsg : reg n23 8 = if sw = 1 then yn else xn := by
      rw [k2223 8 (by decide), g22]; simp +decide only [upd_app, ↓reduceIte]; rw [r8_21, r20_21, r19_21]
      exact signw hsw01 hxn01 hyn01
    have hsg01 : reg n23 8 = 0 ∨ reg n23 8 = 1 := by rw [hsg]; split <;> assumption
    have := choice_byte (memStore32 (memStore32 M23 (out + 48) (reg n23 9)) (out + 52) (reg n23 21)) (out + 56)
      (reg n23 8) hsg01
    rw [mem25]
    generalize memStore8 (memStore32 (memStore32 M23 (out + 48) (reg n23 9)) (out + 52) (reg n23 21)) (out + 56)
      ((reg n23 8).extractLsb' 0 8) (out + 56) = b at this ⊢
    have h2 : b.toNat = (reg n23 8).toNat := by
      rw [← this, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
    rw [h2]; rcases hsg01 with h | h <;> rw [h] <;> decide
  · -- pointwise frame facts on the frame
    have bs : ∀ (c l t : Nat), t < c ∨ c + l ≤ t → c + l ≤ 0x100 → t < 0x100 →
        Sep (lcF sp0 + BitVec.ofNat 32 c) l (lcF sp0 + BitVec.ofNat 32 t) 1 := fun c l t h hc ht =>
      fsep (by omega) hc (by omega)
    have bR : ∀ (t : Nat), t < 0x100 → Sep (lcR sp0) 0xE0 (lcF sp0 + BitVec.ofNat 32 t) 1 := fun t ht => by
      rw [fo]; have := rsep (c := 0) (n := 0xE0) (d := 0xE0 + t) (k := 1) (.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have b70 : ∀ (t : Nat), t < 0x100 → Sep (lcF sp0 + 0xFFFFFF90) 0x70 (lcF sp0 + BitVec.ofNat 32 t) 1 :=
      fun t ht => by rw [lcF_m70, fo]; exact rsep (.inl (by omega)) (by omega) (by omega)
    have b20 : ∀ (t : Nat), t < 0x100 → Sep (lcF sp0 + 0xFFFFFFE0) 0x20 (lcF sp0 + BitVec.ofNat 32 t) 1 :=
      fun t ht => by rw [lcF_m20, fo]; exact rsep (.inl (by omega)) (by omega) (by omega)
    have b4 : ∀ (t : Nat), t < 0x100 → Sep (lcF sp0 + 0xFFFFFFFC) 4 (lcF sp0 + BitVec.ofNat 32 t) 1 :=
      fun t ht => by rw [lcF_m4, fo]; exact rsep (.inl (by omega)) (by omega) (by omega)
    have lit : ∀ (w : Word) (c l t : Nat), w = BitVec.ofNat 32 c → t < c ∨ c + l ≤ t → c + l ≤ 0x100 → t < 0x100 →
        Sep (lcF sp0 + w) l (lcF sp0 + BitVec.ofNat 32 t) 1 := fun w c l t hw h hc ht => by
      rw [hw]; exact bs c l t h hc ht
    -- `x`'s low words at `F + 0x68`
    have hXlo : accV M11 (lcF sp0 + BitVec.ofNat 32 0x68) 12 = accV n5.mem (lcF sp0 + BitVec.ofNat 32 0x68) 12 :=
      lc_pt 12 fun t ht => by
        rw [← hM11, fillWords_outside 12 (bs 0xA8 (4 * 12) (0x68 + t) (by omega) (by decide) (by omega)),
          f9 _ (bR _ (by omega)) (bs 0x30 48 _ (by omega) (by decide) (by omega))
            (bs 0x28 8 _ (by omega) (by decide) (by omega)),
          ← hM8, memStore32_get_sep (lit 44 44 4 (0x68 + t) rfl (by omega) (by decide) (by omega)),
          memStore32_get_sep (lit 40 40 4 (0x68 + t) rfl (by omega) (by decide) (by omega)),
          f7 _ (b70 _ (by omega)) (bs 0x30 56 _ (by omega) (by decide) (by omega)),
          ← hM6, memStore32_get_sep (lit 36 36 4 (0x68 + t) rfl (by omega) (by decide) (by omega)),
          memStore32_get_sep (lit 32 32 4 (0x68 + t) rfl (by omega) (by decide) (by omega))]
    -- words at `F + c` of `M17` are `n9`'s for `c` outside the low difference and below `F + 0x68`
    have m17 : ∀ t, t < 0x68 →
        M17 (lcF sp0 + BitVec.ofNat 32 t) = n9.mem (lcF sp0 + BitVec.ofNat 32 t) := fun t ht => by
      rw [← hM17, memStore32_get_sep (lit 164 164 4 t rfl (by omega) (by decide) (by omega)),
        memStore32_get_sep (lit 160 160 4 t rfl (by omega) (by decide) (by omega)),
        ← hM16, copyWords_outside 12 (bs 0x68 (4 * 12) t (by omega) (by decide) (by omega)),
        f14 _ (b4 t (by omega)) (bs 0xA8 (4 * 12) t (by omega) (by decide) (by omega)),
        ← hM11, fillWords_outside 12 (bs 0xA8 (4 * 12) t (by omega) (by decide) (by omega))]
    -- `x`'s high words, kept at `F + 0x20`
    have hXhi : accV M17 (lcF sp0 + BitVec.ofNat 32 0x20) 2 = accV n5.mem (lcF sp0 + BitVec.ofNat 32 0x98) 2 := by
      have e9 : ∀ t, t < 8 → n9.mem (lcF sp0 + BitVec.ofNat 32 (0x20 + t)) =
          M6 (lcF sp0 + BitVec.ofNat 32 (0x20 + t)) := fun t ht => by
        rw [f9 _ (bR _ (by omega)) (bs 0x30 48 _ (by omega) (by decide) (by omega))
            (bs 0x28 8 _ (by omega) (by decide) (by omega)),
          ← hM8, memStore32_get_sep (lit 44 44 4 (0x20 + t) rfl (by omega) (by decide) (by omega)),
          memStore32_get_sep (lit 40 40 4 (0x20 + t) rfl (by omega) (by decide) (by omega)),
          f7 _ (b70 _ (by omega)) (bs 0x30 56 _ (by omega) (by decide) (by omega))]
      rw [lc_pt (M' := M6) 2 fun t ht => by rw [m17 _ (by omega), e9 t (by omega)]]
      rw [accV_two, accV_two, ← hM6]
      rw [show lcF sp0 + BitVec.ofNat 32 0x20 + 4 = lcF sp0 + 36 by rw [BitVec.add_assoc]; rfl,
        show lcF sp0 + BitVec.ofNat 32 0x20 = lcF sp0 + 32 from rfl, memLoad32_store32_same,
        memLoad32_store32_sep (sep_word_offsets _ 36 32 (.inr (by decide)) (by decide) (by decide)),
        memLoad32_store32_same, show lcF sp0 + BitVec.ofNat 32 0x98 + 4 = lcF sp0 + 156 by rw [BitVec.add_assoc]; rfl,
        show lcF sp0 + BitVec.ofNat 32 0x98 = lcF sp0 + 152 from rfl]
    -- `y'`, after the first conditional negation, at `F + 0x30` and `F + 0x28`
    have hYlo : accV M11 (lcF sp0 + BitVec.ofNat 32 0x30) 12 = accV n9.mem (lcF sp0 + BitVec.ofNat 32 0x30) 12 :=
      lc_pt 12 fun t ht => by
        rw [← hM11, fillWords_outside 12 (bs 0xA8 (4 * 12) (0x30 + t) (by omega) (by decide) (by omega))]
    have hYhi : accV M17 (lcF sp0 + BitVec.ofNat 32 0x28) 2 = accV n9.mem (lcF sp0 + BitVec.ofNat 32 0x28) 2 :=
      lc_pt 2 fun t ht => m17 _ (by omega)
    -- `y` itself, before it
    have hY : accV M8 (lcF sp0 + BitVec.ofNat 32 0x30) 12 + 2 ^ 384 * accV M8 (lcF sp0 + BitVec.ofNat 32 0x28) 2 =
        accV n7.mem (lcF sp0 + BitVec.ofNat 32 0x30) 14 := by
      have h1 : accV M8 (lcF sp0 + BitVec.ofNat 32 0x30) 12 = accV n7.mem (lcF sp0 + BitVec.ofNat 32 0x30) 12 :=
        lc_pt 12 fun t ht => by
          rw [← hM8, memStore32_get_sep (lit 44 44 4 (0x30 + t) rfl (by omega) (by decide) (by omega)),
            memStore32_get_sep (lit 40 40 4 (0x30 + t) rfl (by omega) (by decide) (by omega))]
      have h2 : accV M8 (lcF sp0 + BitVec.ofNat 32 0x28) 2 =
          accV n7.mem (lcF sp0 + BitVec.ofNat 32 0x30 + BitVec.ofNat 32 (4 * 12)) 2 := by
        rw [accV_two, accV_two, ← hM8,
          show lcF sp0 + BitVec.ofNat 32 0x28 + 4 = lcF sp0 + 44 by rw [BitVec.add_assoc]; rfl,
          show lcF sp0 + BitVec.ofNat 32 0x28 = lcF sp0 + 40 from rfl, memLoad32_store32_same,
          memLoad32_store32_sep (sep_word_offsets _ 44 40 (.inr (by decide)) (by decide) (by decide)),
          memLoad32_store32_same]
        rw [show lcF sp0 + BitVec.ofNat 32 0x30 + BitVec.ofNat 32 (4 * 12) = lcF sp0 + 96 by rw [add_ofNat_assoc]; rfl,
          show lcF sp0 + 96 + 4 = lcF sp0 + 100 by rw [BitVec.add_assoc]; rfl]
      rw [h1, h2, ← accV_split]
    -- `x` itself
    have hX : accV n5.mem (lcF sp0 + BitVec.ofNat 32 0x68) 12 + 2 ^ 384 * accV n5.mem (lcF sp0 + BitVec.ofNat 32 0x98) 2
        = accV n5.mem (lcF sp0 + BitVec.ofNat 32 0x68) 14 := by
      rw [show lcF sp0 + BitVec.ofNat 32 0x98 = lcF sp0 + BitVec.ofNat 32 0x68 + BitVec.ofNat 32 (4 * 12) by
        rw [add_ofNat_assoc], ← accV_split]
    -- the two halves of the difference
    have hD1 : accV M20 (lcF sp0 + BitVec.ofNat 32 0x68) 12 = accV M14 (lcF sp0 + BitVec.ofNat 32 0xA8) 12 := by
      have h1 : accV M20 (lcF sp0 + BitVec.ofNat 32 0x68) 12 = accV M16 (lcF sp0 + BitVec.ofNat 32 0x68) 12 :=
        lc_pt 12 fun t ht => by
          rw [← hM20, memStore32_get_sep (lit 160 160 4 (0x68 + t) rfl (by omega) (by decide) (by omega)),
            memStore32_get_sep (lit 36 36 4 (0x68 + t) rfl (by omega) (by decide) (by omega)),
            memStore32_get_sep (lit 32 32 4 (0x68 + t) rfl (by omega) (by decide) (by omega)),
            f19 _ (b4 _ (by omega)) (bs 0xA0 8 _ (by omega) (by decide) (by omega)),
            ← hM17, memStore32_get_sep (lit 164 164 4 (0x68 + t) rfl (by omega) (by decide) (by omega)),
            memStore32_get_sep (lit 160 160 4 (0x68 + t) rfl (by omega) (by decide) (by omega))]
      rw [h1, ← hM16]
      exact accV_congr2 12 fun i hi => copyWords_load 12 i hi (by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega)
    have hD2 : accV M20 (lcF sp0 + BitVec.ofNat 32 0x20) 2 = accV M19 (lcF sp0 + BitVec.ofNat 32 0xA0) 2 := by
      rw [accV_two, accV_two, ← hM20,
        show lcF sp0 + BitVec.ofNat 32 0x20 + 4 = lcF sp0 + 36 by rw [BitVec.add_assoc]; rfl,
        show lcF sp0 + BitVec.ofNat 32 0x20 = lcF sp0 + 32 from rfl,
        memLoad32_store32_sep (sep_word_offsets _ 160 32 (.inr (by decide)) (by decide) (by decide)),
        memLoad32_store32_sep (sep_word_offsets _ 160 36 (.inr (by decide)) (by decide) (by decide)),
        memLoad32_store32_sep (sep_word_offsets _ 36 32 (.inr (by decide)) (by decide) (by decide)),
        memLoad32_store32_same, memLoad32_store32_same,
        show lcF sp0 + BitVec.ofNat 32 0xA0 + 4 = lcF sp0 + 164 by rw [BitVec.add_assoc]; rfl,
        show lcF sp0 + BitVec.ofNat 32 0xA0 = lcF sp0 + 160 from rfl]
    -- the products, in terms of the arguments
    have e0 : ∀ {M : Word → BitVec 8} {b : Word} {k : Nat}, (∀ x, Sep (lcR sp0) 0x1E0 x 1 → M x = m.mem x) →
        Sep b (4 * k) (lcR sp0) 0x1E0 → accV M b k = accV m.mem b k := fun hM hs =>
      accV_congr _ fun i hi => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact hM _ (hs.symm.subR (by omega))
    have cR8 : Sep cp (4 * 2) (lcR sp0) 0x1E0 := env.cR
    have dR8 : Sep dp (4 * 2) (lcR sp0) 0x1E0 := env.dR
    simp only [limbVal_wordsAt] at v1 b1 v3 b3
    rw [e0 frR0 cR8] at v1 b1
    rw [e0 frR1 dR8] at v3 b3
    have hx : accV n5.mem (lcF sp0 + BitVec.ofNat 32 0x68) 14 = accV m.mem ap 12 *
        (if accV m.mem cp 2 < 2 ^ 63 then accV m.mem cp 2 else 2 ^ 64 - accV m.mem cp 2) := by
      have h : accV n3.mem (lcF sp0 + BitVec.ofNat 32 8) 2 = accV n1.mem (lcF sp0 + BitVec.ofNat 32 8) 2 :=
        lc_pt 2 fun t ht => by
          rw [f3 _ (b20 _ (by omega)) (bs 0x14 9 _ (by omega) (by decide) (by omega))]
      rw [v5, e0 frR3 (aR48 : Sep ap (4 * 12) _ _), h, v1]
    have hy : accV n7.mem (lcF sp0 + BitVec.ofNat 32 0x30) 14 = accV m.mem bp 12 *
        (if accV m.mem dp 2 < 2 ^ 63 then accV m.mem dp 2 else 2 ^ 64 - accV m.mem dp 2) := by
      have h : accV M6 (lcF sp0 + BitVec.ofNat 32 0x14) 2 = accV n3.mem (lcF sp0 + BitVec.ofNat 32 0x14) 2 :=
        lc_pt 2 fun t ht => by
          rw [← hM6, memStore32_get_sep (lit 36 36 4 (0x14 + t) rfl (by omega) (by decide) (by omega)),
            memStore32_get_sep (lit 32 32 4 (0x14 + t) rfl (by omega) (by decide) (by omega)),
            f5 _ (b70 _ (by omega)) (bs 0x68 56 _ (by omega) (by decide) (by omega))]
      rw [v7, e0 frR6 (bR48 : Sep bp (4 * 12) _ _), h, v3]
    -- the sign bits
    have hxn : xn.toNat = ((m.mem (ap + 48)).toNat + (if accV m.mem cp 2 < 2 ^ 63 then 0 else 1)) % 2 := by
      rw [← hxn, xor_bits (by rw [ea]; exact hsa) (by rw [b1]; split <;> decide), ea, b1]
    have hyn : yn.toNat = ((m.mem (bp + 48)).toNat + (if accV m.mem dp 2 < 2 ^ 63 then 0 else 1)) % 2 := by
      rw [← hyn, xor_bits (by rw [eb]; exact hsb) (by rw [b3]; split <;> decide), eb, b3]
    -- what `out` holds
    have hOutLo : accV (memStore8 (memStore32 (memStore32 M23 (out + 48) (reg n23 9)) (out + 52) (reg n23 21))
        (out + 56) ((reg n23 8).extractLsb' 0 8)) out 12 = accV n21.mem (lcF sp0 + BitVec.ofNat 32 0x68) 12 := by
      rw [e48', e52, e56]
      have h1 : accV (memStore8 (memStore32 (memStore32 M23 (out + BitVec.ofNat 32 48) (reg n23 9))
          (out + BitVec.ofNat 32 52) (reg n23 21)) (out + BitVec.ofNat 32 56) ((reg n23 8).extractLsb' 0 8)) out 12 =
          accV M23 out 12 := accV_congr 12 fun i hi => by
        rw [memLoad32_store8_sep (sep_offsets out (.inr (by omega)) (by have := env.hwo; omega)
            (by have := env.hwo; omega)),
          memLoad32_store32_sep (sep_offsets out (.inr (by omega)) (by have := env.hwo; omega)
            (by have := env.hwo; omega)),
          memLoad32_store32_sep (sep_offsets out (.inr (by omega)) (by have := env.hwo; omega)
            (by have := env.hwo; omega))]
      rw [h1, ← hM23]
      exact accV_congr2 12 fun i hi => copyWords_load 12 i hi (by have := env.hwo; omega)
    have r9_23 : reg n23 9 = memLoad32 n21.mem (lcF sp0 + 32) := by
      rw [k2223 9 (by decide), g22]; simp +decide only [upd_app, ↓reduceIte]; rw [sp21]
    have r21_23 : reg n23 21 = memLoad32 n21.mem (lcF sp0 + 36) := by
      rw [k2223 21 (by decide), g22]; simp +decide only [upd_app, ↓reduceIte]; rw [sp21]
    have hOutHi : accV (memStore8 (memStore32 (memStore32 M23 (out + 48) (reg n23 9)) (out + 52) (reg n23 21))
        (out + 56) ((reg n23 8).extractLsb' 0 8)) (out + 48) 2 = accV n21.mem (lcF sp0 + BitVec.ofNat 32 0x20) 2 := by
      rw [accV_two, accV_two, e48', e52, e56,
        show out + BitVec.ofNat 32 48 + 4 = out + BitVec.ofNat 32 52 by rw [BitVec.add_assoc]; rfl,
        memLoad32_store8_sep (sep_offsets out (.inr (by decide)) (by have := env.hwo; omega)
          (by have := env.hwo; omega)),
        memLoad32_store8_sep (sep_offsets out (.inr (by decide)) (by have := env.hwo; omega)
          (by have := env.hwo; omega)),
        memLoad32_store32_same,
        memLoad32_store32_sep (sep_offsets out (.inr (by decide)) (by have := env.hwo; omega)
          (by have := env.hwo; omega)),
        memLoad32_store32_same, r9_23, r21_23,
        show lcF sp0 + BitVec.ofNat 32 0x20 + 4 = lcF sp0 + 36 by rw [BitVec.add_assoc]; rfl]
      rfl
    have hbyte : (memStore8 (memStore32 (memStore32 M23 (out + 48) (reg n23 9)) (out + 52) (reg n23 21))
        (out + 56) ((reg n23 8).extractLsb' 0 8) (out + 56)).toNat = (if sw = 1 then yn else xn).toNat := by
      have hsg : reg n23 8 = if sw = 1 then yn else xn := by
        rw [k2223 8 (by decide), g22]; simp +decide only [upd_app, ↓reduceIte]; rw [r8_21, r20_21, r19_21]
        exact signw hsw01 hxn01 hyn01
      have hsg01 : reg n23 8 = 0 ∨ reg n23 8 = 1 := by rw [hsg]; split <;> assumption
      have := choice_byte (memStore32 (memStore32 M23 (out + 48) (reg n23 9)) (out + 52) (reg n23 21)) (out + 56)
        (reg n23 8) hsg01
      rw [← hsg]
      generalize memStore8 (memStore32 (memStore32 M23 (out + 48) (reg n23 9)) (out + 52) (reg n23 21)) (out + 56)
        ((reg n23 8).extractLsb' 0 8) (out + 56) = b at this ⊢
      rw [← this, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
    -- the bits and their conditions
    have hb1 := mb_le1 (reg n14 24)
    have hb2 := mb_le1 b2
    have hsw1 : sw = 1 ↔ (xn.toNat ≠ yn.toNat ∧ maskBit b2 = 1) := by
      rw [← hsw, ← hon]
      rcases hxn01 with h1 | h1 <;> rcases hyn01 with h2 | h2 <;> rcases bm19 with h3 | h3 <;>
        (rw [h1, h2, h3]; decide)
    have hfl : (aluEval .and (aluEval .xor on 1) 0xFF = 1) ↔ xn.toNat = yn.toNat := by
      rw [hfl1, ← hon]
      rcases hxn01 with h1 | h1 <;> rcases hyn01 with h2 | h2 <;> (rw [h1, h2]; decide)
    have hxn1 : xn.toNat ≤ 1 := by rcases hxn01 with h | h <;> rw [h] <;> decide
    have hyn1 : yn.toNat ≤ 1 := by rcases hyn01 with h | h <;> rw [h] <;> decide
    have hselt : (if sw = 1 then yn else xn).toNat =
        if xn.toNat ≠ yn.toNat ∧ maskBit b2 = 1 then yn.toNat else xn.toNat := by
      by_cases h : sw = 1
      · rw [if_pos h, if_pos (hsw1.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hsw1.mpr h'))]
    -- the bounds
    have hC := accV_lt m.mem cp 2
    have hD := accV_lt m.mem dp 2
    have hA := accV_lt m.mem ap 12
    have hB := accV_lt m.mem bp 12
    have absle : ∀ {C : Nat}, C < 2 ^ (32 * 2) → (if C < 2 ^ 63 then C else 2 ^ 64 - C) ≤ 2 ^ 63 := fun h => by
      split <;> omega
    have hxlt : accV m.mem ap 12 * (if accV m.mem cp 2 < 2 ^ 63 then accV m.mem cp 2 else 2 ^ 64 - accV m.mem cp 2)
        < 2 ^ 447 := by
      have := Nat.mul_lt_mul_of_lt_of_le hA (absle hC) (Nat.two_pow_pos 63)
      rwa [← Nat.pow_add] at this
    have hylt : accV m.mem bp 12 * (if accV m.mem dp 2 < 2 ^ 63 then accV m.mem dp 2 else 2 ^ 64 - accV m.mem dp 2)
        < 2 ^ 447 := by
      have := Nat.mul_lt_mul_of_lt_of_le hB (absle hD) (Nat.two_pow_pos 63)
      rwa [← Nat.pow_add] at this
    have hD1lt := accV_lt M14 (lcF sp0 + BitVec.ofNat 32 0xA8) 12
    have hD2lt := accV_lt M19 (lcF sp0 + BitVec.ofNat 32 0xA0) 2
    -- the difference
    have hloop : accV m.mem ap 12 * (if accV m.mem cp 2 < 2 ^ 63 then accV m.mem cp 2 else 2 ^ 64 - accV m.mem cp 2)
        + 2 ^ 448 * maskBit b2 =
        (if xn.toNat = yn.toNat then (2 ^ 448 - accV m.mem bp 12 *
          (if accV m.mem dp 2 < 2 ^ 63 then accV m.mem dp 2 else 2 ^ 64 - accV m.mem dp 2)) % 2 ^ 448
         else accV m.mem bp 12 * (if accV m.mem dp 2 < 2 ^ 63 then accV m.mem dp 2 else 2 ^ 64 - accV m.mem dp 2)) +
        (accV M14 (lcF sp0 + BitVec.ofNat 32 0xA8) 12 + 2 ^ 384 * accV M19 (lcF sp0 + BitVec.ofNat 32 0xA0) 2) := by
      rw [← hx, ← hy, ← hX, ← hY, ← hXlo, ← hXhi]
      have hYp : accV M11 (lcF sp0 + BitVec.ofNat 32 0x30) 12 + 2 ^ 384 * accV M17 (lcF sp0 + BitVec.ofNat 32 0x28) 2
          = if xn.toNat = yn.toNat then
              (2 ^ 448 - (accV M8 (lcF sp0 + BitVec.ofNat 32 0x30) 12 +
                2 ^ 384 * accV M8 (lcF sp0 + BitVec.ofNat 32 0x28) 2)) % 2 ^ 448
            else accV M8 (lcF sp0 + BitVec.ofNat 32 0x30) 12 + 2 ^ 384 * accV M8 (lcF sp0 + BitVec.ofNat 32 0x28) 2 := by
        rw [hYlo, hYhi, v9]
        by_cases h : xn.toNat = yn.toNat
        · rw [if_pos (hfl.mpr h), if_pos h]
        · rw [if_neg (fun h' => h (hfl.mp h')), if_neg h]
      rw [← hYp]
      rw [show maskBit 0 = 0 from rfl, show (32 * 12 : Nat) = 384 from rfl] at v14
      rw [show (32 * 2 : Nat) = 64 from rfl] at v19
      omega
    have key := lc_math hxlt hylt hxn1 hyn1 (by omega) hb2 hloop
    rw [mem25]
    rw [hbyte]
    rw [hOutLo, hOutHi]
    rw [v21, hD1, hD2, hselt]
    have hif : ∀ (u v : Nat), (if sw = 1 then u else v) =
        if xn.toNat ≠ yn.toNat ∧ maskBit b2 = 1 then u else v := fun u v => by
      by_cases h : sw = 1
      · rw [if_pos h, if_pos (hsw1.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hsw1.mpr h'))]
    rw [hif, key, hxn, hyn, lc_sgn hsa hC, lc_sgn hsb hD]
  · rw [mem25, e48', e52, e56, memStore8_ne (fun e => ho.point (i := 56) (j := 0) (by decide) (by decide) (by
        rw [add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (ho.sub (c := 52) (l := 4) (by decide)), memStore32_get_sep (ho.sub (c := 48) (l := 4)
        (by decide)), ← hM23, copyWords_outside 12 (ho.sub (c := 0) (l := 4 * 12) (by decide) |> fun h => by
        rwa [add_ofNat_zero] at h), frR21 x hx]

end C3.RV32
