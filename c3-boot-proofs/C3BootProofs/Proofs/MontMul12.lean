import C3BootProofs.Proofs.FieldWideArith
import C3BootProofs.Proofs.FieldSub
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.MemsetAny

/-!
# P-384's Montgomery multiplication, as compiled

`crypto_bigint`'s `mul_montgomery_form::<12>` multiplies two 12-limb numbers
in Montgomery form with `montgomery_multiply_inner`: an outer loop over the
first operand's limbs, each pass adding that limb times the second operand
and one multiple of the modulus that clears the low limb, and shifting the
accumulator down a limb. A final `try_sub_with_carry` subtracts the modulus
once if needed, with `borrowing_sub` and `Uint<12>::select`.

`square_montgomery_form::<12>` compiles the same loop with other registers,
so the loop body is stated once, over its registers (`mmBody`).
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem mm_at_0 : fetchRel mulMont12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF60, 2) := by decide
theorem mm_at_2 : fetchRel mulMont12Code 0x2 = some (.auipc (5 : Fin 32) 0xD000, 4) := by decide
theorem mm_at_6 : fetchRel mulMont12Code 0x6 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFB98, 4) := by decide
theorem mm_at_a : fetchRel mulMont12Code 0xA = some (.alu .add (19 : Fin 32) x0 a4, 2) := by decide
theorem mm_at_c : fetchRel mulMont12Code 0xC = some (.alu .add (23 : Fin 32) x0 a3, 2) := by decide
theorem mm_at_e : fetchRel mulMont12Code 0xE = some (.alu .add (21 : Fin 32) x0 a2, 2) := by decide
theorem mm_at_10 : fetchRel mulMont12Code 0x10 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem mm_at_12 : fetchRel mulMont12Code 0x12 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem mm_at_14 : fetchRel mulMont12Code 0x14 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem mm_at_16 : fetchRel mulMont12Code 0x16 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem mm_at_1a : fetchRel mulMont12Code 0x1A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm_at_1c : fetchRel mulMont12Code 0x1C = some (.auipc ra 0xD000, 4) := by decide
theorem mm_at_20 : fetchRel mulMont12Code 0x20 = some (.jalr ra ra 0x2D8, 4) := by decide
theorem mm_at_24 : fetchRel mulMont12Code 0x24 = some (.auipc (5 : Fin 32) 0xD000, 4) := by decide
theorem mm_at_28 : fetchRel mulMont12Code 0x28 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0x1C, 4) := by decide
theorem mm_at_2c : fetchRel mulMont12Code 0x2C = some (.aluImm .add (5 : Fin 32) x0 0xC, 2) := by decide
theorem mm_at_2e : fetchRel mulMont12Code 0x2E = some (.branch .beq (5 : Fin 32) x0 0xB4, 4) := by decide
theorem mm_at_32 : fetchRel mulMont12Code 0x32 = some (.aluImm .sll a0 (29 : Fin 32) 0x2, 4) := by decide
theorem mm_at_36 : fetchRel mulMont12Code 0x36 = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem mm_at_38 : fetchRel mulMont12Code 0x38 = some (.load .lw (30 : Fin 32) a0 0x0, 4) := by decide
theorem mm_at_3c : fetchRel mulMont12Code 0x3C = some (.alu .mul a0 (6 : Fin 32) (30 : Fin 32), 4) := by decide
theorem mm_at_40 : fetchRel mulMont12Code 0x40 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem mm_at_42 : fetchRel mulMont12Code 0x42 = some (.alu .add a1 a1 a0, 2) := by decide
theorem mm_at_44 : fetchRel mulMont12Code 0x44 = some (.alu .mul (31 : Fin 32) (19 : Fin 32) a1, 4) := by decide
theorem mm_at_48 : fetchRel mulMont12Code 0x48 = some (.alu .mulhu a2 (6 : Fin 32) (30 : Fin 32), 4) := by decide
theorem mm_at_4c : fetchRel mulMont12Code 0x4C = some (.alu .mul a3 (31 : Fin 32) (7 : Fin 32), 4) := by decide
theorem mm_at_50 : fetchRel mulMont12Code 0x50 = some (.alu .mulhu (9 : Fin 32) (31 : Fin 32) (7 : Fin 32), 4) := by decide
theorem mm_at_54 : fetchRel mulMont12Code 0x54 = some (.alu .sltu a0 a1 a0, 4) := by decide
theorem mm_at_58 : fetchRel mulMont12Code 0x58 = some (.alu .add a0 a0 a2, 2) := by decide
theorem mm_at_5a : fetchRel mulMont12Code 0x5A = some (.alu .add a1 a1 a3, 2) := by decide
theorem mm_at_5c : fetchRel mulMont12Code 0x5C = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem mm_at_5e : fetchRel mulMont12Code 0x5E = some (.alu .sltu a2 a1 a3, 4) := by decide
theorem mm_at_62 : fetchRel mulMont12Code 0x62 = some (.aluImm .add (25 : Fin 32) x0 0xB, 2) := by decide
theorem mm_at_64 : fetchRel mulMont12Code 0x64 = some (.alu .add a2 a2 a0, 2) := by decide
theorem mm_at_66 : fetchRel mulMont12Code 0x66 = some (.alu .sltu a3 a0 (9 : Fin 32), 4) := by decide
theorem mm_at_6a : fetchRel mulMont12Code 0x6A = some (.alu .sltu a0 a2 a0, 4) := by decide
theorem mm_at_6e : fetchRel mulMont12Code 0x6E = some (.alu .add (26 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem mm_at_70 : fetchRel mulMont12Code 0x70 = some (.alu .add (24 : Fin 32) a3 a0, 4) := by decide
theorem mm_at_74 : fetchRel mulMont12Code 0x74 = some (.alu .add a3 x0 a6, 2) := by decide
theorem mm_at_76 : fetchRel mulMont12Code 0x76 = some (.alu .add (9 : Fin 32) x0 (21 : Fin 32), 2) := by decide
theorem mm_at_78 : fetchRel mulMont12Code 0x78 = some (.branch .beq (25 : Fin 32) x0 0x52, 4) := by decide
theorem mm_at_7c : fetchRel mulMont12Code 0x7C = some (.load .lw a4 (26 : Fin 32) 0x0, 4) := by decide
theorem mm_at_80 : fetchRel mulMont12Code 0x80 = some (.load .lw a5 (9 : Fin 32) 0x0, 2) := by decide
theorem mm_at_82 : fetchRel mulMont12Code 0x82 = some (.alu .mulhu a0 a4 (31 : Fin 32), 4) := by decide
theorem mm_at_86 : fetchRel mulMont12Code 0x86 = some (.alu .mul (8 : Fin 32) a5 (30 : Fin 32), 4) := by decide
theorem mm_at_8a : fetchRel mulMont12Code 0x8A = some (.alu .mul a4 a4 (31 : Fin 32), 4) := by decide
theorem mm_at_8e : fetchRel mulMont12Code 0x8E = some (.load .lw a1 a3 0x0, 2) := by decide
theorem mm_at_90 : fetchRel mulMont12Code 0x90 = some (.alu .mulhu a5 a5 (30 : Fin 32), 4) := by decide
theorem mm_at_94 : fetchRel mulMont12Code 0x94 = some (.alu .add a0 a0 (24 : Fin 32), 2) := by decide
theorem mm_at_96 : fetchRel mulMont12Code 0x96 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem mm_at_98 : fetchRel mulMont12Code 0x98 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem mm_at_9a : fetchRel mulMont12Code 0x9A = some (.alu .add a2 a2 a4, 2) := by decide
theorem mm_at_9c : fetchRel mulMont12Code 0x9C = some (.alu .sltu (8 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem mm_at_a0 : fetchRel mulMont12Code 0xA0 = some (.alu .sltu a4 a2 a4, 4) := by decide
theorem mm_at_a4 : fetchRel mulMont12Code 0xA4 = some (.alu .add a1 a1 a2, 2) := by decide
theorem mm_at_a6 : fetchRel mulMont12Code 0xA6 = some (.alu .add a5 a5 (8 : Fin 32), 2) := by decide
theorem mm_at_a8 : fetchRel mulMont12Code 0xA8 = some (.alu .add a0 a0 a4, 2) := by decide
theorem mm_at_aa : fetchRel mulMont12Code 0xAA = some (.alu .sltu a2 a1 a2, 4) := by decide
theorem mm_at_ae : fetchRel mulMont12Code 0xAE = some (.alu .add a5 a5 a0, 2) := by decide
theorem mm_at_b0 : fetchRel mulMont12Code 0xB0 = some (.store .sw a3 a1 0xFFFFFFFC, 4) := by decide
theorem mm_at_b4 : fetchRel mulMont12Code 0xB4 = some (.alu .add a2 a2 a5, 2) := by decide
theorem mm_at_b6 : fetchRel mulMont12Code 0xB6 = some (.alu .sltu (24 : Fin 32) a5 a0, 4) := by decide
theorem mm_at_ba : fetchRel mulMont12Code 0xBA = some (.alu .sltu a0 a2 a5, 4) := by decide
theorem mm_at_be : fetchRel mulMont12Code 0xBE = some (.aluImm .add a3 a3 0x4, 2) := by decide
theorem mm_at_c0 : fetchRel mulMont12Code 0xC0 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a0, 2) := by decide
theorem mm_at_c2 : fetchRel mulMont12Code 0xC2 = some (.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x4, 2) := by decide
theorem mm_at_c4 : fetchRel mulMont12Code 0xC4 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem mm_at_c6 : fetchRel mulMont12Code 0xC6 = some (.branch .bne (25 : Fin 32) x0 0xFFFFFFB6, 4) := by decide
theorem mm_at_ca : fetchRel mulMont12Code 0xCA = some (.alu .add (22 : Fin 32) (22 : Fin 32) a2, 2) := by decide
theorem mm_at_cc : fetchRel mulMont12Code 0xCC = some (.alu .add a0 (24 : Fin 32) (28 : Fin 32), 4) := by decide
theorem mm_at_d0 : fetchRel mulMont12Code 0xD0 = some (.alu .sltu a1 (22 : Fin 32) a2, 4) := by decide
theorem mm_at_d4 : fetchRel mulMont12Code 0xD4 = some (.store .sw sp (22 : Fin 32) 0x38, 2) := by decide
theorem mm_at_d6 : fetchRel mulMont12Code 0xD6 = some (.alu .add (22 : Fin 32) a0 a1, 4) := by decide
theorem mm_at_da : fetchRel mulMont12Code 0xDA = some (.aluImm .add (29 : Fin 32) (29 : Fin 32) 0x1, 2) := by decide
theorem mm_at_dc : fetchRel mulMont12Code 0xDC = some (.aluImm .add (28 : Fin 32) x0 0x0, 2) := by decide
theorem mm_at_de : fetchRel mulMont12Code 0xDE = some (.branch .bne (29 : Fin 32) (5 : Fin 32) 0xFFFFFF54, 4) := by decide
theorem mm_at_e2 : fetchRel mulMont12Code 0xE2 = some (.aluImm .add a0 sp 0x3C, 2) := by decide
theorem mm_at_e4 : fetchRel mulMont12Code 0xE4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem mm_at_e8 : fetchRel mulMont12Code 0xE8 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm_at_ea : fetchRel mulMont12Code 0xEA = some (.aluImm .add (19 : Fin 32) sp 0x3C, 4) := by decide
theorem mm_at_ee : fetchRel mulMont12Code 0xEE = some (.auipc ra 0xD000, 4) := by decide
theorem mm_at_f2 : fetchRel mulMont12Code 0xF2 = some (.jalr ra ra 0x206, 4) := by decide
theorem mm_at_f6 : fetchRel mulMont12Code 0xF6 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem mm_at_f8 : fetchRel mulMont12Code 0xF8 = some (.aluImm .add (9 : Fin 32) sp 0xC, 2) := by decide
theorem mm_at_fa : fetchRel mulMont12Code 0xFA = some (.aluImm .add (8 : Fin 32) x0 0xC, 2) := by decide
theorem mm_at_fc : fetchRel mulMont12Code 0xFC = some (.branch .beq (8 : Fin 32) x0 0x20, 2) := by decide
theorem mm_at_fe : fetchRel mulMont12Code 0xFE = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem mm_at_100 : fetchRel mulMont12Code 0x100 = some (.load .lw a1 (23 : Fin 32) 0x0, 4) := by decide
theorem mm_at_104 : fetchRel mulMont12Code 0x104 = some (.auipc ra 0xFFFF0000, 4) := by decide
theorem mm_at_108 : fetchRel mulMont12Code 0x108 = some (.jalr ra ra 0xFFFFFE86, 4) := by decide
theorem mm_at_10c : fetchRel mulMont12Code 0x10C = some (.alu .add a2 x0 a1, 2) := by decide
theorem mm_at_10e : fetchRel mulMont12Code 0x10E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem mm_at_110 : fetchRel mulMont12Code 0x110 = some (.store .sw (19 : Fin 32) a0 0x0, 4) := by decide
theorem mm_at_114 : fetchRel mulMont12Code 0x114 = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem mm_at_116 : fetchRel mulMont12Code 0x116 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x4, 2) := by decide
theorem mm_at_118 : fetchRel mulMont12Code 0x118 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem mm_at_11a : fetchRel mulMont12Code 0x11A = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem mm_at_11c : fetchRel mulMont12Code 0x11C = some (.store .sw sp (22 : Fin 32) 0x6C, 2) := by decide
theorem mm_at_11e : fetchRel mulMont12Code 0x11E = some (.aluImm .add a0 sp 0x6C, 2) := by decide
theorem mm_at_120 : fetchRel mulMont12Code 0x120 = some (.load .lw a0 sp 0x6C, 2) := by decide
theorem mm_at_122 : fetchRel mulMont12Code 0x122 = some (.aluImm .sltu (9 : Fin 32) a0 0x1, 4) := by decide
theorem mm_at_126 : fetchRel mulMont12Code 0x126 = some (.alu .and (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem mm_at_128 : fetchRel mulMont12Code 0x128 = some (.store .sb sp (9 : Fin 32) 0x6C, 4) := by decide
theorem mm_at_12c : fetchRel mulMont12Code 0x12C = some (.aluImm .add a0 sp 0x6C, 2) := by decide
theorem mm_at_12e : fetchRel mulMont12Code 0x12E = some (.load .lbu a0 sp 0x6C, 4) := by decide
theorem mm_at_132 : fetchRel mulMont12Code 0x132 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem mm_at_134 : fetchRel mulMont12Code 0x134 = some (.alu .and a2 a2 a0, 2) := by decide
theorem mm_at_136 : fetchRel mulMont12Code 0x136 = some (.alu .add a0 x0 (22 : Fin 32), 2) := by decide
theorem mm_at_138 : fetchRel mulMont12Code 0x138 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem mm_at_13a : fetchRel mulMont12Code 0x13A = some (.auipc ra 0xFFFF0000, 4) := by decide
theorem mm_at_13e : fetchRel mulMont12Code 0x13E = some (.jalr ra ra 0xFFFFFE50, 4) := by decide
theorem mm_at_142 : fetchRel mulMont12Code 0x142 = some (.aluImm .add a1 sp 0x3C, 2) := by decide
theorem mm_at_144 : fetchRel mulMont12Code 0x144 = some (.aluImm .add a2 sp 0xC, 2) := by decide
theorem mm_at_146 : fetchRel mulMont12Code 0x146 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem mm_at_148 : fetchRel mulMont12Code 0x148 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem mm_at_14a : fetchRel mulMont12Code 0x14A = some (.auipc ra 0x0, 4) := by decide
theorem mm_at_14e : fetchRel mulMont12Code 0x14E = some (.jalr ra ra 0x14, 4) := by decide
theorem mm_at_152 : fetchRel mulMont12Code 0x152 = some (.auipc (5 : Fin 32) 0xD000, 4) := by decide
theorem mm_at_156 : fetchRel mulMont12Code 0x156 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFA96, 4) := by decide
theorem mm_at_15a : fetchRel mulMont12Code 0x15A = some (.aluImm .add sp sp 0xA0, 2) := by decide
theorem mm_at_15c : fetchRel mulMont12Code 0x15C = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- One column of the compiled Montgomery loop, as the instructions compute
it: the word stored, then the two-word carry out. -/
def mmCols (N Y O U X CL CH : Word) : Word × Word × Word :=
  let th0 := aluEval .mulhu N U
  let tl0 := aluEval .mul Y X
  let tn1 := aluEval .mul N U
  let ty1 := aluEval .mulhu Y X
  let th1 := aluEval .add th0 CH
  let ta1 := aluEval .add O tl0
  let cl1 := aluEval .add CL tn1
  let tl1 := aluEval .sltu ta1 tl0
  let tn2 := aluEval .sltu cl1 tn1
  let ta2 := aluEval .add ta1 cl1
  let ty2 := aluEval .add ty1 tl1
  let th2 := aluEval .add th1 tn2
  let cl2 := aluEval .sltu ta2 cl1
  let ty3 := aluEval .add ty2 th2
  let cl3 := aluEval .add cl2 ty3
  let ch1 := aluEval .sltu ty3 th2
  let th3 := aluEval .sltu cl3 ty3
  (ta2, cl3, aluEval .add ch1 th3)

theorem add_toNat (x y : Word) : (aluEval .add x y).toNat = (x.toNat + y.toNat) % 2 ^ 32 := by
  show (x + y).toNat = _; rw [BitVec.toNat_add]

theorem carry_le1 {s a c : Word} (h : s.toNat + 2 ^ 32 * c.toNat = a.toNat + a.toNat) : c.toNat ≤ 1 := by
  have := s.isLt; have := a.isLt; omega

set_option maxHeartbeats 2000000 in
theorem mm_step (N Y O U X CL CH : Word) (hc : CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2) :
    (mmCols N Y O U X CL CH).1.toNat + 2 ^ 32 * ((mmCols N Y O U X CL CH).2.1.toNat +
        2 ^ 32 * (mmCols N Y O U X CL CH).2.2.toNat) =
      X.toNat * Y.toNat + O.toNat + U.toNat * N.toNat + CL.toNat + 2 ^ 32 * CH.toNat ∧
    (mmCols N Y O U X CL CH).2.1.toNat + 2 ^ 32 * (mmCols N Y O U X CL CH).2.2.toNat ≤ 2 * 2 ^ 32 - 2 := by
  unfold mmCols
  simp only
  have e0 := mul_mulhu N U
  have e1 := mul_mulhu Y X
  have e2 := add_carry O (aluEval .mul Y X)
  have e3 := add_carry CL (aluEval .mul N U)
  have a1 := add_toNat (aluEval .mulhu N U) CH
  generalize aluEval .mulhu N U = th0 at e0 a1 ⊢
  generalize aluEval .mul Y X = tl0 at e1 e2 ⊢
  generalize aluEval .mul N U = tn1 at e0 e3 ⊢
  generalize aluEval .mulhu Y X = ty1 at e1 ⊢
  generalize aluEval .add th0 CH = th1 at a1 ⊢
  generalize aluEval .add O tl0 = ta1 at e2 ⊢
  generalize aluEval .add CL tn1 = cl1 at e3 ⊢
  generalize aluEval .sltu ta1 tl0 = tl1 at e2 ⊢
  generalize aluEval .sltu cl1 tn1 = tn2 at e3 ⊢
  have e4 := add_carry ta1 cl1
  have a2 := add_toNat ty1 tl1
  have a3 := add_toNat th1 tn2
  generalize aluEval .add ta1 cl1 = ta2 at e4 ⊢
  generalize aluEval .add ty1 tl1 = ty2 at a2 ⊢
  generalize aluEval .add th1 tn2 = th2 at a3 ⊢
  generalize aluEval .sltu ta2 cl1 = cl2 at e4 ⊢
  have e5 := add_carry ty2 th2
  generalize aluEval .add ty2 th2 = ty3 at e5 ⊢
  have e6 := add_carry cl2 ty3
  generalize aluEval .add cl2 ty3 = cl3 at e6 ⊢
  generalize aluEval .sltu ty3 th2 = ch1 at e5 ⊢
  generalize aluEval .sltu cl3 ty3 = th3 at e6 ⊢
  have a4 := add_toNat ch1 th3
  generalize aluEval .add ch1 th3 = ch2 at a4 ⊢
  have hN := N.isLt; have hY := Y.isLt; have hU := U.isLt; have hX := X.isLt
  have P1 : N.toNat * U.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have P2 : Y.toNat * X.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.mul_comm X.toNat Y.toNat, Nat.mul_comm U.toNat N.toNat]
  generalize N.toNat * U.toNat = p1 at e0 P1 ⊢
  generalize Y.toNat * X.toNat = p2 at e1 P2 ⊢
  have := th0.isLt; have := tl0.isLt; have := tn1.isLt; have := ty1.isLt; have := th1.isLt; have := ta1.isLt
  have := cl1.isLt; have := tl1.isLt; have := tn2.isLt; have := ta2.isLt; have := ty2.isLt; have := th2.isLt
  have := cl2.isLt; have := ty3.isLt; have := cl3.isLt; have := ch1.isLt; have := th3.isLt; have := ch2.isLt
  have := O.isLt; have := CL.isLt; have := CH.isLt
  have hth0 : th0.toNat ≤ 2 ^ 32 - 2 := by omega
  have hty1 : ty1.toNat ≤ 2 ^ 32 - 2 := by omega
  have hCH : CH.toNat ≤ 1 := by omega
  have h1 : th1.toNat = th0.toNat + CH.toNat := by rw [a1]; exact Nat.mod_eq_of_lt (by omega)
  have htl1 : tl1.toNat ≤ 1 := by omega
  have htn2 : tn2.toNat ≤ 1 := by omega
  have hcl2 : cl2.toNat ≤ 1 := by omega
  have h2 : ty2.toNat = ty1.toNat + tl1.toNat := by rw [a2]; exact Nat.mod_eq_of_lt (by omega)
  have hsum : tn2.toNat + th0.toNat + CH.toNat ≤ 2 ^ 32 - 1 := by omega
  have h3 : th2.toNat = th1.toNat + tn2.toNat := by rw [a3]; exact Nat.mod_eq_of_lt (by omega)
  have hch1 : ch1.toNat ≤ 1 := by omega
  have hth3 : th3.toNat ≤ 1 := by omega
  have h4 : ch2.toNat = ch1.toNat + th3.toNat := by rw [a4]; exact Nat.mod_eq_of_lt (by omega)
  rw [h4]
  constructor
  · omega
  · omega

/-- The first column of a pass of the compiled Montgomery loop: the factor
`u`, then the two-word carry out. The column's own word is zero. -/
def mmHead (Y0 X O0 K N0 : Word) : Word × Word × Word :=
  let a0 := aluEval .mul Y0 X
  let a1 := aluEval .add O0 a0
  let u := aluEval .mul K a1
  let a2 := aluEval .mulhu Y0 X
  let a3 := aluEval .mul u N0
  let s1 := aluEval .mulhu u N0
  let c1 := aluEval .sltu a1 a0
  let h1 := aluEval .add c1 a2
  let lo := aluEval .add a1 a3
  let h2 := aluEval .add h1 s1
  let c2 := aluEval .sltu lo a3
  let cl := aluEval .add c2 h2
  let o1 := aluEval .sltu h2 s1
  let o2 := aluEval .sltu cl h2
  (u, cl, aluEval .add o1 o2)

theorem mont_low {s k n : Nat} (h : (k * n + 1) % 2 ^ 32 = 0) : (s + k * s % 2 ^ 32 * n % 2 ^ 32) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod (k * s % 2 ^ 32) n, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    show s + k * s * n = s * (k * n + 1) by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm s, Nat.mul_assoc,
      Nat.mul_comm s n, ← Nat.mul_assoc, Nat.add_comm], Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

set_option maxHeartbeats 2000000 in
theorem mm_head (Y0 X O0 K N0 : Word) (hk : (K.toNat * N0.toNat + 1) % 2 ^ 32 = 0) :
    X.toNat * Y0.toNat + O0.toNat + (mmHead Y0 X O0 K N0).1.toNat * N0.toNat =
      2 ^ 32 * ((mmHead Y0 X O0 K N0).2.1.toNat + 2 ^ 32 * (mmHead Y0 X O0 K N0).2.2.toNat) ∧
    (mmHead Y0 X O0 K N0).2.1.toNat + 2 ^ 32 * (mmHead Y0 X O0 K N0).2.2.toNat ≤ 2 * 2 ^ 32 - 2 := by
  unfold mmHead
  simp only
  have e1 := mul_mulhu Y0 X
  have e2 := add_carry O0 (aluEval .mul Y0 X)
  have hu : (aluEval .mul K (aluEval .add O0 (aluEval .mul Y0 X))).toNat =
      K.toNat * (aluEval .add O0 (aluEval .mul Y0 X)).toNat % 2 ^ 32 := by
    show (K * _).toNat = _; rw [BitVec.toNat_mul]
  have e3 := mul_mulhu (aluEval .mul K (aluEval .add O0 (aluEval .mul Y0 X))) N0
  have hlun : (aluEval .mul (aluEval .mul K (aluEval .add O0 (aluEval .mul Y0 X))) N0).toNat =
      (aluEval .mul K (aluEval .add O0 (aluEval .mul Y0 X))).toNat * N0.toNat % 2 ^ 32 := by
    show (_ * N0).toNat = _; rw [BitVec.toNat_mul]
  generalize aluEval .mul Y0 X = a0 at e1 e2 hu hlun e3 ⊢
  generalize aluEval .add O0 a0 = a1 at e2 hu hlun e3 ⊢
  generalize aluEval .mul K a1 = u at hu hlun e3 ⊢
  generalize aluEval .mulhu Y0 X = a2 at e1 ⊢
  generalize aluEval .mul u N0 = a3 at e3 hlun ⊢
  generalize aluEval .mulhu u N0 = s1 at e3 ⊢
  generalize aluEval .sltu a1 a0 = c1 at e2 ⊢
  have b1 := add_toNat c1 a2
  generalize aluEval .add c1 a2 = h1 at b1 ⊢
  have e4 := add_carry a1 a3
  generalize aluEval .add a1 a3 = lo at e4 ⊢
  have e5 := add_carry h1 s1
  generalize aluEval .add h1 s1 = h2 at e5 ⊢
  generalize aluEval .sltu lo a3 = c2 at e4 ⊢
  have e6 := add_carry c2 h2
  generalize aluEval .add c2 h2 = cl at e6 ⊢
  generalize aluEval .sltu h2 s1 = o1 at e5 ⊢
  generalize aluEval .sltu cl h2 = o2 at e6 ⊢
  have b2 := add_toNat o1 o2
  generalize aluEval .add o1 o2 = ch at b2 ⊢
  have hlo : lo.toNat = 0 := by
    have h0 := mont_low (s := a1.toNat) hk
    rw [← hu, ← hlun] at h0
    have := lo.isLt; have := a1.isLt; have := a3.isLt
    have : lo.toNat = (a1.toNat + a3.toNat) % 2 ^ 32 := by omega
    omega
  have hY := Y0.isLt; have hX := X.isLt; have hN := N0.isLt; have hU := u.isLt
  have P1 : Y0.toNat * X.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have P2 : u.toNat * N0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [Nat.mul_comm X.toNat Y0.toNat]
  generalize Y0.toNat * X.toNat = p1 at e1 P1 ⊢
  generalize u.toNat * N0.toNat = p2 at e3 P2 hlun ⊢
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt; have := s1.isLt; have := c1.isLt
  have := h1.isLt; have := h2.isLt; have := c2.isLt; have := cl.isLt; have := o1.isLt; have := o2.isLt
  have := ch.isLt; have := O0.isLt
  have ha2 : a2.toNat ≤ 2 ^ 32 - 2 := by omega
  have hc1 : c1.toNat ≤ 1 := by omega
  have hh1 : h1.toNat = c1.toNat + a2.toNat := by rw [b1]; exact Nat.mod_eq_of_lt (by omega)
  have ho1 : o1.toNat ≤ 1 := by omega
  have ho2 : o2.toNat ≤ 1 := by omega
  have hch : ch.toNat = o1.toNat + o2.toNat := by rw [b2]; exact Nat.mod_eq_of_lt (by omega)
  rw [hch]
  constructor
  · omega
  · omega


/-- One pass of the inner loop, over its registers: the modulus pointer
`pn`, the second operand's pointer `py`, the accumulator pointer `po`, the
factor `u`, the first operand's limb `xi`, the carry `cl` and `ch`, the
count `cnt`, and five scratch registers. -/
def mmBody (pn py po u xi cl ch cnt tn ty th tl ta : Fin 32) : List BInstr :=
  [.lw tn pn 0, .lw ty py 0, .alu .mulhu th tn u, .alu .mul tl ty xi, .alu .mul tn tn u, .lw ta po 0,
   .alu .mulhu ty ty xi, .alu .add th th ch, .aluImm .add py py 4, .alu .add ta ta tl, .alu .add cl cl tn,
   .alu .sltu tl ta tl, .alu .sltu tn cl tn, .alu .add ta ta cl, .alu .add ty ty tl, .alu .add th th tn,
   .alu .sltu cl ta cl, .alu .add ty ty th, .sw po ta 0xFFFFFFFC, .alu .add cl cl ty, .alu .sltu ch ty th,
   .alu .sltu th cl ty, .aluImm .add po po 4, .alu .add ch ch th, .aluImm .add pn pn 4,
   .aluImm .add cnt cnt 0xFFFFFFFF]

/-- The loop body in `mul_montgomery_form::<12>`. -/
abbrev mmBodyM : List BInstr :=
  mmBody (26 : Fin 32) (9 : Fin 32) a3 (31 : Fin 32) (30 : Fin 32) a2 (24 : Fin 32) (25 : Fin 32) a4 a5 a0
    (8 : Fin 32) a1

section
set_option maxRecDepth 20000
theorem mmBodyM_end : blockEnd mulMont12Code 0x7C mmBodyM = some 0xC6 := by decide
end

set_option maxRecDepth 20000 in
theorem mmBodyM_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmBodyM (M, f)).1 = memStore32 M (f a3 + 0xFFFFFFFC)
        (mmCols (memLoad32 M (f (26 : Fin 32) + 0)) (memLoad32 M (f (9 : Fin 32) + 0)) (memLoad32 M (f a3 + 0))
          (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2) (f (24 : Fin 32))).1 ∧
    (runBlock mmBodyM (M, f)).2 a2 = (mmCols (memLoad32 M (f (26 : Fin 32) + 0)) (memLoad32 M (f (9 : Fin 32) + 0))
        (memLoad32 M (f a3 + 0)) (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2) (f (24 : Fin 32))).2.1 ∧
    (runBlock mmBodyM (M, f)).2 (24 : Fin 32) = (mmCols (memLoad32 M (f (26 : Fin 32) + 0))
        (memLoad32 M (f (9 : Fin 32) + 0)) (memLoad32 M (f a3 + 0)) (f (31 : Fin 32)) (f (30 : Fin 32)) (f a2)
        (f (24 : Fin 32))).2.2 ∧
    (runBlock mmBodyM (M, f)).2 (26 : Fin 32) = f (26 : Fin 32) + 4 ∧
    (runBlock mmBodyM (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock mmBodyM (M, f)).2 a3 = f a3 + 4 ∧
    (runBlock mmBodyM (M, f)).2 (25 : Fin 32) = f (25 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (26 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a3 → q ≠ a2 → q ≠ (24 : Fin 32) → q ≠ (25 : Fin 32) →
      q ≠ a4 → q ≠ a5 → q ≠ a0 → q ≠ (8 : Fin 32) → q ≠ a1 → (runBlock mmBodyM (M, f)).2 q = f q := by
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

theorem mmBodyM_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hn : (f (26 : Fin 32) + 0).toNat % 4 = 0) (hy : (f (9 : Fin 32) + 0).toNat % 4 = 0)
    (ho : (f a3 + 0).toNat % 4 = 0) (hs : (f a3 + 0xFFFFFFFC).toNat % 4 = 0)
    (hsep : Sep (f a3 + 0xFFFFFFFC) 4 base len) : BlockOk base len mmBodyM (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmBody, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hn, hy, ho, hs, hsep⟩

theorem back4 (a : Word) (k : Nat) :
    a + BitVec.ofNat 32 (4 * (k + 1)) + 0xFFFFFFFC = a + BitVec.ofNat 32 (4 * k) := by
  have e : BitVec.ofNat 32 (4 * (k + 1)) + 0xFFFFFFFC = BitVec.ofNat 32 (4 * k) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    show (4 * (k + 1) % 2 ^ 32 + 0xFFFFFFFC) % 2 ^ 32 = _
    omega
  rw [BitVec.add_assoc, e]

theorem cnt11_dec : ∀ k : Nat, k < 11 → BitVec.ofNat 32 (11 - k) + 0xFFFFFFFF = BitVec.ofNat 32 (11 - (k + 1)) := by
  decide

theorem cnt11_ne : ∀ k : Nat, k < 11 → (BitVec.ofNat 32 (11 - (k + 1)) != 0) = decide (k + 1 < 11) := by decide

theorem pkeep_ne {p : Fin 32 → Bool} {q r : Fin 32} (h : p q = true) (hr : p r = false) : q ≠ r :=
  fun e => by rw [e, hr] at h; exact Bool.false_ne_true h

/-- The registers the loop body leaves alone. -/
def bodyKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26]

theorem ptr4 (b : Word) (k : Nat) : b + BitVec.ofNat 32 (4 * k) + 4 = b + BitVec.ofNat 32 (4 * (k + 1)) := by
  rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2

/-- **One pass of the inner loop**, from 0x7C: column `k + 1` of a pass,
which stores the accumulator's word `k`. -/
theorem mm_iter {M : Word → BitVec 8} {B np yp acc U X CL CH : Word} {n : Machine} {k : Nat}
    (s : St M B n 0x7C (reg n)) (hc : CodeIn M B mulMont12Code) (hk : k < 11)
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hS : Sep (acc + BitVec.ofNat 32 (4 * k)) 4 B mulMont12Code.length)
    (r26 : reg n (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)))
    (r9 : reg n (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 1)))
    (ra3 : reg n a3 = acc + BitVec.ofNat 32 (4 * (k + 1)))
    (r31 : reg n (31 : Fin 32) = U) (r30 : reg n (30 : Fin 32) = X) (ra2 : reg n a2 = CL)
    (r24 : reg n (24 : Fin 32) = CH) (r25 : reg n (25 : Fin 32) = BitVec.ofNat 32 (11 - k)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (acc + BitVec.ofNat 32 (4 * k))
        (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1))))
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) U X CL CH).1)
        B n' (if k + 1 < 11 then 0x7C else 0xCA) (reg n') ∧
      reg n' a2 = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n' (24 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n' (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a3 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (25 : Fin 32) = BitVec.ofNat 32 (11 - (k + 1)) ∧
      ∀ q, bodyKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have ok := mmBodyM_ok (M := M) (f := reg n) (base := B) (len := mulMont12Code.length)
    (by rw [r26, add_lit_zero]; exact aligned_add hnp (by omega))
    (by rw [r9, add_lit_zero]; exact aligned_add hyp (by omega))
    (by rw [ra3, add_lit_zero]; exact aligned_add hacc (by omega))
    (by rw [ra3, back4 acc k]; exact aligned_add hacc (by omega))
    (by rw [ra3, back4 acc k]; exact hS)
  obtain ⟨n1, c1, u1⟩ := St.block mmBodyM s hc mmBodyM_end ok
  obtain ⟨em, e2, e24, e26, e9, e3, e25, fr⟩ := mmBodyM_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em, r26, r9, ra3, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero, back4 acc k] at u1'
  have g : ∀ q, reg n1 q = (runBlock mmBodyM (M, reg n)).2 q := u1.regs
  have hb : branchTaken .bne (reg n1 (25 : Fin 32)) (reg n1 x0) = decide (k + 1 < 11) := by
    rw [g, e25, r25, cnt11_dec k hk, u1'.zero]; exact cnt11_ne k hk
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
      reg n2 (25 : Fin 32) = BitVec.ofNat 32 (11 - (k + 1)) ∧
      ∀ q, bodyKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h2, g, e2, r26, r9, ra3, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e24, r26, r9, ra3, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e26, r26, ptr4]
    · rw [h2, g, e9, r9, ptr4]
    · rw [h2, g, e3, ra3, ptr4]
    · rw [h2, g, e25, r25, cnt11_dec k hk]
    · rw [h2, g]
      exact fr q (pkeep_ne (r := 26) hq rfl) (pkeep_ne (r := 9) hq rfl) (pkeep_ne (r := a3) hq rfl)
        (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := 24) hq rfl) (pkeep_ne (r := 25) hq rfl)
        (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := a0) hq rfl)
        (pkeep_ne (r := 8) hq rfl) (pkeep_ne (r := a1) hq rfl)
  by_cases hl : k + 1 < 11
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x7C mm_at_c6 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0xCA mm_at_c6 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

theorem mm_inner_arith {Ak lo C C' P B X U y o nn Y O N : Nat}
    (h1 : B * Ak + C * (P * B) = X * Y + O + U * N) (h2 : lo + B * C' = X * y + o + U * nn + C) :
    B * (Ak + lo * P) + C' * (P * B * B) = X * (Y + y * (P * B)) + (O + o * (P * B)) + U * (N + nn * (P * B)) := by
  have e2 : (lo + B * C') * (P * B) = (X * y + o + U * nn + C) * (P * B) := by rw [h2]
  simp only [Nat.add_mul, Nat.mul_add] at e2 ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at h1 e2 ⊢
  omega

theorem load_frame {M M0 : Word → BitVec 8} {acc b : Word} {n : Nat} (hf : ∀ a, Sep acc n a 1 → M a = M0 a)
    (hs : Sep acc n b 4) : memLoad32 M b = memLoad32 M0 b :=
  memLoad32_congr fun q hq => hf _ (hs.subR (c := q) (l := 1) (by omega))

theorem pow32_succ (k : Nat) : 2 ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 := by
  rw [Nat.mul_succ, Nat.pow_add]

/-- What one inner-loop pass does to the pass's sum: column `k + 1` moves
from the inputs into the stored words and the carry. -/
theorem mm_inv_step {M M0 : Word → BitVec 8} {acc yp np U X CL CH lo cl ch : Word} {k : Nat} (hk : k < 11)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAY : Sep acc 48 yp 48) (hAN : Sep acc 48 np 48)
    (hfr : ∀ a, Sep acc 48 a 1 → M a = M0 a)
    (hab : ∀ i, k ≤ i → i < 12 →
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
    (∀ a, Sep acc 48 a 1 → memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo a = M0 a) ∧
    (∀ i, k + 1 ≤ i → i < 12 → memLoad32 (memStore32 M (acc + BitVec.ofNat 32 (4 * k)) lo)
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

/-- **The inner loop**, from column `k + 1` of a pass to its end at 0xCA:
columns `k + 1..11` of the pass. -/
theorem mm_inner {B acc yp np U X : Word} {M0 : Word → BitVec 8}
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0) (hw : acc.toNat + 48 ≤ 2 ^ 32)
    (hAY : Sep acc 48 yp 48) (hAN : Sep acc 48 np 48) (hAC : Sep acc 48 B mulMont12Code.length) :
    ∀ m k, k + m + 1 = 11 → ∀ {M : Word → BitVec 8} {n : Machine} {CL CH : Word},
      St M B n 0x7C (reg n) → CodeIn M B mulMont12Code →
      (∀ a, Sep acc 48 a 1 → M a = M0 a) →
      (∀ i, k ≤ i → i < 12 →
        memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) →
      2 ^ 32 * accV M acc k + (CL.toNat + 2 ^ 32 * CH.toNat) * 2 ^ (32 * (k + 1)) =
        X.toNat * accV M0 yp (k + 1) + accV M0 acc (k + 1) + U.toNat * accV M0 np (k + 1) →
      CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2 →
      reg n (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a3 = acc + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (31 : Fin 32) = U → reg n (30 : Fin 32) = X → reg n a2 = CL → reg n (24 : Fin 32) = CH →
      reg n (25 : Fin 32) = BitVec.ofNat 32 (11 - k) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0xCA (reg n') ∧ CodeIn M' B mulMont12Code ∧
        2 ^ 32 * accV M' acc 11 + ((reg n' a2).toNat + 2 ^ 32 * (reg n' (24 : Fin 32)).toNat) * 2 ^ (32 * 12) =
          X.toNat * accV M0 yp 12 + accV M0 acc 12 + U.toNat * accV M0 np 12 ∧
        (reg n' a2).toNat + 2 ^ 32 * (reg n' (24 : Fin 32)).toNat ≤ 2 * 2 ^ 32 - 2 ∧
        (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
        memLoad32 M' (acc + BitVec.ofNat 32 (4 * 11)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * 11)) ∧
        reg n' (26 : Fin 32) = np + BitVec.ofNat 32 (4 * 12) ∧
        reg n' (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * 12) ∧
        reg n' a3 = acc + BitVec.ofNat 32 (4 * 12) ∧
        reg n' (25 : Fin 32) = 0 ∧
        ∀ q, bodyKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r26 r9 ra3 r31 r30 ra2 r24 r25
    have k10 : k = 10 := by omega
    subst k10
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (10 + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (10 + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (10 + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e2, e24, e26, e9, e3, e25, fr⟩ := mm_iter (k := 10) s hc (by decide) hnp hyp hacc
      (hAC.sub (by omega)) r26 r9 ra3 r31 r30 ra2 r24 r25
    rw [hcol] at u1 e2 e24
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step (k := 10) (by decide) hw hAY hAN hfr hab hinv hbd hcol
    refine ⟨n1, _, c1, u1, CodeIn.store32 hc (hAC.sub (by omega)), ?_, ?_, i3, i4 11 (by decide) (by decide),
      e26, e9, e3, e25, fr⟩
    · rw [e2, e24, show (12 : Nat) = 10 + 2 from rfl]; exact i1
    · rw [e2, e24]; exact i2
  | succ m ih =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r26 r9 ra3 r31 r30 ra2 r24 r25
    have hl : k + 1 < 11 := by omega
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e2, e24, e26, e9, e3, e25, fr⟩ := mm_iter (k := k) s hc (by omega) hnp hyp hacc
      (hAC.sub (by omega)) r26 r9 ra3 r31 r30 ra2 r24 r25
    rw [hcol] at u1 e2 e24
    rw [ite_eq_left hl] at u1
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step (k := k) (by omega) hw hAY hAN hfr hab hinv hbd hcol
    have k31 : reg n1 (31 : Fin 32) = U := by rw [fr _ rfl, r31]
    have k30 : reg n1 (30 : Fin 32) = X := by rw [fr _ rfl, r30]
    obtain ⟨n', M', c', u', hc', f1, f2, f3, f4, f26, f9, f3', f25, fr'⟩ :=
      ih (k + 1) (by omega) u1 (CodeIn.store32 hc (hAC.sub (by omega))) i3 i4 i1 i2 e26 e9 e3 k31 k30 e2 e24 e25
    exact ⟨n', M', c1.trans c', u', hc', f1, f2, f3, f4, f26, f9, f3', f25,
      fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- The start of a pass, from 0x32: load the first operand's limb, compute
the factor `u` and the first column's carry, and set up the inner loop. -/
def mmHeadBlock : List BInstr :=
  [.aluImm .sll a0 (29 : Fin 32) 2, .alu .add a0 a0 (20 : Fin 32), .lw (30 : Fin 32) a0 0,
   .alu .mul a0 (6 : Fin 32) (30 : Fin 32), .lw a1 sp 0xC, .alu .add a1 a1 a0, .alu .mul (31 : Fin 32) (19 : Fin 32) a1,
   .alu .mulhu a2 (6 : Fin 32) (30 : Fin 32), .alu .mul a3 (31 : Fin 32) (7 : Fin 32),
   .alu .mulhu (9 : Fin 32) (31 : Fin 32) (7 : Fin 32), .alu .sltu a0 a1 a0, .alu .add a0 a0 a2, .alu .add a1 a1 a3,
   .alu .add a0 a0 (9 : Fin 32), .alu .sltu a2 a1 a3, .aluImm .add (25 : Fin 32) x0 0xB, .alu .add a2 a2 a0,
   .alu .sltu a3 a0 (9 : Fin 32), .alu .sltu a0 a2 a0, .alu .add (26 : Fin 32) x0 (17 : Fin 32),
   .alu .add (24 : Fin 32) a3 a0, .alu .add a3 x0 a6, .alu .add (9 : Fin 32) x0 (21 : Fin 32)]

/-- The end of a pass, from 0xCA: add the old top carry into the last word,
store it, and count the pass. -/
def mmTailBlock : List BInstr :=
  [.alu .add (22 : Fin 32) (22 : Fin 32) a2, .alu .add a0 (24 : Fin 32) (28 : Fin 32), .alu .sltu a1 (22 : Fin 32) a2,
   .sw sp (22 : Fin 32) 0x38, .alu .add (22 : Fin 32) a0 a1, .aluImm .add (29 : Fin 32) (29 : Fin 32) 1,
   .aluImm .add (28 : Fin 32) x0 0]

section
set_option maxRecDepth 20000
theorem mmHeadBlock_end : blockEnd mulMont12Code 0x32 mmHeadBlock = some 0x78 := by decide
theorem mmTailBlock_end : blockEnd mulMont12Code 0xCA mmTailBlock = some 0xDE := by decide
end

/-- The registers the start of a pass leaves alone. -/
def headKeep (q : Fin 32) : Bool := q.val ∉ [9, 10, 11, 12, 13, 24, 25, 26, 30, 31]

set_option maxRecDepth 20000 in
theorem mmHeadBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmHeadBlock (M, f)).1 = M ∧
    (runBlock mmHeadBlock (M, f)).2 (30 : Fin 32) =
      memLoad32 M (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0) ∧
    (runBlock mmHeadBlock (M, f)).2 (31 : Fin 32) = (mmHead (f (6 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (7 : Fin 32))).1 ∧
    (runBlock mmHeadBlock (M, f)).2 a2 = (mmHead (f (6 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (7 : Fin 32))).2.1 ∧
    (runBlock mmHeadBlock (M, f)).2 (24 : Fin 32) = (mmHead (f (6 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (7 : Fin 32))).2.2 ∧
    (runBlock mmHeadBlock (M, f)).2 (25 : Fin 32) = BitVec.ofNat 32 (11 - 0) ∧
    (runBlock mmHeadBlock (M, f)).2 (26 : Fin 32) = f (17 : Fin 32) ∧
    (runBlock mmHeadBlock (M, f)).2 a3 = f a6 ∧
    (runBlock mmHeadBlock (M, f)).2 (9 : Fin 32) = f (21 : Fin 32) ∧
    ∀ q, headKeep q = true → (runBlock mmHeadBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmHeadBlock]
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

theorem mmHeadBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hx : (aluEval .add (aluEval .sll (f (29 : Fin 32)) 2) (f (20 : Fin 32)) + 0).toNat % 4 = 0)
    (hs : (f sp + 0xC).toNat % 4 = 0) : BlockOk base len mmHeadBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmHeadBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hx, hs⟩

/-- The registers the end of a pass leaves alone. -/
def tailKeep (q : Fin 32) : Bool := q.val ∉ [10, 11, 22, 28, 29]

set_option maxRecDepth 20000 in
theorem mmTailBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmTailBlock (M, f)).1 = memStore32 M (f sp + 0x38) (aluEval .add (f (22 : Fin 32)) (f a2)) ∧
    (runBlock mmTailBlock (M, f)).2 (22 : Fin 32) = aluEval .add (aluEval .add (f (24 : Fin 32)) (f (28 : Fin 32)))
      (aluEval .sltu (aluEval .add (f (22 : Fin 32)) (f a2)) (f a2)) ∧
    (runBlock mmTailBlock (M, f)).2 (29 : Fin 32) = f (29 : Fin 32) + 1 ∧
    (runBlock mmTailBlock (M, f)).2 (28 : Fin 32) = 0 ∧
    ∀ q, tailKeep q = true → (runBlock mmTailBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmTailBlock]
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

theorem mmTailBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hs : (f sp + 0x38).toNat % 4 = 0) (hsep : Sep (f sp + 0x38) 4 base len) :
    BlockOk base len mmTailBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmTailBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hs, hsep⟩

theorem sll12 : ∀ i : Nat, i < 12 → aluEval .sll (BitVec.ofNat 32 i) 2 = BitVec.ofNat 32 (4 * i) := by decide

theorem pass_ne : ∀ i : Nat, i < 12 → (BitVec.ofNat 32 (i + 1) != 12) = decide (i + 1 < 12) := by decide

theorem ofNat_succ (i : Nat) : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]

theorem mm_tail_arith {A11 B P cl ch mc w c XY O UN : Nat}
    (h1 : B * A11 + (cl + B * ch) * (P * B) = XY + O + UN) (h2 : w + B * c = mc + cl) :
    B * (A11 + w * P + (ch + c) * (P * B)) = O + mc * (P * B) + XY + UN := by
  have e2 : (w + B * c) * (P * B) = (mc + cl) * (P * B) := by rw [h2]
  simp only [Nat.add_mul, Nat.mul_add] at h1 e2 ⊢
  simp only [Nat.mul_comm, Nat.mul_left_comm] at h1 e2 ⊢
  omega

/-- The registers a pass leaves alone. -/
def passKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 22, 24, 25, 26, 28, 29, 30, 31]

theorem passKeep_head : ∀ q, passKeep q = true → headKeep q = true := by decide
theorem passKeep_body : ∀ q, passKeep q = true → bodyKeep q = true := by decide
theorem passKeep_tail : ∀ q, passKeep q = true → tailKeep q = true := by decide

theorem accV_succ1 (M : Word → BitVec 8) (b : Word) (n : Nat) :
    accV M b (n + 1) = accV M b n + (memLoad32 M (b + BitVec.ofNat 32 (4 * n))).toNat * 2 ^ (32 * n) := rfl

theorem accV_frame48 {M M0 : Word → BitVec 8} {acc b : Word} {n : Nat} (hf : ∀ a, Sep acc 48 a 1 → M a = M0 a)
    (hs : Sep acc 48 b (4 * n)) : accV M b n = accV M0 b n :=
  accV_congr n fun l hl => load_frame hf (hs.subR (by omega))

set_option exponentiation.threshold 400 in
/-- **One pass of the outer loop**, from 0x32: add limb `i` of the first
operand times the second operand, and `u` times the modulus, to the
accumulator and its top carry in `s6`, and shift the sum down a word. -/
theorem mm_pass {B acc xp yp np K : Word} {M0 : Word → BitVec 8} {i : Nat} (hi : i < 12)
    (hxp : xp.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAX : Sep acc 48 xp 48) (hAY : Sep acc 48 yp 48) (hAN : Sep acc 48 np 48)
    (hAC : Sep acc 48 B mulMont12Code.length)
    (hk : (K.toNat * (memLoad32 M0 np).toNat + 1) % 2 ^ 32 = 0)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x32 (reg n)) (hc : CodeIn M B mulMont12Code)
    (hfr : ∀ a, Sep acc 48 a 1 → M a = M0 a)
    (r29 : reg n (29 : Fin 32) = BitVec.ofNat 32 i) (r20 : reg n (20 : Fin 32) = xp)
    (r6 : reg n (6 : Fin 32) = memLoad32 M0 yp) (r7 : reg n (7 : Fin 32) = memLoad32 M0 np)
    (r19 : reg n (19 : Fin 32) = K) (rsp : reg n sp + 0xC = acc)
    (rsp38 : reg n sp + 0x38 = acc + BitVec.ofNat 32 (4 * 11))
    (r17 : reg n (17 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)))
    (r16 : reg n a6 = acc + BitVec.ofNat 32 (4 * (0 + 1)))
    (r21 : reg n (21 : Fin 32) = yp + BitVec.ofNat 32 (4 * (0 + 1)))
    (r28 : reg n (28 : Fin 32) = 0) (r5 : reg n (5 : Fin 32) = 12) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 12 then 0x32 else 0xE2) (reg n') ∧ CodeIn M' B mulMont12Code ∧
      (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
      (∃ u : Nat, u < 2 ^ 32 ∧ 2 ^ 32 * (accV M' acc 12 + (reg n' (22 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M acc 12 + (reg n (22 : Fin 32)).toNat * 2 ^ (32 * 12) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 yp 12 + u * accV M0 np 12) ∧
      reg n' (29 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ reg n' (28 : Fin 32) = 0 ∧
      ∀ q, passKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hX : aluEval .add (aluEval .sll (reg n (29 : Fin 32)) 2) (reg n (20 : Fin 32)) + 0 =
      xp + BitVec.ofNat 32 (4 * i) := by
    rw [r29, r20, sll12 i hi, add_lit_zero]; exact BitVec.add_comm _ _
  have ok1 := mmHeadBlock_ok (M := M) (f := reg n) (base := B) (len := mulMont12Code.length)
    (by rw [hX]; exact aligned_add hxp (by omega)) (by rw [rsp]; exact hacc)
  obtain ⟨n1, c1, u1⟩ := St.block mmHeadBlock s hc mmHeadBlock_end ok1
  obtain ⟨hm1, h30, h31, h2, h24, h25, h26, h3, h9, hfr1⟩ := mmHeadBlock_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [hm1] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock mmHeadBlock (M, reg n)).2 q := u1.regs
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
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 0x7C mm_at_78 (by decide) hb
  have g2 : ∀ q, reg n2 q = (runBlock mmHeadBlock (M, reg n)).2 q := fun q => by rw [u2.regs, g1]
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
    mm_inner (M0 := M) (U := u) (X := memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) hnp hyp hacc hw hAY hAN hAC
      10 0 (by decide) u2.self hc (fun _ _ => rfl) (fun _ _ _ => rfl) inv0 bd
      (by rw [g2, h26, r17]) (by rw [g2, h9, r21]) (by rw [g2, h3, r16]) (by rw [g2, h31]) (by rw [g2, h30])
      (by rw [g2, h2]) (by rw [g2, h24]) (by rw [g2, h25])
  have k3 : ∀ q, passKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [fr3 q (passKeep_body q hq), g2, hfr1 q (passKeep_head q hq)]
  have hb3 : ∀ q, headKeep q = true → bodyKeep q = true → reg n3 q = reg n q := fun q h1 h2 => by
    rw [fr3 q h2, g2, hfr1 q h1]
  have sp3 : reg n3 sp = reg n sp := k3 sp rfl
  have ok3 := mmTailBlock_ok (M := M1) (f := reg n3) (base := B) (len := mulMont12Code.length)
    (by rw [sp3, rsp38]; exact aligned_add hacc (by omega)) (by rw [sp3, rsp38]; exact hAC.sub (by omega))
  obtain ⟨n4, c4, u4⟩ := St.block mmTailBlock u3 hc3 mmTailBlock_end ok3
  obtain ⟨hm4, t22, t29, t28, tfr⟩ := mmTailBlock_run (M := M1) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [hm4, sp3, rsp38] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock mmTailBlock (M1, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)) hc3 (hAC.sub (c := 4 * 11) (by omega))
  have e29 : reg n4 (29 : Fin 32) = BitVec.ofNat 32 (i + 1) := by
    rw [g4, t29, hb3 (29 : Fin 32) rfl rfl, r29, ofNat_succ]
  have e28 : reg n4 (28 : Fin 32) = 0 := by rw [g4, t28]
  have k4 : ∀ q, passKeep q = true → reg n4 q = reg n q := fun q hq => by
    rw [g4, tfr q (passKeep_tail q hq), k3 q hq]
  have hb4 : branchTaken .bne (reg n4 (29 : Fin 32)) (reg n4 (5 : Fin 32)) = decide (i + 1 < 12) := by
    rw [e29, k4 _ rfl, r5]; exact pass_ne i hi
  -- the arithmetic of the pass
  have arith : 2 ^ 32 * (accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11))
        (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2))) acc 12 + (reg n4 (22 : Fin 32)).toNat * 2 ^ (32 * 12)) =
      accV M acc 12 + (reg n (22 : Fin 32)).toNat * 2 ^ (32 * 12) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 yp 12 + u.toNat * accV M0 np 12 := by
    have hA : accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11)) (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)))
        acc 12 = accV M1 acc 11 + (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)).toNat * 2 ^ (32 * 11) := by
      rw [show (12 : Nat) = 11 + 1 from rfl, accV_succ1, accV_store_above (by omega) 11 (Nat.le_refl 11),
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
    have p12 : (2 : Nat) ^ (32 * 12) = 2 ^ (32 * 11) * 2 ^ 32 := pow32_succ 11
    rw [eX, accV_frame48 (b := yp) (n := 12) hfr hAY, accV_frame48 (b := np) (n := 12) hfr hAN, p12] at I1
    rw [hA, h22, p12, hb3 (22 : Fin 32) rfl rfl]
    rw [hb3 (22 : Fin 32) rfl rfl] at ac
    exact mm_tail_arith I1 ac
  have fr4 : ∀ a, Sep acc 48 a 1 → memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11))
      (aluEval .add (reg n3 (22 : Fin 32)) (reg n3 a2)) a = M0 a := fun a ha => by
    rw [memStore32_ne fun j hj e => (ha.point (i := 4 * 11 + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm), I3 a ha, hfr a ha]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x32 mm_at_de (by decide) (by rw [hb4]; exact decide_eq_true hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e29], by rw [g5, e28], fun q hq => by rw [g5, k4 q hq]⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0xE2 mm_at_de (by decide) (by rw [hb4]; exact decide_eq_false hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e29], by rw [g5, e28], fun q hq => by rw [g5, k4 q hq]⟩

theorem mm_outer_arith {B P T T' x Y u N Xi Ui : Nat} (hB : 0 < B)
    (hp : B * T' = T + x * Y + u * N) (hinv : P * T = Xi * Y + Ui * N) (hbd : T < 2 * N) (hx : x < B)
    (hu : u < B) (hY : Y < N) :
    P * B * T' = (Xi + x * P) * Y + (Ui + P * u) * N ∧ T' < 2 * N := by
  constructor
  · rw [Nat.mul_assoc, hp]
    simp only [Nat.mul_add, Nat.add_mul, hinv]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega
  · have h1 : x * Y ≤ (B - 1) * N := Nat.mul_le_mul (by omega) (by omega)
    have h2 : u * N ≤ (B - 1) * N := Nat.mul_le_mul_right _ (by omega)
    have e : (B - 1) * N + N = B * N := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hB]
    have : B * T' < B * (2 * N) := by rw [Nat.mul_left_comm]; omega
    exact Nat.lt_of_mul_lt_mul_left this

set_option exponentiation.threshold 400 in
/-- **The outer loop**, from pass `i` to its end at 0xE2. The accumulator
and its top carry hold a sum `T` with `2^(32 i) T = X_i Y + U N`, for `X_i`
the first operand's low `i` limbs and some `U`, and `T < 2N`. -/
theorem mm_outer {B acc xp yp np K : Word} {M0 : Word → BitVec 8}
    (hxp : xp.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAX : Sep acc 48 xp 48) (hAY : Sep acc 48 yp 48) (hAN : Sep acc 48 np 48)
    (hAC : Sep acc 48 B mulMont12Code.length)
    (hk : (K.toNat * (memLoad32 M0 np).toNat + 1) % 2 ^ 32 = 0) (hYN : accV M0 yp 12 < accV M0 np 12) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x32 (reg n) → CodeIn M B mulMont12Code → (∀ a, Sep acc 48 a 1 → M a = M0 a) →
      (∃ U, 2 ^ (32 * i) * (accV M acc 12 + (reg n (22 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M0 xp i * accV M0 yp 12 + U * accV M0 np 12) →
      accV M acc 12 + (reg n (22 : Fin 32)).toNat * 2 ^ (32 * 12) < 2 * accV M0 np 12 →
      reg n (29 : Fin 32) = BitVec.ofNat 32 i → reg n (20 : Fin 32) = xp →
      reg n (6 : Fin 32) = memLoad32 M0 yp → reg n (7 : Fin 32) = memLoad32 M0 np →
      reg n (19 : Fin 32) = K → reg n sp + 0xC = acc →
      reg n sp + 0x38 = acc + BitVec.ofNat 32 (4 * 11) →
      reg n (17 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n a6 = acc + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (21 : Fin 32) = yp + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (28 : Fin 32) = 0 → reg n (5 : Fin 32) = 12 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0xE2 (reg n') ∧ CodeIn M' B mulMont12Code ∧
        (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
        (∃ U, 2 ^ (32 * 12) * (accV M' acc 12 + (reg n' (22 : Fin 32)).toNat * 2 ^ (32 * 12)) =
          accV M0 xp 12 * accV M0 yp 12 + U * accV M0 np 12) ∧
        accV M' acc 12 + (reg n' (22 : Fin 32)).toNat * 2 ^ (32 * 12) < 2 * accV M0 np 12 ∧
        ∀ q, passKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hinv hbd r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    have i11 : i = 11 := by omega
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e29, e28, k1⟩ := mm_pass (i := 11) (by decide) hxp hyp hnp hacc
      hw hAX hAY hAN hAC hk s hc hfr r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * 11))).isLt hu hYN
    refine ⟨n1, M1, c1, u1, hc1, hf1, ⟨U + 2 ^ (32 * 11) * u, ?_⟩, a2, k1⟩
    rw [pow32_succ 11] at a1 ⊢
    rw [a1, accV_succ1 M0 xp 11]
  | succ m ih =>
    intro i hi M n s hc hfr hinv hbd r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    have hl : i + 1 < 12 := by omega
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e29, e28, k1⟩ := mm_pass (i := i) (by omega) hxp hyp hnp hacc
      hw hAX hAY hAN hAC hk s hc hfr r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    rw [ite_eq_left hl] at u1
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).isLt hu hYN
    have inv1 : ∃ U, 2 ^ (32 * (i + 1)) * (accV M1 acc 12 + (reg n1 (22 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M0 xp (i + 1) * accV M0 yp 12 + U * accV M0 np 12 :=
      ⟨U + 2 ^ (32 * i) * u, by rw [pow32_succ i, a1, accV_succ1 M0 xp i]⟩
    obtain ⟨n', M', c', u', hc', hf', hv', hb', k'⟩ := ih (i + 1) (by omega) u1 hc1 hf1 inv1 a2 e29
      (by rw [k1 _ rfl, r20]) (by rw [k1 _ rfl, r6]) (by rw [k1 _ rfl, r7]) (by rw [k1 _ rfl, r19])
      (by rw [k1 _ rfl, rsp]) (by rw [k1 _ rfl, rsp38]) (by rw [k1 _ rfl, r17]) (by rw [k1 _ rfl, r16])
      (by rw [k1 _ rfl, r21]) e28 (by rw [k1 _ rfl, r5])
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', hb', fun q hq => by rw [k' q hq, k1 q hq]⟩

end C3.RV32
