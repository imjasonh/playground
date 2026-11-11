import C3BootProofs.Proofs.MontMul12Main

/-!
# P-384's Montgomery squaring, as compiled

`crypto_bigint`'s `square_montgomery_form::<12>` compiles the same loop as
`mul_montgomery_form::<12>` with both operands the same, in other registers.
The loop body is `mmBody` over those registers, and the arithmetic lemmas of
`MontMul12.lean` apply unchanged.
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem sq_at_0 : fetchRel sqMont12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF60, 2) := by decide
theorem sq_at_2 : fetchRel sqMont12Code 0x2 = some (.auipc (5 : Fin 32) 0xC000, 4) := by decide
theorem sq_at_6 : fetchRel sqMont12Code 0x6 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFFF8, 4) := by decide
theorem sq_at_a : fetchRel sqMont12Code 0xA = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem sq_at_c : fetchRel sqMont12Code 0xC = some (.alu .add (22 : Fin 32) x0 a2, 2) := by decide
theorem sq_at_e : fetchRel sqMont12Code 0xE = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem sq_at_10 : fetchRel sqMont12Code 0x10 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem sq_at_12 : fetchRel sqMont12Code 0x12 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem sq_at_14 : fetchRel sqMont12Code 0x14 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem sq_at_18 : fetchRel sqMont12Code 0x18 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem sq_at_1a : fetchRel sqMont12Code 0x1A = some (.auipc ra 0xC000, 4) := by decide
theorem sq_at_1e : fetchRel sqMont12Code 0x1E = some (.jalr ra ra 0x73A, 4) := by decide
theorem sq_at_22 : fetchRel sqMont12Code 0x22 = some (.aluImm .add (21 : Fin 32) x0 0x0, 2) := by decide
theorem sq_at_24 : fetchRel sqMont12Code 0x24 = some (.aluImm .add (29 : Fin 32) x0 0x0, 2) := by decide
theorem sq_at_26 : fetchRel sqMont12Code 0x26 = some (.aluImm .add (30 : Fin 32) x0 0x0, 2) := by decide
theorem sq_at_28 : fetchRel sqMont12Code 0x28 = some (.load .lw (7 : Fin 32) (20 : Fin 32) 0x0, 4) := by decide
theorem sq_at_2c : fetchRel sqMont12Code 0x2C = some (.load .lw (28 : Fin 32) (22 : Fin 32) 0x0, 4) := by decide
theorem sq_at_30 : fetchRel sqMont12Code 0x30 = some (.aluImm .add a6 (20 : Fin 32) 0x4, 4) := by decide
theorem sq_at_34 : fetchRel sqMont12Code 0x34 = some (.aluImm .add (17 : Fin 32) sp 0x10, 4) := by decide
theorem sq_at_38 : fetchRel sqMont12Code 0x38 = some (.aluImm .add (5 : Fin 32) (22 : Fin 32) 0x4, 4) := by decide
theorem sq_at_3c : fetchRel sqMont12Code 0x3C = some (.aluImm .add (6 : Fin 32) x0 0xC, 2) := by decide
theorem sq_at_3e : fetchRel sqMont12Code 0x3E = some (.branch .beq (6 : Fin 32) x0 0xB4, 4) := by decide
theorem sq_at_42 : fetchRel sqMont12Code 0x42 = some (.aluImm .sll a0 (30 : Fin 32) 0x2, 4) := by decide
theorem sq_at_46 : fetchRel sqMont12Code 0x46 = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem sq_at_48 : fetchRel sqMont12Code 0x48 = some (.load .lw (31 : Fin 32) a0 0x0, 4) := by decide
theorem sq_at_4c : fetchRel sqMont12Code 0x4C = some (.alu .mul a0 (7 : Fin 32) (31 : Fin 32), 4) := by decide
theorem sq_at_50 : fetchRel sqMont12Code 0x50 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem sq_at_52 : fetchRel sqMont12Code 0x52 = some (.alu .add a1 a1 a0, 2) := by decide
theorem sq_at_54 : fetchRel sqMont12Code 0x54 = some (.alu .mul (23 : Fin 32) (19 : Fin 32) a1, 4) := by decide
theorem sq_at_58 : fetchRel sqMont12Code 0x58 = some (.alu .mulhu a2 (7 : Fin 32) (31 : Fin 32), 4) := by decide
theorem sq_at_5c : fetchRel sqMont12Code 0x5C = some (.alu .mul a4 (23 : Fin 32) (28 : Fin 32), 4) := by decide
theorem sq_at_60 : fetchRel sqMont12Code 0x60 = some (.alu .mulhu (9 : Fin 32) (23 : Fin 32) (28 : Fin 32), 4) := by decide
theorem sq_at_64 : fetchRel sqMont12Code 0x64 = some (.alu .sltu a0 a1 a0, 4) := by decide
theorem sq_at_68 : fetchRel sqMont12Code 0x68 = some (.alu .add a0 a0 a2, 2) := by decide
theorem sq_at_6a : fetchRel sqMont12Code 0x6A = some (.alu .add a1 a1 a4, 2) := by decide
theorem sq_at_6c : fetchRel sqMont12Code 0x6C = some (.alu .add a0 a0 (9 : Fin 32), 2) := by decide
theorem sq_at_6e : fetchRel sqMont12Code 0x6E = some (.alu .sltu a2 a1 a4, 4) := by decide
theorem sq_at_72 : fetchRel sqMont12Code 0x72 = some (.aluImm .add (25 : Fin 32) x0 0xB, 2) := by decide
theorem sq_at_74 : fetchRel sqMont12Code 0x74 = some (.alu .add a2 a2 a0, 2) := by decide
theorem sq_at_76 : fetchRel sqMont12Code 0x76 = some (.alu .sltu a4 a0 (9 : Fin 32), 4) := by decide
theorem sq_at_7a : fetchRel sqMont12Code 0x7A = some (.alu .sltu a0 a2 a0, 4) := by decide
theorem sq_at_7e : fetchRel sqMont12Code 0x7E = some (.alu .add (26 : Fin 32) x0 (5 : Fin 32), 2) := by decide
theorem sq_at_80 : fetchRel sqMont12Code 0x80 = some (.alu .add (24 : Fin 32) a4 a0, 4) := by decide
theorem sq_at_84 : fetchRel sqMont12Code 0x84 = some (.alu .add a4 x0 (17 : Fin 32), 2) := by decide
theorem sq_at_86 : fetchRel sqMont12Code 0x86 = some (.alu .add (9 : Fin 32) x0 a6, 2) := by decide
theorem sq_at_88 : fetchRel sqMont12Code 0x88 = some (.branch .beq (25 : Fin 32) x0 0x52, 4) := by decide
theorem sq_at_8c : fetchRel sqMont12Code 0x8C = some (.load .lw a5 (26 : Fin 32) 0x0, 4) := by decide
theorem sq_at_90 : fetchRel sqMont12Code 0x90 = some (.load .lw a3 (9 : Fin 32) 0x0, 2) := by decide
theorem sq_at_92 : fetchRel sqMont12Code 0x92 = some (.alu .mulhu a0 a5 (23 : Fin 32), 4) := by decide
theorem sq_at_96 : fetchRel sqMont12Code 0x96 = some (.alu .mul (8 : Fin 32) a3 (31 : Fin 32), 4) := by decide
theorem sq_at_9a : fetchRel sqMont12Code 0x9A = some (.alu .mul a5 a5 (23 : Fin 32), 4) := by decide
theorem sq_at_9e : fetchRel sqMont12Code 0x9E = some (.load .lw a1 a4 0x0, 2) := by decide
theorem sq_at_a0 : fetchRel sqMont12Code 0xA0 = some (.alu .mulhu a3 a3 (31 : Fin 32), 4) := by decide
theorem sq_at_a4 : fetchRel sqMont12Code 0xA4 = some (.alu .add a0 a0 (24 : Fin 32), 2) := by decide
theorem sq_at_a6 : fetchRel sqMont12Code 0xA6 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem sq_at_a8 : fetchRel sqMont12Code 0xA8 = some (.alu .add a1 a1 (8 : Fin 32), 2) := by decide
theorem sq_at_aa : fetchRel sqMont12Code 0xAA = some (.alu .add a2 a2 a5, 2) := by decide
theorem sq_at_ac : fetchRel sqMont12Code 0xAC = some (.alu .sltu (8 : Fin 32) a1 (8 : Fin 32), 4) := by decide
theorem sq_at_b0 : fetchRel sqMont12Code 0xB0 = some (.alu .sltu a5 a2 a5, 4) := by decide
theorem sq_at_b4 : fetchRel sqMont12Code 0xB4 = some (.alu .add a1 a1 a2, 2) := by decide
theorem sq_at_b6 : fetchRel sqMont12Code 0xB6 = some (.alu .add a3 a3 (8 : Fin 32), 2) := by decide
theorem sq_at_b8 : fetchRel sqMont12Code 0xB8 = some (.alu .add a0 a0 a5, 2) := by decide
theorem sq_at_ba : fetchRel sqMont12Code 0xBA = some (.alu .sltu a2 a1 a2, 4) := by decide
theorem sq_at_be : fetchRel sqMont12Code 0xBE = some (.alu .add a3 a3 a0, 2) := by decide
theorem sq_at_c0 : fetchRel sqMont12Code 0xC0 = some (.store .sw a4 a1 0xFFFFFFFC, 4) := by decide
theorem sq_at_c4 : fetchRel sqMont12Code 0xC4 = some (.alu .add a2 a2 a3, 2) := by decide
theorem sq_at_c6 : fetchRel sqMont12Code 0xC6 = some (.alu .sltu (24 : Fin 32) a3 a0, 4) := by decide
theorem sq_at_ca : fetchRel sqMont12Code 0xCA = some (.alu .sltu a0 a2 a3, 4) := by decide
theorem sq_at_ce : fetchRel sqMont12Code 0xCE = some (.aluImm .add a4 a4 0x4, 2) := by decide
theorem sq_at_d0 : fetchRel sqMont12Code 0xD0 = some (.alu .add (24 : Fin 32) (24 : Fin 32) a0, 2) := by decide
theorem sq_at_d2 : fetchRel sqMont12Code 0xD2 = some (.aluImm .add (26 : Fin 32) (26 : Fin 32) 0x4, 2) := by decide
theorem sq_at_d4 : fetchRel sqMont12Code 0xD4 = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem sq_at_d6 : fetchRel sqMont12Code 0xD6 = some (.branch .bne (25 : Fin 32) x0 0xFFFFFFB6, 4) := by decide
theorem sq_at_da : fetchRel sqMont12Code 0xDA = some (.alu .add (21 : Fin 32) (21 : Fin 32) a2, 2) := by decide
theorem sq_at_dc : fetchRel sqMont12Code 0xDC = some (.alu .add a0 (24 : Fin 32) (29 : Fin 32), 4) := by decide
theorem sq_at_e0 : fetchRel sqMont12Code 0xE0 = some (.alu .sltu a1 (21 : Fin 32) a2, 4) := by decide
theorem sq_at_e4 : fetchRel sqMont12Code 0xE4 = some (.store .sw sp (21 : Fin 32) 0x38, 2) := by decide
theorem sq_at_e6 : fetchRel sqMont12Code 0xE6 = some (.alu .add (21 : Fin 32) a0 a1, 4) := by decide
theorem sq_at_ea : fetchRel sqMont12Code 0xEA = some (.aluImm .add (30 : Fin 32) (30 : Fin 32) 0x1, 2) := by decide
theorem sq_at_ec : fetchRel sqMont12Code 0xEC = some (.aluImm .add (29 : Fin 32) x0 0x0, 2) := by decide
theorem sq_at_ee : fetchRel sqMont12Code 0xEE = some (.branch .bne (30 : Fin 32) (6 : Fin 32) 0xFFFFFF54, 4) := by decide
theorem sq_at_f2 : fetchRel sqMont12Code 0xF2 = some (.aluImm .add a0 sp 0x3C, 2) := by decide
theorem sq_at_f4 : fetchRel sqMont12Code 0xF4 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem sq_at_f8 : fetchRel sqMont12Code 0xF8 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem sq_at_fa : fetchRel sqMont12Code 0xFA = some (.aluImm .add (19 : Fin 32) sp 0x3C, 4) := by decide
theorem sq_at_fe : fetchRel sqMont12Code 0xFE = some (.auipc ra 0xC000, 4) := by decide
theorem sq_at_102 : fetchRel sqMont12Code 0x102 = some (.jalr ra ra 0x656, 4) := by decide
theorem sq_at_106 : fetchRel sqMont12Code 0x106 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem sq_at_108 : fetchRel sqMont12Code 0x108 = some (.aluImm .add (9 : Fin 32) sp 0xC, 2) := by decide
theorem sq_at_10a : fetchRel sqMont12Code 0x10A = some (.aluImm .add (8 : Fin 32) x0 0xC, 2) := by decide
theorem sq_at_10c : fetchRel sqMont12Code 0x10C = some (.branch .beq (8 : Fin 32) x0 0x20, 2) := by decide
theorem sq_at_10e : fetchRel sqMont12Code 0x10E = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem sq_at_110 : fetchRel sqMont12Code 0x110 = some (.load .lw a1 (22 : Fin 32) 0x0, 4) := by decide
theorem sq_at_114 : fetchRel sqMont12Code 0x114 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem sq_at_118 : fetchRel sqMont12Code 0x118 = some (.jalr ra ra 0x2D6, 4) := by decide
theorem sq_at_11c : fetchRel sqMont12Code 0x11C = some (.alu .add a2 x0 a1, 2) := by decide
theorem sq_at_11e : fetchRel sqMont12Code 0x11E = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem sq_at_120 : fetchRel sqMont12Code 0x120 = some (.store .sw (19 : Fin 32) a0 0x0, 4) := by decide
theorem sq_at_124 : fetchRel sqMont12Code 0x124 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x4, 2) := by decide
theorem sq_at_126 : fetchRel sqMont12Code 0x126 = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x4, 2) := by decide
theorem sq_at_128 : fetchRel sqMont12Code 0x128 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem sq_at_12a : fetchRel sqMont12Code 0x12A = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem sq_at_12c : fetchRel sqMont12Code 0x12C = some (.store .sw sp (21 : Fin 32) 0x6C, 2) := by decide
theorem sq_at_12e : fetchRel sqMont12Code 0x12E = some (.aluImm .add a0 sp 0x6C, 2) := by decide
theorem sq_at_130 : fetchRel sqMont12Code 0x130 = some (.load .lw a0 sp 0x6C, 2) := by decide
theorem sq_at_132 : fetchRel sqMont12Code 0x132 = some (.aluImm .sltu (9 : Fin 32) a0 0x1, 4) := by decide
theorem sq_at_136 : fetchRel sqMont12Code 0x136 = some (.alu .and (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem sq_at_138 : fetchRel sqMont12Code 0x138 = some (.store .sb sp (9 : Fin 32) 0x6C, 4) := by decide
theorem sq_at_13c : fetchRel sqMont12Code 0x13C = some (.aluImm .add a0 sp 0x6C, 2) := by decide
theorem sq_at_13e : fetchRel sqMont12Code 0x13E = some (.load .lbu a0 sp 0x6C, 4) := by decide
theorem sq_at_142 : fetchRel sqMont12Code 0x142 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem sq_at_144 : fetchRel sqMont12Code 0x144 = some (.alu .and a2 a2 a0, 2) := by decide
theorem sq_at_146 : fetchRel sqMont12Code 0x146 = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem sq_at_148 : fetchRel sqMont12Code 0x148 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem sq_at_14a : fetchRel sqMont12Code 0x14A = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem sq_at_14e : fetchRel sqMont12Code 0x14E = some (.jalr ra ra 0x2A0, 4) := by decide
theorem sq_at_152 : fetchRel sqMont12Code 0x152 = some (.aluImm .add a1 sp 0x3C, 2) := by decide
theorem sq_at_154 : fetchRel sqMont12Code 0x154 = some (.aluImm .add a2 sp 0xC, 2) := by decide
theorem sq_at_156 : fetchRel sqMont12Code 0x156 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem sq_at_158 : fetchRel sqMont12Code 0x158 = some (.alu .add a3 x0 (9 : Fin 32), 2) := by decide
theorem sq_at_15a : fetchRel sqMont12Code 0x15A = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem sq_at_15e : fetchRel sqMont12Code 0x15E = some (.jalr ra ra 0x464, 4) := by decide
theorem sq_at_162 : fetchRel sqMont12Code 0x162 = some (.auipc (5 : Fin 32) 0xC000, 4) := by decide
theorem sq_at_166 : fetchRel sqMont12Code 0x166 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFEE6, 4) := by decide
theorem sq_at_16a : fetchRel sqMont12Code 0x16A = some (.aluImm .add sp sp 0xA0, 2) := by decide
theorem sq_at_16c : fetchRel sqMont12Code 0x16C = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- The loop body in `square_montgomery_form::<12>`. -/
abbrev mmBodyS : List BInstr :=
  mmBody (26 : Fin 32) (9 : Fin 32) a4 (23 : Fin 32) (31 : Fin 32) a2 (24 : Fin 32) (25 : Fin 32) a5 a3 a0
    (8 : Fin 32) a1

section
set_option maxRecDepth 20000
theorem mmBodyS_end : blockEnd sqMont12Code 0x8C mmBodyS = some 0xD6 := by decide
end

set_option maxRecDepth 20000 in
theorem mmBodyS_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmBodyS (M, f)).1 = memStore32 M (f a4 + 0xFFFFFFFC)
        (mmCols (memLoad32 M (f (26 : Fin 32) + 0)) (memLoad32 M (f (9 : Fin 32) + 0)) (memLoad32 M (f a4 + 0))
          (f (23 : Fin 32)) (f (31 : Fin 32)) (f a2) (f (24 : Fin 32))).1 ∧
    (runBlock mmBodyS (M, f)).2 a2 = (mmCols (memLoad32 M (f (26 : Fin 32) + 0)) (memLoad32 M (f (9 : Fin 32) + 0))
        (memLoad32 M (f a4 + 0)) (f (23 : Fin 32)) (f (31 : Fin 32)) (f a2) (f (24 : Fin 32))).2.1 ∧
    (runBlock mmBodyS (M, f)).2 (24 : Fin 32) = (mmCols (memLoad32 M (f (26 : Fin 32) + 0))
        (memLoad32 M (f (9 : Fin 32) + 0)) (memLoad32 M (f a4 + 0)) (f (23 : Fin 32)) (f (31 : Fin 32)) (f a2)
        (f (24 : Fin 32))).2.2 ∧
    (runBlock mmBodyS (M, f)).2 (26 : Fin 32) = f (26 : Fin 32) + 4 ∧
    (runBlock mmBodyS (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock mmBodyS (M, f)).2 a4 = f a4 + 4 ∧
    (runBlock mmBodyS (M, f)).2 (25 : Fin 32) = f (25 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ (26 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ a3 → q ≠ a2 → q ≠ (24 : Fin 32) → q ≠ (25 : Fin 32) →
      q ≠ a4 → q ≠ a5 → q ≠ a0 → q ≠ (8 : Fin 32) → q ≠ a1 → (runBlock mmBodyS (M, f)).2 q = f q := by
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

theorem mmBodyS_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hn : (f (26 : Fin 32) + 0).toNat % 4 = 0) (hy : (f (9 : Fin 32) + 0).toNat % 4 = 0)
    (ho : (f a4 + 0).toNat % 4 = 0) (hs : (f a4 + 0xFFFFFFFC).toNat % 4 = 0)
    (hsep : Sep (f a4 + 0xFFFFFFFC) 4 base len) : BlockOk base len mmBodyS (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmBody, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hn, hy, ho, hs, hsep⟩

/-- **One pass of the inner loop**, from 0x8C: column `k + 1` of a pass,
which stores the accumulator's word `k`. -/
theorem sq_iter {M : Word → BitVec 8} {B np yp acc U X CL CH : Word} {n : Machine} {k : Nat}
    (s : St M B n 0x8C (reg n)) (hc : CodeIn M B sqMont12Code) (hk : k < 11)
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hS : Sep (acc + BitVec.ofNat 32 (4 * k)) 4 B sqMont12Code.length)
    (r26 : reg n (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)))
    (r9 : reg n (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 1)))
    (ra4 : reg n a4 = acc + BitVec.ofNat 32 (4 * (k + 1)))
    (r31 : reg n (23 : Fin 32) = U) (r30 : reg n (31 : Fin 32) = X) (ra2 : reg n a2 = CL)
    (r24 : reg n (24 : Fin 32) = CH) (r25 : reg n (25 : Fin 32) = BitVec.ofNat 32 (11 - k)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (acc + BitVec.ofNat 32 (4 * k))
        (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1))))
          (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1)))) U X CL CH).1)
        B n' (if k + 1 < 11 then 0x8C else 0xDA) (reg n') ∧
      reg n' a2 = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.1 ∧
      reg n' (24 : Fin 32) = (mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH).2.2 ∧
      reg n' (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' a4 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n' (25 : Fin 32) = BitVec.ofNat 32 (11 - (k + 1)) ∧
      ∀ q, bodyKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have ok := mmBodyS_ok (M := M) (f := reg n) (base := B) (len := sqMont12Code.length)
    (by rw [r26, add_lit_zero]; exact aligned_add hnp (by omega))
    (by rw [r9, add_lit_zero]; exact aligned_add hyp (by omega))
    (by rw [ra4, add_lit_zero]; exact aligned_add hacc (by omega))
    (by rw [ra4, back4 acc k]; exact aligned_add hacc (by omega))
    (by rw [ra4, back4 acc k]; exact hS)
  obtain ⟨n1, c1, u1⟩ := St.block mmBodyS s hc mmBodyS_end ok
  obtain ⟨em, e2, e24, e26, e9, e3, e25, fr⟩ := mmBodyS_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em, r26, r9, ra4, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero, back4 acc k] at u1'
  have g : ∀ q, reg n1 q = (runBlock mmBodyS (M, reg n)).2 q := u1.regs
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
      reg n2 a4 = acc + BitVec.ofNat 32 (4 * (k + 2)) ∧
      reg n2 (25 : Fin 32) = BitVec.ofNat 32 (11 - (k + 1)) ∧
      ∀ q, bodyKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [h2, g, e2, r26, r9, ra4, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e24, r26, r9, ra4, r31, r30, ra2, r24, add_lit_zero, add_lit_zero, add_lit_zero]
    · rw [h2, g, e26, r26, ptr4]
    · rw [h2, g, e9, r9, ptr4]
    · rw [h2, g, e3, ra4, ptr4]
    · rw [h2, g, e25, r25, cnt11_dec k hk]
    · rw [h2, g]
      exact fr q (pkeep_ne (r := 26) hq rfl) (pkeep_ne (r := 9) hq rfl) (pkeep_ne (r := a3) hq rfl)
        (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := 24) hq rfl) (pkeep_ne (r := 25) hq rfl)
        (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := a0) hq rfl)
        (pkeep_ne (r := 8) hq rfl) (pkeep_ne (r := a1) hq rfl)
  by_cases hl : k + 1 < 11
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x8C sq_at_d6 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0xDA sq_at_d6 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The inner loop**, from column `k + 1` of a pass to its end at 0xDA:
columns `k + 1..11` of the pass. -/
theorem sq_inner {B acc yp np U X : Word} {M0 : Word → BitVec 8}
    (hnp : np.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0) (hw : acc.toNat + 48 ≤ 2 ^ 32)
    (hAY : Sep acc 48 yp 48) (hAN : Sep acc 48 np 48) (hAC : Sep acc 48 B sqMont12Code.length) :
    ∀ m k, k + m + 1 = 11 → ∀ {M : Word → BitVec 8} {n : Machine} {CL CH : Word},
      St M B n 0x8C (reg n) → CodeIn M B sqMont12Code →
      (∀ a, Sep acc 48 a 1 → M a = M0 a) →
      (∀ i, k ≤ i → i < 12 →
        memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) →
      2 ^ 32 * accV M acc k + (CL.toNat + 2 ^ 32 * CH.toNat) * 2 ^ (32 * (k + 1)) =
        X.toNat * accV M0 yp (k + 1) + accV M0 acc (k + 1) + U.toNat * accV M0 np (k + 1) →
      CL.toNat + 2 ^ 32 * CH.toNat ≤ 2 * 2 ^ 32 - 2 →
      reg n (26 : Fin 32) = np + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n a4 = acc + BitVec.ofNat 32 (4 * (k + 1)) →
      reg n (23 : Fin 32) = U → reg n (31 : Fin 32) = X → reg n a2 = CL → reg n (24 : Fin 32) = CH →
      reg n (25 : Fin 32) = BitVec.ofNat 32 (11 - k) →
      ∃ n' M', Steps n n' ∧ St M' B n' 0xDA (reg n') ∧ CodeIn M' B sqMont12Code ∧
        2 ^ 32 * accV M' acc 11 + ((reg n' a2).toNat + 2 ^ 32 * (reg n' (24 : Fin 32)).toNat) * 2 ^ (32 * 12) =
          X.toNat * accV M0 yp 12 + accV M0 acc 12 + U.toNat * accV M0 np 12 ∧
        (reg n' a2).toNat + 2 ^ 32 * (reg n' (24 : Fin 32)).toNat ≤ 2 * 2 ^ 32 - 2 ∧
        (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
        memLoad32 M' (acc + BitVec.ofNat 32 (4 * 11)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * 11)) ∧
        reg n' (26 : Fin 32) = np + BitVec.ofNat 32 (4 * 12) ∧
        reg n' (9 : Fin 32) = yp + BitVec.ofNat 32 (4 * 12) ∧
        reg n' a4 = acc + BitVec.ofNat 32 (4 * 12) ∧
        reg n' (25 : Fin 32) = 0 ∧
        ∀ q, bodyKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r26 r9 ra4 r31 r30 ra2 r24 r25
    have k10 : k = 10 := by omega
    subst k10
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (10 + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (10 + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (10 + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e2, e24, e26, e9, e3, e25, fr⟩ := sq_iter (k := 10) s hc (by decide) hnp hyp hacc
      (hAC.sub (by omega)) r26 r9 ra4 r31 r30 ra2 r24 r25
    rw [hcol] at u1 e2 e24
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step (k := 10) (by decide) hw hAY hAN hfr hab hinv hbd hcol
    refine ⟨n1, _, c1, u1, CodeIn.store32 hc (hAC.sub (by omega)), ?_, ?_, i3, i4 11 (by decide) (by decide),
      e26, e9, e3, e25, fr⟩
    · rw [e2, e24, show (12 : Nat) = 10 + 2 from rfl]; exact i1
    · rw [e2, e24]; exact i2
  | succ m ih =>
    intro k hk M n CL CH s hc hfr hab hinv hbd r26 r9 ra4 r31 r30 ra2 r24 r25
    have hl : k + 1 < 11 := by omega
    obtain ⟨lo, cl, ch, hcol⟩ : ∃ lo cl ch, mmCols (memLoad32 M (np + BitVec.ofNat 32 (4 * (k + 1))))
        (memLoad32 M (yp + BitVec.ofNat 32 (4 * (k + 1)))) (memLoad32 M (acc + BitVec.ofNat 32 (4 * (k + 1))))
        U X CL CH = (lo, cl, ch) := ⟨_, _, _, rfl⟩
    obtain ⟨n1, c1, u1, e2, e24, e26, e9, e3, e25, fr⟩ := sq_iter (k := k) s hc (by omega) hnp hyp hacc
      (hAC.sub (by omega)) r26 r9 ra4 r31 r30 ra2 r24 r25
    rw [hcol] at u1 e2 e24
    rw [ite_eq_left hl] at u1
    obtain ⟨i1, i2, i3, i4⟩ := mm_inv_step (k := k) (by omega) hw hAY hAN hfr hab hinv hbd hcol
    have k31 : reg n1 (23 : Fin 32) = U := by rw [fr _ rfl, r31]
    have k30 : reg n1 (31 : Fin 32) = X := by rw [fr _ rfl, r30]
    obtain ⟨n', M', c', u', hc', f1, f2, f3, f4, f26, f9, f3', f25, fr'⟩ :=
      ih (k + 1) (by omega) u1 (CodeIn.store32 hc (hAC.sub (by omega))) i3 i4 i1 i2 e26 e9 e3 k31 k30 e2 e24 e25
    exact ⟨n', M', c1.trans c', u', hc', f1, f2, f3, f4, f26, f9, f3', f25,
      fun q hq => by rw [fr' q hq, fr q hq]⟩

/-- The start of a pass, from 0x42: load the operand's limb, compute the
factor `u` and the first column's carry, and set up the inner loop. -/
def sqHeadBlock : List BInstr :=
  [.aluImm .sll a0 (30 : Fin 32) 2, .alu .add a0 a0 (20 : Fin 32), .lw (31 : Fin 32) a0 0,
   .alu .mul a0 (7 : Fin 32) (31 : Fin 32), .lw a1 sp 0xC, .alu .add a1 a1 a0, .alu .mul (23 : Fin 32) (19 : Fin 32) a1,
   .alu .mulhu a2 (7 : Fin 32) (31 : Fin 32), .alu .mul a4 (23 : Fin 32) (28 : Fin 32),
   .alu .mulhu (9 : Fin 32) (23 : Fin 32) (28 : Fin 32), .alu .sltu a0 a1 a0, .alu .add a0 a0 a2, .alu .add a1 a1 a4,
   .alu .add a0 a0 (9 : Fin 32), .alu .sltu a2 a1 a4, .aluImm .add (25 : Fin 32) x0 0xB, .alu .add a2 a2 a0,
   .alu .sltu a4 a0 (9 : Fin 32), .alu .sltu a0 a2 a0, .alu .add (26 : Fin 32) x0 (5 : Fin 32),
   .alu .add (24 : Fin 32) a4 a0, .alu .add a4 x0 (17 : Fin 32), .alu .add (9 : Fin 32) x0 a6]

/-- The end of a pass, from 0xDA: add the old top carry into the last word,
store it, and count the pass. -/
def sqTailBlock : List BInstr :=
  [.alu .add (21 : Fin 32) (21 : Fin 32) a2, .alu .add a0 (24 : Fin 32) (29 : Fin 32), .alu .sltu a1 (21 : Fin 32) a2,
   .sw sp (21 : Fin 32) 0x38, .alu .add (21 : Fin 32) a0 a1, .aluImm .add (30 : Fin 32) (30 : Fin 32) 1,
   .aluImm .add (29 : Fin 32) x0 0]

section
set_option maxRecDepth 20000
theorem sqHeadBlock_end : blockEnd sqMont12Code 0x42 sqHeadBlock = some 0x88 := by decide
theorem sqTailBlock_end : blockEnd sqMont12Code 0xDA sqTailBlock = some 0xEE := by decide
end

/-- The registers the start of a pass leaves alone. -/
def sqHeadKeep (q : Fin 32) : Bool := q.val ∉ [9, 10, 11, 12, 14, 23, 24, 25, 26, 31]

set_option maxRecDepth 20000 in
theorem sqHeadBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqHeadBlock (M, f)).1 = M ∧
    (runBlock sqHeadBlock (M, f)).2 (31 : Fin 32) =
      memLoad32 M (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (20 : Fin 32)) + 0) ∧
    (runBlock sqHeadBlock (M, f)).2 (23 : Fin 32) = (mmHead (f (7 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (28 : Fin 32))).1 ∧
    (runBlock sqHeadBlock (M, f)).2 a2 = (mmHead (f (7 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (28 : Fin 32))).2.1 ∧
    (runBlock sqHeadBlock (M, f)).2 (24 : Fin 32) = (mmHead (f (7 : Fin 32))
      (memLoad32 M (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (20 : Fin 32)) + 0))
      (memLoad32 M (f sp + 0xC)) (f (19 : Fin 32)) (f (28 : Fin 32))).2.2 ∧
    (runBlock sqHeadBlock (M, f)).2 (25 : Fin 32) = BitVec.ofNat 32 (11 - 0) ∧
    (runBlock sqHeadBlock (M, f)).2 (26 : Fin 32) = f (5 : Fin 32) ∧
    (runBlock sqHeadBlock (M, f)).2 a4 = f (17 : Fin 32) ∧
    (runBlock sqHeadBlock (M, f)).2 (9 : Fin 32) = f a6 ∧
    ∀ q, sqHeadKeep q = true → (runBlock sqHeadBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqHeadBlock]
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
        pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a4) hq rfl, pkeep_ne (r := 24) hq rfl, pkeep_ne (r := 25) hq rfl,
        pkeep_ne (r := 26) hq rfl, pkeep_ne (r := 23) hq rfl, pkeep_ne (r := 31) hq rfl]

theorem sqHeadBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hx : (aluEval .add (aluEval .sll (f (30 : Fin 32)) 2) (f (20 : Fin 32)) + 0).toNat % 4 = 0)
    (hs : (f sp + 0xC).toNat % 4 = 0) : BlockOk base len sqHeadBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, sqHeadBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hx, hs⟩

/-- The registers the end of a pass leaves alone. -/
def sqTailKeep (q : Fin 32) : Bool := q.val ∉ [10, 11, 21, 29, 30]

set_option maxRecDepth 20000 in
theorem sqTailBlock_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqTailBlock (M, f)).1 = memStore32 M (f sp + 0x38) (aluEval .add (f (21 : Fin 32)) (f a2)) ∧
    (runBlock sqTailBlock (M, f)).2 (21 : Fin 32) = aluEval .add (aluEval .add (f (24 : Fin 32)) (f (29 : Fin 32)))
      (aluEval .sltu (aluEval .add (f (21 : Fin 32)) (f a2)) (f a2)) ∧
    (runBlock sqTailBlock (M, f)).2 (30 : Fin 32) = f (30 : Fin 32) + 1 ∧
    (runBlock sqTailBlock (M, f)).2 (29 : Fin 32) = 0 ∧
    ∀ q, sqTailKeep q = true → (runBlock sqTailBlock (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqTailBlock]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
        pkeep_ne (r := 21) hq rfl, pkeep_ne (r := 29) hq rfl, pkeep_ne (r := 30) hq rfl]

theorem sqTailBlock_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hs : (f sp + 0x38).toNat % 4 = 0) (hsep : Sep (f sp + 0x38) 4 base len) :
    BlockOk base len sqTailBlock (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, sqTailBlock, upd, ↓reduceIte, true_and, and_true]
  exact ⟨hs, hsep⟩

/-- The registers a pass of the squaring leaves alone. -/
def sqPassKeep (q : Fin 32) : Bool := q.val ∉ [8, 9, 10, 11, 12, 13, 14, 15, 21, 23, 24, 25, 26, 29, 30, 31]

theorem sqPassKeep_head : ∀ q, sqPassKeep q = true → sqHeadKeep q = true := by decide
theorem sqPassKeep_body : ∀ q, sqPassKeep q = true → bodyKeep q = true := by decide
theorem sqPassKeep_tail : ∀ q, sqPassKeep q = true → sqTailKeep q = true := by decide

set_option exponentiation.threshold 400 in
/-- **One pass of the outer loop**, from 0x42: add limb `i` of the first
operand times the second operand, and `u` times the modulus, to the
accumulator and its top carry in `s6`, and shift the sum down a word. -/
theorem sq_pass {B acc xp yp np K : Word} {M0 : Word → BitVec 8} {i : Nat} (hi : i < 12)
    (hxp : xp.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAX : Sep acc 48 xp 48) (hAY : Sep acc 48 yp 48) (hAN : Sep acc 48 np 48)
    (hAC : Sep acc 48 B sqMont12Code.length)
    (hk : (K.toNat * (memLoad32 M0 np).toNat + 1) % 2 ^ 32 = 0)
    {M : Word → BitVec 8} {n : Machine} (s : St M B n 0x42 (reg n)) (hc : CodeIn M B sqMont12Code)
    (hfr : ∀ a, Sep acc 48 a 1 → M a = M0 a)
    (r29 : reg n (30 : Fin 32) = BitVec.ofNat 32 i) (r20 : reg n (20 : Fin 32) = xp)
    (r6 : reg n (7 : Fin 32) = memLoad32 M0 yp) (r7 : reg n (28 : Fin 32) = memLoad32 M0 np)
    (r19 : reg n (19 : Fin 32) = K) (rsp : reg n sp + 0xC = acc)
    (rsp38 : reg n sp + 0x38 = acc + BitVec.ofNat 32 (4 * 11))
    (r17 : reg n (5 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)))
    (r16 : reg n (17 : Fin 32) = acc + BitVec.ofNat 32 (4 * (0 + 1)))
    (r21 : reg n a6 = yp + BitVec.ofNat 32 (4 * (0 + 1)))
    (r28 : reg n (29 : Fin 32) = 0) (r5 : reg n (6 : Fin 32) = 12) :
    ∃ n' M', Steps n n' ∧ St M' B n' (if i + 1 < 12 then 0x42 else 0xF2) (reg n') ∧ CodeIn M' B sqMont12Code ∧
      (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
      (∃ u : Nat, u < 2 ^ 32 ∧ 2 ^ 32 * (accV M' acc 12 + (reg n' (21 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M acc 12 + (reg n (21 : Fin 32)).toNat * 2 ^ (32 * 12) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 yp 12 + u * accV M0 np 12) ∧
      reg n' (30 : Fin 32) = BitVec.ofNat 32 (i + 1) ∧ reg n' (29 : Fin 32) = 0 ∧
      ∀ q, sqPassKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hX : aluEval .add (aluEval .sll (reg n (30 : Fin 32)) 2) (reg n (20 : Fin 32)) + 0 =
      xp + BitVec.ofNat 32 (4 * i) := by
    rw [r29, r20, sll12 i hi, add_lit_zero]; exact BitVec.add_comm _ _
  have ok1 := sqHeadBlock_ok (M := M) (f := reg n) (base := B) (len := sqMont12Code.length)
    (by rw [hX]; exact aligned_add hxp (by omega)) (by rw [rsp]; exact hacc)
  obtain ⟨n1, c1, u1⟩ := St.block sqHeadBlock s hc sqHeadBlock_end ok1
  obtain ⟨hm1, h30, h31, h2, h24, h25, h26, h3, h9, hfr1⟩ := sqHeadBlock_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [hm1] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock sqHeadBlock (M, reg n)).2 q := u1.regs
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
  obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 0x8C sq_at_88 (by decide) hb
  have g2 : ∀ q, reg n2 q = (runBlock sqHeadBlock (M, reg n)).2 q := fun q => by rw [u2.regs, g1]
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
    sq_inner (M0 := M) (U := u) (X := memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) hnp hyp hacc hw hAY hAN hAC
      10 0 (by decide) u2.self hc (fun _ _ => rfl) (fun _ _ _ => rfl) inv0 bd
      (by rw [g2, h26, r17]) (by rw [g2, h9, r21]) (by rw [g2, h3, r16]) (by rw [g2, h31]) (by rw [g2, h30])
      (by rw [g2, h2]) (by rw [g2, h24]) (by rw [g2, h25])
  have k3 : ∀ q, sqPassKeep q = true → reg n3 q = reg n q := fun q hq => by
    rw [fr3 q (sqPassKeep_body q hq), g2, hfr1 q (sqPassKeep_head q hq)]
  have hb3 : ∀ q, sqHeadKeep q = true → bodyKeep q = true → reg n3 q = reg n q := fun q h1 h2 => by
    rw [fr3 q h2, g2, hfr1 q h1]
  have sp3 : reg n3 sp = reg n sp := k3 sp rfl
  have ok3 := sqTailBlock_ok (M := M1) (f := reg n3) (base := B) (len := sqMont12Code.length)
    (by rw [sp3, rsp38]; exact aligned_add hacc (by omega)) (by rw [sp3, rsp38]; exact hAC.sub (by omega))
  obtain ⟨n4, c4, u4⟩ := St.block sqTailBlock u3 hc3 sqTailBlock_end ok3
  obtain ⟨hm4, t22, t29, t28, tfr⟩ := sqTailBlock_run (M := M1) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [hm4, sp3, rsp38] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock sqTailBlock (M1, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := aluEval .add (reg n3 (21 : Fin 32)) (reg n3 a2)) hc3 (hAC.sub (c := 4 * 11) (by omega))
  have e29 : reg n4 (30 : Fin 32) = BitVec.ofNat 32 (i + 1) := by
    rw [g4, t29, hb3 (30 : Fin 32) rfl rfl, r29, ofNat_succ]
  have e28 : reg n4 (29 : Fin 32) = 0 := by rw [g4, t28]
  have k4 : ∀ q, sqPassKeep q = true → reg n4 q = reg n q := fun q hq => by
    rw [g4, tfr q (sqPassKeep_tail q hq), k3 q hq]
  have hb4 : branchTaken .bne (reg n4 (30 : Fin 32)) (reg n4 (6 : Fin 32)) = decide (i + 1 < 12) := by
    rw [e29, k4 _ rfl, r5]; exact pass_ne i hi
  -- the arithmetic of the pass
  have arith : 2 ^ 32 * (accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11))
        (aluEval .add (reg n3 (21 : Fin 32)) (reg n3 a2))) acc 12 + (reg n4 (21 : Fin 32)).toNat * 2 ^ (32 * 12)) =
      accV M acc 12 + (reg n (21 : Fin 32)).toNat * 2 ^ (32 * 12) +
        (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).toNat * accV M0 yp 12 + u.toNat * accV M0 np 12 := by
    have hA : accV (memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11)) (aluEval .add (reg n3 (21 : Fin 32)) (reg n3 a2)))
        acc 12 = accV M1 acc 11 + (aluEval .add (reg n3 (21 : Fin 32)) (reg n3 a2)).toNat * 2 ^ (32 * 11) := by
      rw [show (12 : Nat) = 11 + 1 from rfl, accV_succ1, accV_store_above (by omega) 11 (Nat.le_refl 11),
        memLoad32_store32_same]
    have ac := add_carry (reg n3 (21 : Fin 32)) (reg n3 a2)
    have hch : (reg n3 (24 : Fin 32)).toNat ≤ 1 := by omega
    have hcy : (aluEval .sltu (aluEval .add (reg n3 (21 : Fin 32)) (reg n3 a2)) (reg n3 a2)).toNat ≤ 1 := by
      have := (reg n3 (21 : Fin 32)).isLt; have := (reg n3 a2).isLt; omega
    have h22 : (reg n4 (21 : Fin 32)).toNat = (reg n3 (24 : Fin 32)).toNat +
        (aluEval .sltu (aluEval .add (reg n3 (21 : Fin 32)) (reg n3 a2)) (reg n3 a2)).toNat := by
      rw [g4, t22, hb3 (29 : Fin 32) rfl rfl, r28, show aluEval .add (reg n3 (24 : Fin 32)) 0 = reg n3 (24 : Fin 32) from
        BitVec.add_zero _, add_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    have p12 : (2 : Nat) ^ (32 * 12) = 2 ^ (32 * 11) * 2 ^ 32 := pow32_succ 11
    rw [eX, accV_frame48 (b := yp) (n := 12) hfr hAY, accV_frame48 (b := np) (n := 12) hfr hAN, p12] at I1
    rw [hA, h22, p12, hb3 (21 : Fin 32) rfl rfl]
    rw [hb3 (21 : Fin 32) rfl rfl] at ac
    exact mm_tail_arith I1 ac
  have fr4 : ∀ a, Sep acc 48 a 1 → memStore32 M1 (acc + BitVec.ofNat 32 (4 * 11))
      (aluEval .add (reg n3 (21 : Fin 32)) (reg n3 a2)) a = M0 a := fun a ha => by
    rw [memStore32_ne fun j hj e => (ha.point (i := 4 * 11 + j) (j := 0) (by omega) (by decide)) (by
      rw [add_ofNat_zero, ← add_ofNat_assoc]; exact e.symm), I3 a ha, hfr a ha]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x42 sq_at_ee (by decide) (by rw [hb4]; exact decide_eq_true hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e29], by rw [g5, e28], fun q hq => by rw [g5, k4 q hq]⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0xF2 sq_at_ee (by decide) (by rw [hb4]; exact decide_eq_false hl)
    have g5 : ∀ q, reg n5 q = reg n4 q := u5.regs
    refine ⟨n5, _, Steps.trans c1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      hc4, fr4, ⟨u.toNat, u.isLt, by rw [g5]; exact arith⟩, by rw [g5, e29], by rw [g5, e28], fun q hq => by rw [g5, k4 q hq]⟩


set_option exponentiation.threshold 400 in
/-- **The outer loop**, from pass `i` to its end at 0xF2. The accumulator
and its top carry hold a sum `T` with `2^(32 i) T = X_i Y + U N`, for `X_i`
the first operand's low `i` limbs and some `U`, and `T < 2N`. -/
theorem sq_outer {B acc xp yp np K : Word} {M0 : Word → BitVec 8}
    (hxp : xp.toNat % 4 = 0) (hyp : yp.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hw : acc.toNat + 48 ≤ 2 ^ 32) (hAX : Sep acc 48 xp 48) (hAY : Sep acc 48 yp 48) (hAN : Sep acc 48 np 48)
    (hAC : Sep acc 48 B sqMont12Code.length)
    (hk : (K.toNat * (memLoad32 M0 np).toNat + 1) % 2 ^ 32 = 0) (hYN : accV M0 yp 12 < accV M0 np 12) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M B n 0x42 (reg n) → CodeIn M B sqMont12Code → (∀ a, Sep acc 48 a 1 → M a = M0 a) →
      (∃ U, 2 ^ (32 * i) * (accV M acc 12 + (reg n (21 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M0 xp i * accV M0 yp 12 + U * accV M0 np 12) →
      accV M acc 12 + (reg n (21 : Fin 32)).toNat * 2 ^ (32 * 12) < 2 * accV M0 np 12 →
      reg n (30 : Fin 32) = BitVec.ofNat 32 i → reg n (20 : Fin 32) = xp →
      reg n (7 : Fin 32) = memLoad32 M0 yp → reg n (28 : Fin 32) = memLoad32 M0 np →
      reg n (19 : Fin 32) = K → reg n sp + 0xC = acc →
      reg n sp + 0x38 = acc + BitVec.ofNat 32 (4 * 11) →
      reg n (5 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (17 : Fin 32) = acc + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n a6 = yp + BitVec.ofNat 32 (4 * (0 + 1)) →
      reg n (29 : Fin 32) = 0 → reg n (6 : Fin 32) = 12 →
      ∃ n' M', Steps n n' ∧ St M' B n' 0xF2 (reg n') ∧ CodeIn M' B sqMont12Code ∧
        (∀ a, Sep acc 48 a 1 → M' a = M0 a) ∧
        (∃ U, 2 ^ (32 * 12) * (accV M' acc 12 + (reg n' (21 : Fin 32)).toNat * 2 ^ (32 * 12)) =
          accV M0 xp 12 * accV M0 yp 12 + U * accV M0 np 12) ∧
        accV M' acc 12 + (reg n' (21 : Fin 32)).toNat * 2 ^ (32 * 12) < 2 * accV M0 np 12 ∧
        ∀ q, sqPassKeep q = true → reg n' q = reg n q := by
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hinv hbd r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e29, e28, k1⟩ := sq_pass (i := 11) (by decide) hxp hyp hnp hacc
      hw hAX hAY hAN hAC hk s hc hfr r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * 11))).isLt hu hYN
    refine ⟨n1, M1, c1, u1, hc1, hf1, ⟨U + 2 ^ (32 * 11) * u, ?_⟩, a2, k1⟩
    rw [pow32_succ 11] at a1 ⊢
    rw [a1, accV_succ1 M0 xp 11]
  | succ m ih =>
    intro i hi M n s hc hfr hinv hbd r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    have hl : i + 1 < 12 := idx_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, ⟨u, hu, hp⟩, e29, e28, k1⟩ := sq_pass (i := i) (Nat.lt_trans (Nat.lt_succ_self i) hl) hxp hyp hnp hacc
      hw hAX hAY hAN hAC hk s hc hfr r29 r20 r6 r7 r19 rsp rsp38 r17 r16 r21 r28 r5
    rw [ite_eq_left hl] at u1
    obtain ⟨U, hU⟩ := hinv
    obtain ⟨a1, a2⟩ := mm_outer_arith (by decide) hp hU hbd (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))).isLt hu hYN
    have inv1 : ∃ U, 2 ^ (32 * (i + 1)) * (accV M1 acc 12 + (reg n1 (21 : Fin 32)).toNat * 2 ^ (32 * 12)) =
        accV M0 xp (i + 1) * accV M0 yp 12 + U * accV M0 np 12 :=
      ⟨U + 2 ^ (32 * i) * u, by rw [pow32_succ i, a1, accV_succ1 M0 xp i]⟩
    obtain ⟨n', M', c', u', hc', hf', hv', hb', k'⟩ := ih (i + 1) (idx_succ hi) u1 hc1 hf1 inv1 a2 e29
      (by rw [k1 _ rfl, r20]) (by rw [k1 _ rfl, r6]) (by rw [k1 _ rfl, r7]) (by rw [k1 _ rfl, r19])
      (by rw [k1 _ rfl, rsp]) (by rw [k1 _ rfl, rsp38]) (by rw [k1 _ rfl, r17]) (by rw [k1 _ rfl, r16])
      (by rw [k1 _ rfl, r21]) e28 (by rw [k1 _ rfl, r5])
    exact ⟨n', M', c1.trans c', u', hc', hf', hv', hb', fun q hq => by rw [k' q hq, k1 q hq]⟩

end C3.RV32
