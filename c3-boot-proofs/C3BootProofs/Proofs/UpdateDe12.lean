import C3BootProofs.Proofs.LincombShiftMod12
import C3BootProofs.Proofs.FromI64

/-!
# `safegcd::update_de::<12>`

The compiled function turns each row of the transition matrix into two
`Int<2>` values with `Int<2>::from_i64`, stores `mi` in its frame, and
computes the new `d` and `e` with `lincomb_int_reduce_shift_mod`.
`fromI64_correct` and `lincombShiftMod12_correct` prove the calls.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000

theorem ud12_at_0 : fetchRel updateDe12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem ud12_at_2 : fetchRel updateDe12Code 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem ud12_at_4 : fetchRel updateDe12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem ud12_at_6 : fetchRel updateDe12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem ud12_at_8 : fetchRel updateDe12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem ud12_at_a : fetchRel updateDe12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem ud12_at_c : fetchRel updateDe12Code 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem ud12_at_e : fetchRel updateDe12Code 0xE = some (.store .sw sp (21 : Fin 32) 0x34, 2) := by decide
theorem ud12_at_10 : fetchRel updateDe12Code 0x10 = some (.store .sw sp (22 : Fin 32) 0x30, 2) := by decide
theorem ud12_at_12 : fetchRel updateDe12Code 0x12 = some (.store .sw sp (23 : Fin 32) 0x2C, 2) := by decide
theorem ud12_at_14 : fetchRel updateDe12Code 0x14 = some (.alu .add (18 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem ud12_at_16 : fetchRel updateDe12Code 0x16 = some (.alu .add (9 : Fin 32) x0 a6, 2) := by decide
theorem ud12_at_18 : fetchRel updateDe12Code 0x18 = some (.alu .add (22 : Fin 32) x0 a5, 2) := by decide
theorem ud12_at_1a : fetchRel updateDe12Code 0x1A = some (.alu .add (23 : Fin 32) x0 a4, 2) := by decide
theorem ud12_at_1c : fetchRel updateDe12Code 0x1C = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem ud12_at_1e : fetchRel updateDe12Code 0x1E = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem ud12_at_20 : fetchRel updateDe12Code 0x20 = some (.alu .add (21 : Fin 32) x0 a1, 2) := by decide
theorem ud12_at_22 : fetchRel updateDe12Code 0x22 = some (.alu .add a3 x0 a6, 2) := by decide
theorem ud12_at_24 : fetchRel updateDe12Code 0x24 = some (.load .lw a1 a3 0x0, 2) := by decide
theorem ud12_at_26 : fetchRel updateDe12Code 0x26 = some (.load .lw a2 a3 0x4, 2) := by decide
theorem ud12_at_28 : fetchRel updateDe12Code 0x28 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem ud12_at_2a : fetchRel updateDe12Code 0x2A = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ud12_at_2c : fetchRel updateDe12Code 0x2C = some (.auipc ra 0x0, 4) := by decide
theorem ud12_at_30 : fetchRel updateDe12Code 0x30 = some (.jalr ra ra 0x86, 4) := by decide
theorem ud12_at_34 : fetchRel updateDe12Code 0x34 = some (.load .lw a1 (9 : Fin 32) 0x8, 2) := by decide
theorem ud12_at_36 : fetchRel updateDe12Code 0x36 = some (.load .lw a2 (9 : Fin 32) 0xC, 2) := by decide
theorem ud12_at_38 : fetchRel updateDe12Code 0x38 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem ud12_at_3a : fetchRel updateDe12Code 0x3A = some (.auipc ra 0x0, 4) := by decide
theorem ud12_at_3e : fetchRel updateDe12Code 0x3E = some (.jalr ra ra 0x78, 4) := by decide
theorem ud12_at_42 : fetchRel updateDe12Code 0x42 = some (.store .sw sp (23 : Fin 32) 0x24, 2) := by decide
theorem ud12_at_44 : fetchRel updateDe12Code 0x44 = some (.store .sw sp (22 : Fin 32) 0x28, 2) := by decide
theorem ud12_at_46 : fetchRel updateDe12Code 0x46 = some (.aluImm .add a3 sp 0x4, 2) := by decide
theorem ud12_at_48 : fetchRel updateDe12Code 0x48 = some (.aluImm .add a4 sp 0xC, 2) := by decide
theorem ud12_at_4a : fetchRel updateDe12Code 0x4A = some (.aluImm .add (17 : Fin 32) sp 0x24, 4) := by decide
theorem ud12_at_4e : fetchRel updateDe12Code 0x4E = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem ud12_at_50 : fetchRel updateDe12Code 0x50 = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem ud12_at_52 : fetchRel updateDe12Code 0x52 = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem ud12_at_54 : fetchRel updateDe12Code 0x54 = some (.alu .add a5 x0 (18 : Fin 32), 2) := by decide
theorem ud12_at_56 : fetchRel updateDe12Code 0x56 = some (.alu .add a6 x0 (19 : Fin 32), 2) := by decide
theorem ud12_at_58 : fetchRel updateDe12Code 0x58 = some (.auipc ra 0x0, 4) := by decide
theorem ud12_at_5c : fetchRel updateDe12Code 0x5C = some (.jalr ra ra 0xFFFFF84E, 4) := by decide
theorem ud12_at_60 : fetchRel updateDe12Code 0x60 = some (.load .lw a1 (9 : Fin 32) 0x10, 2) := by decide
theorem ud12_at_62 : fetchRel updateDe12Code 0x62 = some (.load .lw a2 (9 : Fin 32) 0x14, 2) := by decide
theorem ud12_at_64 : fetchRel updateDe12Code 0x64 = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem ud12_at_66 : fetchRel updateDe12Code 0x66 = some (.auipc ra 0x0, 4) := by decide
theorem ud12_at_6a : fetchRel updateDe12Code 0x6A = some (.jalr ra ra 0x4C, 4) := by decide
theorem ud12_at_6e : fetchRel updateDe12Code 0x6E = some (.load .lw a1 (9 : Fin 32) 0x18, 2) := by decide
theorem ud12_at_70 : fetchRel updateDe12Code 0x70 = some (.load .lw a2 (9 : Fin 32) 0x1C, 2) := by decide
theorem ud12_at_72 : fetchRel updateDe12Code 0x72 = some (.aluImm .add a0 sp 0x1C, 2) := by decide
theorem ud12_at_74 : fetchRel updateDe12Code 0x74 = some (.auipc ra 0x0, 4) := by decide
theorem ud12_at_78 : fetchRel updateDe12Code 0x78 = some (.jalr ra ra 0x3E, 4) := by decide
theorem ud12_at_7c : fetchRel updateDe12Code 0x7C = some (.store .sw sp (23 : Fin 32) 0x24, 2) := by decide
theorem ud12_at_7e : fetchRel updateDe12Code 0x7E = some (.store .sw sp (22 : Fin 32) 0x28, 2) := by decide
theorem ud12_at_80 : fetchRel updateDe12Code 0x80 = some (.aluImm .add a0 (8 : Fin 32) 0x34, 4) := by decide
theorem ud12_at_84 : fetchRel updateDe12Code 0x84 = some (.aluImm .add a3 sp 0x14, 2) := by decide
theorem ud12_at_86 : fetchRel updateDe12Code 0x86 = some (.aluImm .add a4 sp 0x1C, 2) := by decide
theorem ud12_at_88 : fetchRel updateDe12Code 0x88 = some (.aluImm .add (17 : Fin 32) sp 0x24, 4) := by decide
theorem ud12_at_8c : fetchRel updateDe12Code 0x8C = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem ud12_at_8e : fetchRel updateDe12Code 0x8E = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem ud12_at_90 : fetchRel updateDe12Code 0x90 = some (.alu .add a5 x0 (18 : Fin 32), 2) := by decide
theorem ud12_at_92 : fetchRel updateDe12Code 0x92 = some (.alu .add a6 x0 (19 : Fin 32), 2) := by decide
theorem ud12_at_94 : fetchRel updateDe12Code 0x94 = some (.auipc ra 0x0, 4) := by decide
theorem ud12_at_98 : fetchRel updateDe12Code 0x98 = some (.jalr ra ra 0xFFFFF812, 4) := by decide
theorem ud12_at_9c : fetchRel updateDe12Code 0x9C = some (.load .lw ra sp 0x4C, 2) := by decide
theorem ud12_at_9e : fetchRel updateDe12Code 0x9E = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem ud12_at_a0 : fetchRel updateDe12Code 0xA0 = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem ud12_at_a2 : fetchRel updateDe12Code 0xA2 = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem ud12_at_a4 : fetchRel updateDe12Code 0xA4 = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem ud12_at_a6 : fetchRel updateDe12Code 0xA6 = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem ud12_at_a8 : fetchRel updateDe12Code 0xA8 = some (.load .lw (21 : Fin 32) sp 0x34, 2) := by decide
theorem ud12_at_aa : fetchRel updateDe12Code 0xAA = some (.load .lw (22 : Fin 32) sp 0x30, 2) := by decide
theorem ud12_at_ac : fetchRel updateDe12Code 0xAC = some (.load .lw (23 : Fin 32) sp 0x2C, 2) := by decide
theorem ud12_at_ae : fetchRel updateDe12Code 0xAE = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem ud12_at_b0 : fetchRel updateDe12Code 0xB0 = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- The prologue, to the first `from_i64` call at 0x2C. -/
def udPro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFB0, .sw sp ra 0x4C, .sw sp (8 : Fin 32) 0x48, .sw sp (9 : Fin 32) 0x44,
   .sw sp (18 : Fin 32) 0x40, .sw sp (19 : Fin 32) 0x3C, .sw sp (20 : Fin 32) 0x38, .sw sp (21 : Fin 32) 0x34,
   .sw sp (22 : Fin 32) 0x30, .sw sp (23 : Fin 32) 0x2C, .alu .add (18 : Fin 32) x0 (17 : Fin 32),
   .alu .add (9 : Fin 32) x0 a6, .alu .add (22 : Fin 32) x0 a5, .alu .add (23 : Fin 32) x0 a4,
   .alu .add (19 : Fin 32) x0 a3, .alu .add (20 : Fin 32) x0 a2, .alu .add (21 : Fin 32) x0 a1,
   .alu .add a3 x0 a6, .lw a1 a3 0, .lw a2 a3 4, .alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 4]
/-- Loads a matrix entry from `s1 + o` and points `a0` at `sp + d`. -/
def udLd (o d : Word) : List BInstr := [.lw a1 (9 : Fin 32) o, .lw a2 (9 : Fin 32) (o + 4), .aluImm .add a0 sp d]
def udB2 : List BInstr :=
  [.sw sp (23 : Fin 32) 0x24, .sw sp (22 : Fin 32) 0x28, .aluImm .add a3 sp 4, .aluImm .add a4 sp 0xC,
   .aluImm .add (17 : Fin 32) sp 0x24, .alu .add a0 x0 (8 : Fin 32), .alu .add a1 x0 (21 : Fin 32),
   .alu .add a2 x0 (20 : Fin 32), .alu .add a5 x0 (18 : Fin 32), .alu .add a6 x0 (19 : Fin 32)]
def udB5 : List BInstr :=
  [.sw sp (23 : Fin 32) 0x24, .sw sp (22 : Fin 32) 0x28, .aluImm .add a0 (8 : Fin 32) 0x34, .aluImm .add a3 sp 0x14,
   .aluImm .add a4 sp 0x1C, .aluImm .add (17 : Fin 32) sp 0x24, .alu .add a1 x0 (21 : Fin 32),
   .alu .add a2 x0 (20 : Fin 32), .alu .add a5 x0 (18 : Fin 32), .alu .add a6 x0 (19 : Fin 32)]
/-- The saved registers and their frame slots. -/
def udPs : List (Fin 32 × Word) :=
  [(ra, 0x4C), (8, 0x48), (9, 0x44), (18, 0x40), (19, 0x3C), (20, 0x38), (21, 0x34), (22, 0x30), (23, 0x2C)]

section
set_option maxRecDepth 20000
theorem udPro_end : blockEnd updateDe12Code 0 udPro = some 0x2C := by decide
theorem udB1_end : blockEnd updateDe12Code 0x34 (udLd 8 0xC) = some 0x3A := by decide
theorem udB2_end : blockEnd updateDe12Code 0x42 udB2 = some 0x58 := by decide
theorem udB3_end : blockEnd updateDe12Code 0x60 (udLd 0x10 0x14) = some 0x66 := by decide
theorem udB4_end : blockEnd updateDe12Code 0x6E (udLd 0x18 0x1C) = some 0x74 := by decide
theorem udB5_end : blockEnd updateDe12Code 0x7C udB5 = some 0x94 := by decide
theorem udEpi_end : blockEnd updateDe12Code 0x9C (restoreBlock udPs) = some 0xAE := by decide
end


theorem ud_zadd (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

set_option maxRecDepth 200000 in
theorem udPro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock udPro (M, f)).1 = saveMem M (f sp + 0xFFFFFFB0) f udPs ∧
    (runBlock udPro (M, f)).2 sp = f sp + 0xFFFFFFB0 ∧
    (runBlock udPro (M, f)).2 (18 : Fin 32) = f 17 ∧ (runBlock udPro (M, f)).2 (9 : Fin 32) = f a6 ∧
    (runBlock udPro (M, f)).2 (22 : Fin 32) = f a5 ∧ (runBlock udPro (M, f)).2 (23 : Fin 32) = f a4 ∧
    (runBlock udPro (M, f)).2 (19 : Fin 32) = f a3 ∧ (runBlock udPro (M, f)).2 (20 : Fin 32) = f a2 ∧
    (runBlock udPro (M, f)).2 (21 : Fin 32) = f a1 ∧
    (runBlock udPro (M, f)).2 a1 = memLoad32 (saveMem M (f sp + 0xFFFFFFB0) f udPs) (f a6) ∧
    (runBlock udPro (M, f)).2 a2 = memLoad32 (saveMem M (f sp + 0xFFFFFFB0) f udPs) (f a6 + 4) ∧
    (runBlock udPro (M, f)).2 (8 : Fin 32) = f a0 ∧ (runBlock udPro (M, f)).2 a0 = f sp + 0xFFFFFFB0 + 4 ∧
    ∀ q : Fin 32, q.val ∉ [2, 8, 9, 10, 11, 12, 13, 18, 19, 20, 21, 22, 23] → (runBlock udPro (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, udPro] <;>
    simp +decide only [upd, ↓reduceIte, saveMem, udPs, ev_add, BitVec.add_assoc, hz, add_lit_zero, ud_zadd] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem udLd_run {M : Word → BitVec 8} {f : Fin 32 → Word} {o d : Word} (hz : f 0 = 0) :
    (runBlock (udLd o d) (M, f)).1 = M ∧ (runBlock (udLd o d) (M, f)).2 a1 = memLoad32 M (f 9 + o) ∧
    (runBlock (udLd o d) (M, f)).2 a2 = memLoad32 M (f 9 + (o + 4)) ∧ (runBlock (udLd o d) (M, f)).2 a0 = f sp + d ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12] → (runBlock (udLd o d) (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  all_goals simp only [runBlock, BInstr.run, udLd]
  any_goals (simp +decide only [upd, ↓reduceIte, ev_add]; done)
  all_goals try (simp +decide only [upd, ↓reduceIte, ev_add]; rfl)
  have nq : ∀ w : Fin 32, w.val ∈ [10, 11, 12] → q ≠ w := fun w hw e => hq (e ▸ hw)
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [hz]
  · simp only [upd, h0, nq a0 (by decide), nq a1 (by decide), nq a2 (by decide), ite_false]

set_option maxRecDepth 20000 in
theorem udB2_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock udB2 (M, f)).1 = memStore32 (memStore32 M (f sp + 0x24) (f 23)) (f sp + 0x28) (f 22) ∧
    (runBlock udB2 (M, f)).2 a3 = f sp + 4 ∧ (runBlock udB2 (M, f)).2 a4 = f sp + 0xC ∧
    (runBlock udB2 (M, f)).2 (17 : Fin 32) = f sp + 0x24 ∧ (runBlock udB2 (M, f)).2 a0 = f 8 ∧
    (runBlock udB2 (M, f)).2 a1 = f 21 ∧ (runBlock udB2 (M, f)).2 a2 = f 20 ∧ (runBlock udB2 (M, f)).2 a5 = f 18 ∧
    (runBlock udB2 (M, f)).2 a6 = f 19 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13, 14, 15, 16, 17] → (runBlock udB2 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, udB2] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem udB5_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock udB5 (M, f)).1 = memStore32 (memStore32 M (f sp + 0x24) (f 23)) (f sp + 0x28) (f 22) ∧
    (runBlock udB5 (M, f)).2 a0 = f 8 + 0x34 ∧ (runBlock udB5 (M, f)).2 a3 = f sp + 0x14 ∧
    (runBlock udB5 (M, f)).2 a4 = f sp + 0x1C ∧ (runBlock udB5 (M, f)).2 (17 : Fin 32) = f sp + 0x24 ∧
    (runBlock udB5 (M, f)).2 a1 = f 21 ∧ (runBlock udB5 (M, f)).2 a2 = f 20 ∧ (runBlock udB5 (M, f)).2 a5 = f 18 ∧
    (runBlock udB5 (M, f)).2 a6 = f 19 ∧
    ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13, 14, 15, 16, 17] → (runBlock udB5 (M, f)).2 q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => runBlock_keepL (by decide) hz hq⟩ <;>
    simp only [runBlock, BInstr.run, udB5] <;> simp +decide only [upd, ↓reduceIte, ev_add, hz] <;>
    first | rfl | exact BitVec.zero_add _ | skip

set_option maxRecDepth 20000 in
theorem udEpi_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (∀ r o, (r, o) ∈ udPs → (runBlock (restoreBlock udPs) (M, f)).2 r = memLoad32 M (f sp + o)) ∧
    (runBlock (restoreBlock udPs) (M, f)).1 = M ∧
    ∀ q : Fin 32, q.val ∉ [1, 8, 9, 18, 19, 20, 21, 22, 23] → (runBlock (restoreBlock udPs) (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, restoreBlock, udPs, List.map]
  refine ⟨fun r o h => ?_, trivial, fun q hq => ?_⟩
  · simp only [udPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd, ↓reduceIte, ev_add]
  · have nq : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19, 20, 21, 22, 23] → q ≠ w := fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp only [upd, h0, nq ra (by decide), nq 8 (by decide), nq 9 (by decide), nq 18 (by decide),
        nq 19 (by decide), nq 20 (by decide), nq 21 (by decide), nq 22 (by decide), nq 23 (by decide), ite_false]


/-- Where `lincomb_int_reduce_shift_mod` is, from `update_de`. -/
abbrev udL (P : Word) : Word := P + 0xFFFFF8A6

/-- Where `update_de::<12>` runs: its code and its callees', the 0x380
bytes of stack at `G` that it and its callees use (its frame is the top
0x50), the result pair `out`, the operands `d` and `e`, the modulus `mp`,
and the matrix `tp`, each apart from what it must not touch. -/
structure UDEnv (M : Word → BitVec 8) (P G out ap bp mp tp : Word) : Prop where
  hP : P.toNat % 2 = 0
  lmc : CodeIn M (udL P) lincombShiftMod12Code
  lc : CodeIn M (lmLc (udL P)) lincomb12Code
  abs : CodeIn M (lmLc (udL P) + 0xFFFFA54E) absSign2Code
  wide : CodeIn M (lmLc (udL P) + 0x398) wideMul12x2Code
  neg : CodeIn M (lmLc (udL P) + 0x482) condNeg12Code
  mset : CodeIn M (lmLc (udL P) + 0x18A8) memsetCode
  stub : CodeIn M (lmLc (udL P) + 0x1910) memcpyStubCode
  body : CodeIn M (lmLc (udL P) + 0x1918) memcpyBodyCode
  bsub : CodeIn M (lcBsub (lmLc (udL P))) borrowingSubCode
  sel2 : CodeIn M (lmLc (udL P) + 0x592) uintSelect2Code
  sel12 : CodeIn M (lmLc (udL P) + 0xFFFFFF2A) uintSelect12Code
  zero : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  shr : CodeIn M (lmShr (udL P)) shr12Code
  lm : CodeIn M (lmShr (udL P) + 0x1EE) leadMut12Code
  tr : CodeIn M (lmShr (udL P) + 0x1FE) trailing12Code
  tur : CodeIn M (udL P + 0xFFFF9DCE) toUintResize2Code
  max : CodeIn M (BitVec.ofNat 32 u2MaxAddress) u2MaxData
  code : CodeIn M (P) updateDe12Code
  fi : CodeIn M (P + 0xB2) fromI64Code
  g_lmc : Sep G 0x380 (udL P) lincombShiftMod12Code.length
  g_lc : Sep G 0x380 (lmLc (udL P)) lincomb12Code.length
  g_abs : Sep G 0x380 (lmLc (udL P) + 0xFFFFA54E) absSign2Code.length
  g_wide : Sep G 0x380 (lmLc (udL P) + 0x398) wideMul12x2Code.length
  g_neg : Sep G 0x380 (lmLc (udL P) + 0x482) condNeg12Code.length
  g_mset : Sep G 0x380 (lmLc (udL P) + 0x18A8) memsetCode.length
  g_stub : Sep G 0x380 (lmLc (udL P) + 0x1910) memcpyStubCode.length
  g_body : Sep G 0x380 (lmLc (udL P) + 0x1918) memcpyBodyCode.length
  g_bsub : Sep G 0x380 (lcBsub (lmLc (udL P))) borrowingSubCode.length
  g_sel2 : Sep G 0x380 (lmLc (udL P) + 0x592) uintSelect2Code.length
  g_sel12 : Sep G 0x380 (lmLc (udL P) + 0xFFFFFF2A) uintSelect12Code.length
  g_zero : Sep G 0x380 (BitVec.ofNat 32 u2ZeroAddress) 8
  g_one : Sep G 0x380 (BitVec.ofNat 32 u2OneAddress) 8
  g_shr : Sep G 0x380 (lmShr (udL P)) shr12Code.length
  g_lm : Sep G 0x380 (lmShr (udL P) + 0x1EE) leadMut12Code.length
  g_tr : Sep G 0x380 (lmShr (udL P) + 0x1FE) trailing12Code.length
  g_tur : Sep G 0x380 (udL P + 0xFFFF9DCE) toUintResize2Code.length
  g_max : Sep G 0x380 (BitVec.ofNat 32 u2MaxAddress) 8
  g_code : Sep G 0x380 (P) updateDe12Code.length
  g_fi : Sep G 0x380 (P + 0xB2) fromI64Code.length
  o_lmc : Sep out 0x65 (udL P) lincombShiftMod12Code.length
  o_lc : Sep out 0x65 (lmLc (udL P)) lincomb12Code.length
  o_abs : Sep out 0x65 (lmLc (udL P) + 0xFFFFA54E) absSign2Code.length
  o_wide : Sep out 0x65 (lmLc (udL P) + 0x398) wideMul12x2Code.length
  o_neg : Sep out 0x65 (lmLc (udL P) + 0x482) condNeg12Code.length
  o_mset : Sep out 0x65 (lmLc (udL P) + 0x18A8) memsetCode.length
  o_stub : Sep out 0x65 (lmLc (udL P) + 0x1910) memcpyStubCode.length
  o_body : Sep out 0x65 (lmLc (udL P) + 0x1918) memcpyBodyCode.length
  o_bsub : Sep out 0x65 (lcBsub (lmLc (udL P))) borrowingSubCode.length
  o_sel2 : Sep out 0x65 (lmLc (udL P) + 0x592) uintSelect2Code.length
  o_sel12 : Sep out 0x65 (lmLc (udL P) + 0xFFFFFF2A) uintSelect12Code.length
  o_zero : Sep out 0x65 (BitVec.ofNat 32 u2ZeroAddress) 8
  o_one : Sep out 0x65 (BitVec.ofNat 32 u2OneAddress) 8
  o_shr : Sep out 0x65 (lmShr (udL P)) shr12Code.length
  o_lm : Sep out 0x65 (lmShr (udL P) + 0x1EE) leadMut12Code.length
  o_tr : Sep out 0x65 (lmShr (udL P) + 0x1FE) trailing12Code.length
  o_tur : Sep out 0x65 (udL P + 0xFFFF9DCE) toUintResize2Code.length
  o_max : Sep out 0x65 (BitVec.ofNat 32 u2MaxAddress) 8
  o_code : Sep out 0x65 (P) updateDe12Code.length
  o_fi : Sep out 0x65 (P + 0xB2) fromI64Code.length
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x380 ≤ 2 ^ 32
  hout : out.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hmp : mp.toNat % 4 = 0
  htp : tp.toNat % 4 = 0
  hwo : out.toNat + 0x65 < 2 ^ 32
  hwa : ap.toNat + 49 < 2 ^ 32
  hwb : bp.toNat + 49 < 2 ^ 32
  oG : Sep out 0x65 G 0x380
  aG : Sep ap 49 G 0x380
  bG : Sep bp 49 G 0x380
  mG : Sep mp 48 G 0x380
  tG : Sep tp 32 G 0x380
  aO : Sep ap 49 out 0x65
  bO : Sep bp 49 out 0x65
  mO : Sep mp 48 out 0x65
  tO : Sep tp 32 out 0x65

/-- The environment of a `lincomb_int_reduce_shift_mod` call from
`update_de`, in memory that agrees with the caller's outside its stack and
its result. -/
theorem ud12_lm {M M0 : Word → BitVec 8} {P G out ap bp mp tp res cp dp mip : Word}
    (env : UDEnv M0 P G out ap bp mp tp) (hM : ∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → M x = M0 x)
    (hres : res.toNat % 4 = 0) (hwr : res.toNat + 49 < 2 ^ 32) (rG : Sep res 49 G 0x330)
    (rC : Sep res 49 (udL P) lincombShiftMod12Code.length)
    (rB : Sep res 49 (lmLc (udL P) + 0x1918) memcpyBodyCode.length)
    (hcp : cp.toNat % 4 = 0) (hdp : dp.toNat % 4 = 0) (hmip : mip.toNat % 4 = 0)
    (cG : Sep cp 8 G 0x330) (dG : Sep dp 8 G 0x330) (iG : Sep mip 8 G 0x330) :
    LMEnv M (udL P) G res ap bp cp dp mp mip := by
  have cOf : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep G 0x380 b code.length →
      Sep out 0x65 b code.length → CodeIn M b code := fun hc h1 h2 i hi => by
    rw [hM _ (h1.subR (c := i) (l := 1) (by omega)) (h2.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have cOf8 : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → Sep G 0x380 b 8 →
      Sep out 0x65 b 8 → code.length = 8 → CodeIn M b code := fun hc h1 h2 hl i hi => by
    rw [hM _ (h1.subR (c := i) (l := 1) (by omega)) (h2.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have g : ∀ {b : Word} {k : Nat}, Sep G 0x380 b k → Sep G 0x330 b k := fun h => by
    have := h.sub (c := 0) (l := 0x330) (by decide); rwa [add_ofNat_zero] at this
  have gs : ∀ {b : Word} {k : Nat}, Sep b k G 0x380 → Sep b k G 0x330 := fun h => (g h.symm).symm
  have a49 : ∀ {b : Word}, Sep b 49 G 0x380 → Sep b 49 G 0x330 := gs
  exact {
    hP := even_at P env.hP 0xFFFFF8A6 (by decide)
    code := cOf env.lmc env.g_lmc env.o_lmc
    lc := cOf env.lc env.g_lc env.o_lc
    abs := cOf env.abs env.g_abs env.o_abs
    wide := cOf env.wide env.g_wide env.o_wide
    neg := cOf env.neg env.g_neg env.o_neg
    mset := cOf env.mset env.g_mset env.o_mset
    stub := cOf env.stub env.g_stub env.o_stub
    body := cOf env.body env.g_body env.o_body
    bsub := cOf env.bsub env.g_bsub env.o_bsub
    sel2 := cOf env.sel2 env.g_sel2 env.o_sel2
    sel12 := cOf env.sel12 env.g_sel12 env.o_sel12
    zero := cOf8 env.zero env.g_zero env.o_zero (by decide)
    one := cOf8 env.one env.g_one env.o_one (by decide)
    shr := cOf env.shr env.g_shr env.o_shr
    lm := cOf env.lm env.g_lm env.o_lm
    tr := cOf env.tr env.g_tr env.o_tr
    tur := cOf env.tur env.g_tur env.o_tur
    max := cOf8 env.max env.g_max env.o_max (by decide)
    hG := env.hG
    hGt := by have := env.hGt; omega
    hres := hres
    hap := env.hap
    hbp := env.hbp
    hcp := hcp
    hdp := hdp
    hmp := env.hmp
    hmip := hmip
    hwr := hwr
    hwa := env.hwa
    hwb := env.hwb
    sC := g env.g_lmc
    sL := g env.g_lc
    sA := g env.g_abs
    sW := g env.g_wide
    sN := g env.g_neg
    sM := g env.g_mset
    sU := g env.g_stub
    sB := g env.g_body
    sBs := g env.g_bsub
    s2 := g env.g_sel2
    s12 := g env.g_sel12
    sZ := g env.g_zero
    sO := g env.g_one
    sS := g env.g_shr
    sLm := g env.g_lm
    sTr := g env.g_tr
    sT := g env.g_tur
    sX := g env.g_max
    rG := rG
    aG := a49 env.aG
    bG := a49 env.bG
    cG := cG
    dG := dG
    mG := gs env.mG
    iG := iG
    rC := rC
    rB := rB }


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A call of `from_i64` at `off`: it stores `a1` and `a2` at `d` and
returns to `off + 8`. -/
theorem ud12_fi {M : Word → BitVec 8} {P F d : Word} {n : Machine} {off : Nat} {imm o : Word}
    (st : St M P n off (reg n)) (hc : CodeIn M P updateDe12Code) (hf : CodeIn M (P + 0xB2) fromI64Code)
    (hP : P.toNat % 2 = 0) (h1 : fetchRel updateDe12Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel updateDe12Code (off + 4) = some (.jalr ra ra o, 4)) (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xB2)
    (hoff : (off + 8) % 2 = 0) (hsp : reg n sp = F) (hF : F.toNat % 4 = 0) (hF16 : 16 ≤ F.toNat)
    (ha0 : reg n a0 = d) (hd : d.toNat % 4 = 0)
    (sFC : Sep (F + 0xFFFFFFF0) 16 (P + 0xB2) fromI64Code.length) (sDC : Sep d 8 (P + 0xB2) fromI64Code.length) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 8) (reg n') ∧ reg n' sp = F ∧
      (∀ q, q.val ∉ [1, 11, 12, 13, 14] → reg n' q = reg n q) ∧
      memLoad32 n'.mem d = reg n a1 ∧ memLoad32 n'.mem (d + 4) = reg n a2 ∧
      ∀ x, Sep (F + 0xFFFFFFF0) 16 x 1 → Sep d 8 x 1 → n'.mem x = M x := by
  obtain ⟨t1, c1, pc1, mem1, regs1⟩ := st.callRa hc h1 h2 hb (even_at P hP 0xB2 (by decide))
  have r1 := PEnv.reg1 regs1 st.zero
  obtain ⟨t2, c2, pc2, sp2, k2, lo2, hi2, fr2⟩ := fromI64_correct t1 (by rw [mem1]; exact hf) pc1
    (by rw [r1 _ (by decide), hsp]) (by rw [r1 _ (by decide), ha0]) rfl rfl (by rw [regs1]; simp [upd])
    (even_clear _ (even_at P hP (off + 8) hoff)) hF hF16 hd sFC sDC
  rw [mem1] at fr2
  refine ⟨t2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, sp2, fun q hq => ?_, ?_, ?_, fr2⟩
  · rw [k2 q (fun h => hq (by revert h; revert q; decide)), r1 q (fun e => hq (by rw [e]; decide))]
  · rw [lo2, r1 _ (by decide)]
  · rw [hi2, r1 _ (by decide)]

end C3.RV32
