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


theorem udPro_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base F : Word} {len : Nat}
    (hF : f sp + 0xFFFFFFB0 = F)
    (h : ∀ c : Nat, 0x2C ≤ c → c + 4 ≤ 0x50 → c % 4 = 0 →
      (F + BitVec.ofNat 32 c).toNat % 4 = 0 ∧ Sep (F + BitVec.ofNat 32 c) 4 base len)
    (ht : (f a6).toNat % 4 = 0) :
    BlockOk base len udPro (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, udPro, upd, ↓reduceIte, and_true, true_and, ev_add]
  rw [hF, ud_zadd, add_lit_zero]
  exact ⟨h 0x4C (by decide) (by decide) (by decide), h 0x48 (by decide) (by decide) (by decide), h 0x44 (by decide) (by decide) (by decide), h 0x40 (by decide) (by decide) (by decide), h 0x3C (by decide) (by decide) (by decide), h 0x38 (by decide) (by decide) (by decide), h 0x34 (by decide) (by decide) (by decide), h 0x30 (by decide) (by decide) (by decide), h 0x2C (by decide) (by decide) (by decide), ht, aligned_add ht (by decide)⟩


/-- The frame slot that holds callee-saved register `q`. -/
def udSlot (q : Fin 32) : Word := ((udPs.find? fun p => p.1 == q).map Prod.snd).getD 0

theorem udSlot_mem : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23] → (q, udSlot q) ∈ udPs := by decide

theorem ud_keep_split : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
    q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23] ∨ q.val ∈ [3, 4, 24, 25, 26, 27] := by decide

theorem ud_sg {σ A x x' y y' c c' d d' sa sa' sb sb' : Nat}
    (h : sgnVal σ A = sgnVal sa' x' * i64Val c' + sgnVal sb' y' * i64Val d')
    (e1 : sa' = sa) (e2 : x' = x) (e3 : c' = c) (e4 : sb' = sb) (e5 : y' = y) (e6 : d' = d) :
    sgnVal σ A = sgnVal sa x * i64Val c + sgnVal sb y * i64Val d := by
  subst e1 e2 e3 e4 e5 e6; exact h

theorem ud_lr {σ A mi mi' s M M' r1 r2 : Nat} (h1 : r1 = (lrsm σ A mi' s M').1) (h2 : r2 = (lrsm σ A mi' s M').2)
    (e1 : mi' = mi) (e2 : M' = M) : r1 = (lrsm σ A mi s M).1 ∧ r2 = (lrsm σ A mi s M).2 := by
  subst e1 e2; exact ⟨h1, h2⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `safegcd::update_de::<12>`**: from `d` and `e` (signed
12-limb values with sign bytes 0 or 1), the modulus at `mp`, `mi` in `a4`
and `a5`, the matrix at `tp`, and a shift from 1 to 63, it stores at `out`
and `out + 0x34` the results `lrsm` gives for the two rows' linear
combinations. It returns with `sp` and `s0` through `s11` restored, and
changes no memory outside its 0x380 bytes of stack and the result pair. -/
theorem updateDe12_correct (m : Machine) {P G out ap bp mp tp retAddr mlo mhi : Word} {s : Nat}
    (env : UDEnv m.mem P G out ap bp mp tp) (hpc : m.pc = P) (hsp : reg m sp = G + 0x380)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp) (ha3 : reg m a3 = mp)
    (ha4 : reg m a4 = mlo) (ha5 : reg m a5 = mhi) (ha6 : reg m a6 = tp) (ha7 : reg m 17 = BitVec.ofNat 32 s)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hsa : (m.mem (ap + 0x30)).toNat ≤ 1) (hsb : (m.mem (bp + 0x30)).toNat ≤ 1) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x380 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∃ σ A, σ ≤ 1 ∧
        sgnVal σ A = sgnVal (m.mem (ap + 0x30)).toNat (accV m.mem ap 12) * i64Val (accV m.mem tp 2) +
          sgnVal (m.mem (bp + 0x30)).toNat (accV m.mem bp 12) * i64Val (accV m.mem (tp + 8) 2) ∧
        (m'.mem (out + 0x30)).toNat = (lrsm σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV m.mem mp 12)).1 ∧
        accV m'.mem out 12 = (lrsm σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV m.mem mp 12)).2) ∧
      (∃ σ A, σ ≤ 1 ∧
        sgnVal σ A = sgnVal (m.mem (ap + 0x30)).toNat (accV m.mem ap 12) * i64Val (accV m.mem (tp + 0x10) 2) +
          sgnVal (m.mem (bp + 0x30)).toNat (accV m.mem bp 12) * i64Val (accV m.mem (tp + 0x18) 2) ∧
        (m'.mem (out + 0x34 + 0x30)).toNat =
          (lrsm σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV m.mem mp 12)).1 ∧
        accV m'.mem (out + 0x34) 12 = (lrsm σ A (mlo.toNat + 2 ^ 32 * mhi.toNat) s (accV m.mem mp 12)).2) ∧
      ∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x330 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have tG : ∀ c, c < 0x380 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show G.toNat + c < 2 ^ 32 by omega)]
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x330 + c) := fun c => by
    rw [← hF, show (0x330 : Word) = BitVec.ofNat 32 0x330 from rfl, add_ofNat_assoc]
  have eF : F = G + BitVec.ofNat 32 0x330 := hF.symm
  have hFn : F.toNat = G.toNat + 0x330 := by rw [eF, tG _ (by decide)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have aG : ∀ c, c % 4 = 0 → c < 0x380 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [tG c h2]; have := env.hG; omega
  have aF : ∀ c, c % 4 = 0 → 0x330 + c < 0x380 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [fG]; exact aG _ (by omega) h2
  have sub : ∀ {b : Word} {k : Nat} (c l : Nat), c + l ≤ 0x380 → Sep G 0x380 b k → Sep (G + BitVec.ofNat 32 c) l b k :=
    fun c l h hs => hs.sub h
  have sG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x380 → d + k ≤ 0x380 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 =>
    sep_offsets G h (by omega) (by omega)
  have sF : ∀ {b : Word} {k : Nat} (c l : Nat), 0x330 + c + l ≤ 0x380 → Sep G 0x380 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun c l h hs => by rw [fG]; exact sub _ l h hs
  have cOf : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → M' x = m.mem x) →
      ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x380 b code.length →
        Sep out 0x65 b code.length → CodeIn M' b code :=
    fun hM' _ _ hc h1 h2 i hi => by
      rw [hM' _ (h1.subR (c := i) (l := 1) (by omega)) (h2.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- the prologue
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have eSp : reg m sp + 0xFFFFFFB0 = F := by rw [hsp, ← hF, BitVec.add_assoc]; rfl
  obtain ⟨n1, c1, u1⟩ := St.block udPro s0 env.code udPro_end (udPro_ok eSp (fun c h1 h2 h3 =>
    ⟨aF c h3 (by omega), sF c 4 (by omega) env.g_code⟩) (by rw [ha6]; exact env.htp))
  obtain ⟨pm, psp, ps2, ps1, ps6, ps7, ps3, ps4, ps5, pa1, pa2, ps0, pa0, pk⟩ :=
    udPro_run (M := m.mem) (f := reg m) rfl
  rw [pm, eSp] at u1
  rw [eSp] at pa1 pa2 pa0
  obtain ⟨M1, hM1⟩ : ∃ M1, saveMem m.mem F (reg m) udPs = M1 := ⟨_, rfl⟩
  rw [hM1] at u1 pa1 pa2
  have g1 : ∀ q, reg n1 q = (runBlock udPro (m.mem, reg m)).2 q := u1.regs
  have udPs_range : ∀ p ∈ udPs, p.2.toNat % 4 = 0 ∧ 0x2C ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x50 := by decide
  have fr1 : ∀ x, Sep G 0x380 x 1 → M1 x = m.mem x := fun x hx => by
    rw [← hM1]
    exact saveMem_outside udPs fun p hp => by
      obtain ⟨h1, h2, h3⟩ := udPs_range p hp
      have e : F + p.2 = G + BitVec.ofNat 32 (0x330 + p.2.toNat) := by rw [← fG, ofNat_toNat_self]
      rw [e]; exact sub _ 4 (by omega) hx
  have tpS : ∀ k, k < 32 → Sep G 0x380 (tp + BitVec.ofNat 32 k) 1 := fun k hk => by
    have := env.tG.symm.subR (c := k) (l := 1) (by omega); exact this
  have hc1 := cOf (M' := M1) (fun x h1 _ => fr1 x h1) env.code env.g_code env.o_code
  have hf1 := cOf (M' := M1) (fun x h1 _ => fr1 x h1) env.fi env.g_fi env.o_fi
  have eS16 : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x320 := by rw [eF, BitVec.add_assoc]; rfl
  have sp1 : reg n1 sp = F := by rw [g1, psp, eSp]
  have s1v : reg n1 9 = tp := by rw [g1, ps1, ha6]
  -- `from_i64` of the matrix's first entry, to `F + 4`
  obtain ⟨n2, c2, u2, sp2, k2, lo2, hi2, fr2⟩ := ud12_fi (d := F + 4) u1.self hc1 hf1 env.hP ud12_at_2c ud12_at_30
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) sp1 hFa (by omega) (by rw [g1, pa0])
    (aF 4 rfl (by decide)) (by rw [eS16]; exact sub _ _ (by decide) env.g_fi) (sF 4 8 (by decide) env.g_fi)
  have fr2G : ∀ x, Sep G 0x380 x 1 → n2.mem x = m.mem x := fun x hx => by
    rw [fr2 x (by rw [eS16]; exact sub _ _ (by decide) hx) (sF 4 8 (by decide) hx), fr1 x hx]
  have fr2G' : ∀ b : Word, (∀ j, j < 4 → Sep G 0x380 (b + BitVec.ofNat 32 j) 1) → memLoad32 n2.mem b = memLoad32 m.mem b :=
    fun b hb => memLoad32_congr fun j hj => fr2G _ (hb j hj)
  have hc2 := cOf (M' := n2.mem) (fun x h1 _ => fr2G x h1) env.code env.g_code env.o_code
  have hf2 := cOf (M' := n2.mem) (fun x h1 _ => fr2G x h1) env.fi env.g_fi env.o_fi
  have tpL : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0x380 x 1 → M' x = m.mem x) → ∀ k, k + 4 ≤ 32 →
      memLoad32 M' (tp + BitVec.ofNat 32 k) = memLoad32 m.mem (tp + BitVec.ofNat 32 k) := fun hM' k hk =>
    memLoad32_congr fun j hj => hM' _ (by rw [add_ofNat_assoc]; exact tpS _ (by omega))
  obtain ⟨n3, c3, u3⟩ := St.block (udLd 8 0xC) u2 hc2 udB1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, udLd, upd, ↓reduceIte, and_true, true_and]
    rw [k2 9 (by decide), s1v]
    exact ⟨aligned_add env.htp (by decide), aligned_add env.htp (by decide)⟩)
  obtain ⟨l1e, l1a1, l1a2, l1a0, l1k⟩ := udLd_run (M := n2.mem) (f := reg n2) (o := 8) (d := 0xC) u2.zero
  rw [l1e] at u3
  have g3 : ∀ q, reg n3 q = (runBlock (udLd 8 0xC) (n2.mem, reg n2)).2 q := u3.regs
  obtain ⟨n4, c4, u4, sp4, k4, lo4, hi4, fr4⟩ := ud12_fi (d := F + 0xC) u3.self hc2 hf2 env.hP ud12_at_3a ud12_at_3e
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by rw [g3, l1k sp (by decide), sp2]) hFa (by omega)
    (by rw [g3, l1a0, sp2]) (aF 0xC rfl (by decide)) (by rw [eS16]; exact sub _ _ (by decide) env.g_fi)
    (sF 0xC 8 (by decide) env.g_fi)
  have fr4G : ∀ x, Sep G 0x380 x 1 → n4.mem x = m.mem x := fun x hx => by
    rw [fr4 x (by rw [eS16]; exact sub _ _ (by decide) hx) (sF 0xC 8 (by decide) hx), fr2G x hx]
  have hc4 := cOf (M' := n4.mem) (fun x h1 _ => fr4G x h1) env.code env.g_code env.o_code
  have K4 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n1 q :=
    fun q hq => by
      rw [k4 q (nmem_disj hq (by decide)), g3, l1k q (nmem_disj hq (by decide)), k2 q (nmem_disj hq (by decide))]
  have R1 : ∀ q : Fin 32, q.val ∈ [3, 4, 24, 25, 26, 27] → reg n1 q = reg m q := fun q hq => by
    rw [g1, pk q (nmem_disj hq (by decide))]
  obtain ⟨n5, c5, u5⟩ := St.block udB2 u4 hc4 udB2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, udB2, upd, ↓reduceIte, and_true, true_and]
    rw [sp4]
    exact ⟨⟨aF 0x24 rfl (by decide), sF 0x24 4 (by decide) env.g_code⟩, aF 0x28 rfl (by decide),
      sF 0x28 4 (by decide) env.g_code⟩)
  obtain ⟨b2e, b2a3, b2a4, b2a7, b2a0, b2a1, b2a2, b2a5, b2a6, b2k⟩ := udB2_run (M := n4.mem) (f := reg n4) u4.zero
  rw [b2e, sp4] at u5
  rw [sp4] at b2a3 b2a4 b2a7
  have g5 : ∀ q, reg n5 q = (runBlock udB2 (n4.mem, reg n4)).2 q := u5.regs
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 (memStore32 n4.mem (F + 0x24) (reg n4 23)) (F + 0x28) (reg n4 22) = M5 :=
    ⟨_, rfl⟩
  rw [hM5] at u5
  have fr5 : ∀ x, Sep (F + 0x24) 8 x 1 → M5 x = n4.mem x := fun x hx => by
    have h4 : Sep (F + 0x28) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0x24) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hM5, memStore32_get_sep h4, memStore32_get_sep h0]
  have fr5G : ∀ x, Sep G 0x380 x 1 → M5 x = m.mem x := fun x hx => by
    rw [fr5 x (sF 0x24 8 (by decide) hx), fr4G x hx]
  have hc5 := cOf (M' := M5) (fun x h1 _ => fr5G x h1) env.code env.g_code env.o_code
  have ehb : udL P = P + BitVec.ofNat 32 0x58 + 0x0 + 0xFFFFF84E := by
    show P + 0xFFFFF8A6 = _; rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨t6, ct6, pct6, memt6, regst6⟩ := u5.self.callRa hc5 ud12_at_58 ud12_at_5c (cb := udL P) ehb.symm
    (even_at P env.hP 0xFFFFF8A6 (by decide))
  have rt6 := PEnv.reg1 regst6 u5.self.zero
  have g330 : ∀ {c l : Nat}, 0x330 ≤ c → c + l ≤ 0x380 → Sep (G + BitVec.ofNat 32 c) l G 0x330 := fun {c l} h1 h2 => by
    have := sep_offsets G (c := c) (n := l) (d := 0) (k := 0x330) (.inr (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have oS : ∀ {b : Word} {k : Nat}, Sep out 0x65 b k → Sep out 49 b k := fun h => by
    have := h.sub (c := 0) (l := 49) (by decide); rwa [add_ofNat_zero] at this
  have LE := ud12_lm (M := t6.mem) (res := out) (cp := F + 4) (dp := F + 0xC) (mip := F + 0x24) env
    (fun x h1 h2 => by rw [memt6]; exact fr5G x h1) env.hout (by have := env.hwo; omega)
    (by have := env.oG.subR (c := 0) (l := 0x330) (by decide); rw [add_ofNat_zero] at this; exact oS this)
    (oS env.o_lmc) (oS env.o_body) (aF 4 rfl (by decide)) (aF 0xC rfl (by decide)) (aF 0x24 rfl (by decide))
    (by rw [show F + 4 = G + BitVec.ofNat 32 0x334 from fG 4]; exact g330 (by decide) (by decide))
    (by rw [show F + 0xC = G + BitVec.ofNat 32 0x33C from fG 0xC]; exact g330 (by decide) (by decide))
    (by rw [show F + 0x24 = G + BitVec.ofNat 32 0x354 from fG 0x24]; exact g330 (by decide) (by decide))
  have r5 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg t6 q = reg n1 q :=
    fun q hq => by
      rw [rt6 q (fun e => by rw [e] at hq; exact absurd hq (by decide)), g5, b2k q (nmem_disj hq (by decide)),
        K4 q hq]
  have apS : Sep G 0x380 (ap + 0x30) 1 := env.aG.symm.subR (c := 0x30) (l := 1) (by decide)
  have bpS : Sep G 0x380 (bp + 0x30) 1 := env.bG.symm.subR (c := 0x30) (l := 1) (by decide)
  obtain ⟨t7, σ1, A1, c7, pc7, sp7, k7, hσ1, val7, sgn7, res7, fr7⟩ := lincombShiftMod12_correct t6 LE pct6
    (by rw [rt6 _ (by decide), g5, b2k sp (by decide), sp4, hF])
    (by rw [rt6 _ (by decide), g5, b2a0, K4 8 (by decide), g1, ps0, ha0])
    (by rw [rt6 _ (by decide), g5, b2a1, K4 21 (by decide), g1, ps5, ha1])
    (by rw [rt6 _ (by decide), g5, b2a2, K4 20 (by decide), g1, ps4, ha2])
    (by rw [rt6 _ (by decide), g5, b2a3]) (by rw [rt6 _ (by decide), g5, b2a4])
    (by rw [rt6 _ (by decide), g5, b2a5, K4 18 (by decide), g1, ps2, ha7])
    (by rw [rt6 _ (by decide), g5, b2a6, K4 19 (by decide), g1, ps3, ha3])
    (by rw [rt6 _ (by decide), g5, b2a7]) (by rw [regst6]; simp [upd])
    (even_clear _ (even_at P env.hP (0x58 + 8) (by decide))) hs1 hs2
    (by rw [memt6, fr5G _ apS]; exact hsa) (by rw [memt6, fr5G _ bpS]; exact hsb)
  rw [memt6] at fr7 val7 sgn7 res7
  have gG : ∀ {x : Word}, Sep G 0x380 x 1 → Sep G 0x330 x 1 := fun hx => by
    have := hx.sub (c := 0) (l := 0x330) (by decide); rwa [add_ofNat_zero] at this
  have hT7 : ∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → t7.mem x = m.mem x := fun x h1 h2 => by
    rw [fr7 x (gG h1) (oS h2), fr5G x h1]
  have st7 : St t7.mem P t7 0x60 (reg t7) := ⟨pc7, rfl, fun _ => rfl⟩
  have hc7 := cOf hT7 env.code env.g_code env.o_code
  have hf7 := cOf hT7 env.fi env.g_fi env.o_fi
  have K7 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg t7 q = reg n1 q :=
    fun q hq => by rw [k7 q hq, r5 q hq]
  have sp7F : reg t7 sp = F := by rw [sp7, hF]
  obtain ⟨n8, c8, u8⟩ := St.block (udLd 0x10 0x14) st7 hc7 udB3_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, udLd, upd, ↓reduceIte, and_true, true_and]
    rw [K7 9 (by decide), s1v]
    exact ⟨aligned_add env.htp (by decide), aligned_add env.htp (by decide)⟩)
  obtain ⟨l3e, l3a1, l3a2, l3a0, l3k⟩ := udLd_run (M := t7.mem) (f := reg t7) (o := 0x10) (d := 0x14) st7.zero
  rw [l3e] at u8
  have g8 : ∀ q, reg n8 q = (runBlock (udLd 0x10 0x14) (t7.mem, reg t7)).2 q := u8.regs
  obtain ⟨n9, c9, u9, sp9, k9, lo9, hi9, fr9⟩ := ud12_fi (d := F + 0x14) u8.self hc7 hf7 env.hP ud12_at_66 ud12_at_6a
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by rw [g8, l3k sp (by decide), sp7F]) hFa (by omega)
    (by rw [g8, l3a0, sp7F]) (aF 0x14 rfl (by decide)) (by rw [eS16]; exact sub _ _ (by decide) env.g_fi)
    (sF 0x14 8 (by decide) env.g_fi)
  have hT9 : ∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → n9.mem x = m.mem x := fun x h1 h2 => by
    rw [fr9 x (by rw [eS16]; exact sub _ _ (by decide) h1) (sF 0x14 8 (by decide) h1), hT7 x h1 h2]
  have hc9 := cOf hT9 env.code env.g_code env.o_code
  have hf9 := cOf hT9 env.fi env.g_fi env.o_fi
  obtain ⟨n10, c10, u10⟩ := St.block (udLd 0x18 0x1C) u9 hc9 udB4_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, udLd, upd, ↓reduceIte, and_true, true_and]
    rw [k9 9 (by decide), g8, l3k 9 (by decide), K7 9 (by decide), s1v]
    exact ⟨aligned_add env.htp (by decide), aligned_add env.htp (by decide)⟩)
  obtain ⟨l4e, l4a1, l4a2, l4a0, l4k⟩ := udLd_run (M := n9.mem) (f := reg n9) (o := 0x18) (d := 0x1C) u9.zero
  rw [l4e] at u10
  have g10 : ∀ q, reg n10 q = (runBlock (udLd 0x18 0x1C) (n9.mem, reg n9)).2 q := u10.regs
  obtain ⟨n11, c11, u11, sp11, k11, lo11, hi11, fr11⟩ := ud12_fi (d := F + 0x1C) u10.self hc9 hf9 env.hP ud12_at_74
    ud12_at_78 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (by rw [g10, l4k sp (by decide), sp9])
    hFa (by omega) (by rw [g10, l4a0, sp9]) (aF 0x1C rfl (by decide)) (by rw [eS16]; exact sub _ _ (by decide) env.g_fi)
    (sF 0x1C 8 (by decide) env.g_fi)
  have hT11 : ∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → n11.mem x = m.mem x := fun x h1 h2 => by
    rw [fr11 x (by rw [eS16]; exact sub _ _ (by decide) h1) (sF 0x1C 8 (by decide) h1), hT9 x h1 h2]
  have hc11 := cOf hT11 env.code env.g_code env.o_code
  have K11 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n11 q = reg n1 q :=
    fun q hq => by
      rw [k11 q (nmem_disj hq (by decide)), g10, l4k q (nmem_disj hq (by decide)), k9 q (nmem_disj hq (by decide)),
        g8, l3k q (nmem_disj hq (by decide)), K7 q hq]
  obtain ⟨n12, c12, u12⟩ := St.block udB5 u11 hc11 udB5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, udB5, upd, ↓reduceIte, and_true, true_and]
    rw [sp11]
    exact ⟨⟨aF 0x24 rfl (by decide), sF 0x24 4 (by decide) env.g_code⟩, aF 0x28 rfl (by decide),
      sF 0x28 4 (by decide) env.g_code⟩)
  obtain ⟨b5e, b5a0, b5a3, b5a4, b5a7, b5a1, b5a2, b5a5, b5a6, b5k⟩ := udB5_run (M := n11.mem) (f := reg n11) u11.zero
  rw [b5e, sp11] at u12
  rw [sp11] at b5a3 b5a4 b5a7
  have g12 : ∀ q, reg n12 q = (runBlock udB5 (n11.mem, reg n11)).2 q := u12.regs
  obtain ⟨M12, hM12⟩ : ∃ M12, memStore32 (memStore32 n11.mem (F + 0x24) (reg n11 23)) (F + 0x28) (reg n11 22) = M12 :=
    ⟨_, rfl⟩
  rw [hM12] at u12
  have fr12 : ∀ x, Sep (F + 0x24) 8 x 1 → M12 x = n11.mem x := fun x hx => by
    have h4 : Sep (F + 0x28) 4 x 1 := by
      have := hx.sub (c := 4) (l := 4) (by decide); rw [BitVec.add_assoc] at this; exact this
    have h0 : Sep (F + 0x24) 4 x 1 := by
      have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    rw [← hM12, memStore32_get_sep h4, memStore32_get_sep h0]
  have hT12 : ∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → M12 x = m.mem x := fun x h1 h2 => by
    rw [fr12 x (sF 0x24 8 (by decide) h1), hT11 x h1 h2]
  have hc12 := cOf hT12 env.code env.g_code env.o_code
  have ehb2 : udL P = P + BitVec.ofNat 32 0x94 + 0x0 + 0xFFFFF812 := by
    show P + 0xFFFFF8A6 = _; rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨t13, ct13, pct13, memt13, regst13⟩ := u12.self.callRa hc12 ud12_at_94 ud12_at_98 (cb := udL P) ehb2.symm
    (even_at P env.hP 0xFFFFF8A6 (by decide))
  have rt13 := PEnv.reg1 regst13 u12.self.zero
  have o34 : ∀ {b : Word} {k : Nat}, Sep out 0x65 b k → Sep (out + 0x34) 49 b k := fun h => h.sub (c := 0x34) (l := 49) (by decide)
  have LE2 := ud12_lm (M := t13.mem) (res := out + 0x34) (cp := F + 0x14) (dp := F + 0x1C) (mip := F + 0x24) env
    (fun x h1 h2 => by rw [memt13]; exact hT12 x h1 h2) (aligned_add env.hout (by decide))
    (by have := env.hwo
        rw [BitVec.toNat_add, show (0x34 : Word).toNat = 0x34 from rfl, Nat.mod_eq_of_lt (by omega)]; omega)
    (by have := env.oG.subR (c := 0) (l := 0x330) (by decide); rw [add_ofNat_zero] at this; exact o34 this)
    (o34 env.o_lmc) (o34 env.o_body) (aF 0x14 rfl (by decide)) (aF 0x1C rfl (by decide)) (aF 0x24 rfl (by decide))
    (by rw [show F + 0x14 = G + BitVec.ofNat 32 0x344 from fG 0x14]; exact g330 (by decide) (by decide))
    (by rw [show F + 0x1C = G + BitVec.ofNat 32 0x34C from fG 0x1C]; exact g330 (by decide) (by decide))
    (by rw [show F + 0x24 = G + BitVec.ofNat 32 0x354 from fG 0x24]; exact g330 (by decide) (by decide))
  have r12 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg t13 q = reg n1 q :=
    fun q hq => by
      rw [rt13 q (fun e => by rw [e] at hq; exact absurd hq (by decide)), g12, b5k q (nmem_disj hq (by decide)),
        K11 q hq]
  have apO : Sep out 0x65 (ap + 0x30) 1 := env.aO.symm.subR (c := 0x30) (l := 1) (by decide)
  have bpO : Sep out 0x65 (bp + 0x30) 1 := env.bO.symm.subR (c := 0x30) (l := 1) (by decide)
  obtain ⟨t14, σ2, A2, c14, pc14, sp14, k14, hσ2, val14, sgn14, res14, fr14⟩ := lincombShiftMod12_correct t13 LE2 pct13
    (by rw [rt13 _ (by decide), g12, b5k sp (by decide), sp11, hF])
    (by rw [rt13 _ (by decide), g12, b5a0, K11 8 (by decide), g1, ps0, ha0])
    (by rw [rt13 _ (by decide), g12, b5a1, K11 21 (by decide), g1, ps5, ha1])
    (by rw [rt13 _ (by decide), g12, b5a2, K11 20 (by decide), g1, ps4, ha2])
    (by rw [rt13 _ (by decide), g12, b5a3]) (by rw [rt13 _ (by decide), g12, b5a4])
    (by rw [rt13 _ (by decide), g12, b5a5, K11 18 (by decide), g1, ps2, ha7])
    (by rw [rt13 _ (by decide), g12, b5a6, K11 19 (by decide), g1, ps3, ha3])
    (by rw [rt13 _ (by decide), g12, b5a7]) (by rw [regst13]; simp [upd])
    (even_clear _ (even_at P env.hP (0x94 + 8) (by decide))) hs1 hs2
    (by rw [memt13, hT12 _ apS apO]; exact hsa) (by rw [memt13, hT12 _ bpS bpO]; exact hsb)
  rw [memt13] at fr14 val14 sgn14 res14
  -- the epilogue
  have hT14 : ∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → t14.mem x = m.mem x := fun x h1 h2 => by
    rw [fr14 x (gG h1) (o34 h2), hT12 x h1 h2]
  have hc14 := cOf hT14 env.code env.g_code env.o_code
  have st14 : St t14.mem P t14 0x9C (reg t14) := ⟨pc14, rfl, fun _ => rfl⟩
  have sp14F : reg t14 sp = F := by rw [sp14, hF]
  obtain ⟨n15, c15, u15⟩ := St.block (restoreBlock udPs) st14 hc14 udEpi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, restoreBlock, udPs, List.map, upd, ↓reduceIte, and_true,
      true_and]
    rw [sp14F]
    exact ⟨aF 0x4C rfl (by decide), aF 0x48 rfl (by decide), aF 0x44 rfl (by decide), aF 0x40 rfl (by decide),
      aF 0x3C rfl (by decide), aF 0x38 rfl (by decide), aF 0x34 rfl (by decide), aF 0x30 rfl (by decide),
      aF 0x2C rfl (by decide)⟩)
  obtain ⟨er, em, ek⟩ := udEpi_run (M := t14.mem) (f := reg t14) st14.zero
  rw [em] at u15
  have g15 : ∀ q, reg n15 q = (runBlock (restoreBlock udPs) (t14.mem, reg t14)).2 q := u15.regs
  obtain ⟨n16, d16, u16⟩ := u15.self.aluImm hc14 ud12_at_ae (off' := 0xB0) (by decide)
  -- the saved registers survive
  have slot : ∀ c, 0x2C ≤ c → c + 4 ≤ 0x50 → memLoad32 t14.mem (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, fG]
      have gd : ∀ {a l : Nat}, a + l ≤ 0x330 + (c + j) → Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 (0x330 + (c + j))) 1 :=
        fun h => sG (.inl h) (by omega) (by omega)
      have o1 : Sep out 0x65 (G + BitVec.ofNat 32 (0x330 + (c + j))) 1 := env.oG.subR (c := 0x330 + (c + j)) (l := 1) (by omega)
      have g1' : Sep G 0x330 (G + BitVec.ofNat 32 (0x330 + (c + j))) 1 := by
        have := gd (a := 0) (l := 0x330) (by omega); rwa [add_ofNat_zero] at this
      rw [fr14 _ g1' (o34 o1), fr12 _ (by rw [show F + 0x24 = G + BitVec.ofNat 32 0x354 from fG 0x24]; exact gd (by omega)),
        fr11 _ (by rw [eS16]; exact gd (by omega)) (by rw [show F + 0x1C = G + BitVec.ofNat 32 0x34C from fG 0x1C]; exact gd (by omega)),
        fr9 _ (by rw [eS16]; exact gd (by omega)) (by rw [show F + 0x14 = G + BitVec.ofNat 32 0x344 from fG 0x14]; exact gd (by omega)),
        fr7 _ g1' (oS o1), fr5 _ (by rw [show F + 0x24 = G + BitVec.ofNat 32 0x354 from fG 0x24]; exact gd (by omega)),
        fr4 _ (by rw [eS16]; exact gd (by omega)) (by rw [show F + 0xC = G + BitVec.ofNat 32 0x33C from fG 0xC]; exact gd (by omega)),
        fr2 _ (by rw [eS16]; exact gd (by omega)) (by rw [show F + 4 = G + BitVec.ofNat 32 0x334 from fG 4]; exact gd (by omega))]
  have hslv : ∀ r o, (r, o) ∈ udPs → memLoad32 M1 (F + o) = reg m r := fun r o h => by
    rw [← hM1]
    simp only [udPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem, udPs]
      simp (disch := decide) only [ls_lit, ls_same]
  have slotv : ∀ r o, (r, o) ∈ udPs → memLoad32 t14.mem (reg t14 sp + o) = reg m r := fun r o h => by
    obtain ⟨_, h2, h3⟩ := udPs_range (r, o) h
    have := slot o.toNat h2 h3
    rw [ofNat_toNat_self] at this
    rw [sp14F, this, hslv r o h]
  have rRa : reg n16 ra = retAddr := by
    rw [u16.oldReg u15.self.zero ra (by decide), g15, er ra 0x4C (by decide), slotv ra 0x4C (by decide), hra]
  obtain ⟨n17, d17, pc17, mem17, regs17⟩ := u16.self.jalr hc14 ud12_at_b0
  have g16 : ∀ q, q ≠ sp → reg n16 q = reg n15 q := fun q hq => u16.oldReg u15.self.zero q hq
  refine ⟨n17, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (ct6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (ct13.trans (c14.trans (c15.trans (.cons d16 (.single d17)))))))))))))))),
    by rw [pc17, rRa, add_lit_zero]; exact hret, ?_, ?_, ?_, ?_, fun x h1 h2 => by rw [mem17]; exact hT14 x h1 h2⟩
  · rw [regs17, u16.newReg (by decide)]
    show reg n15 sp + 0x50 = _
    rw [g15, ek sp (by decide), sp14F, eF, BitVec.add_assoc]; rfl
  · intro q hq
    rw [regs17, g16 q (fun e => by rw [e] at hq; exact absurd hq (by decide)), g15]
    rcases ud_keep_split q hq with h | h
    · rw [er q (udSlot q) (udSlot_mem q h), slotv q (udSlot q) (udSlot_mem q h)]
    · rw [ek q (nmem_disj h (by decide)), k14 q (mem_sub h (by decide)), r12 q (mem_sub h (by decide)),
        R1 q h]
  · -- the first row: `d` at `out`
    have outS : ∀ k, k < 0x31 → Sep G 0x380 (out + BitVec.ofNat 32 k) 1 := fun k hk =>
      env.oG.symm.subR (c := k) (l := 1) (by omega)
    have O1 : ∀ k, k < 0x31 → n17.mem (out + BitVec.ofNat 32 k) = t7.mem (out + BitVec.ofNat 32 k) := fun k hk => by
      have h34 : Sep (out + 0x34) 49 (out + BitVec.ofNat 32 k) 1 := by
        have := sep_offsets out (c := 0x34) (n := 49) (d := k) (k := 1) (.inr (by omega)) (by omega) (by omega)
        exact this
      rw [mem17, fr14 _ (gG (outS k hk)) h34, fr12 _ (sF 0x24 8 (by decide) (outS k hk)),
        fr11 _ (by rw [eS16]; exact sub _ _ (by decide) (outS k hk)) (sF 0x1C 8 (by decide) (outS k hk)),
        fr9 _ (by rw [eS16]; exact sub _ _ (by decide) (outS k hk)) (sF 0x14 8 (by decide) (outS k hk))]
    have apV : accV M5 ap 12 = accV m.mem ap 12 := accV_congr 12 fun i hi => memLoad32_congr fun j hj => fr5G _ (by
      have := env.aG.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
    have bpV : accV M5 bp 12 = accV m.mem bp 12 := accV_congr 12 fun i hi => memLoad32_congr fun j hj => fr5G _ (by
      have := env.bG.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
    have mpV : accV M5 mp 12 = accV m.mem mp 12 := accV_congr 12 fun i hi => memLoad32_congr fun j hj => fr5G _ (by
      have := env.mG.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
    have w5 : ∀ c, c + 4 ≤ 0x24 → memLoad32 M5 (F + BitVec.ofNat 32 c) = memLoad32 n4.mem (F + BitVec.ofNat 32 c) :=
      fun c hc => memLoad32_congr fun j hj => fr5 _ (by
        rw [add_ofNat_assoc, fG, show F + 0x24 = G + BitVec.ofNat 32 0x354 from fG 0x24]
        exact sG (.inr (by omega)) (by decide) (by omega))
    have cV : accV M5 (F + 4) 2 = accV m.mem tp 2 := by
      rw [acc2, acc2, show F + 4 + 4 = F + BitVec.ofNat 32 8 by rw [BitVec.add_assoc]; rfl,
        show F + 4 = F + BitVec.ofNat 32 4 from rfl, w5 4 (by decide), w5 8 (by decide)]
      have e4 : memLoad32 n4.mem (F + BitVec.ofNat 32 4) = memLoad32 n2.mem (F + 4) :=
        memLoad32_congr fun j hj => fr4 _ (by rw [add_ofNat_assoc, fG, eS16]; exact sG (.inl (by omega)) (by decide) (by omega))
          (by rw [add_ofNat_assoc, fG, show F + 0xC = G + BitVec.ofNat 32 0x33C from fG 0xC]
              exact sG (.inr (by omega)) (by decide) (by omega))
      have e8 : memLoad32 n4.mem (F + BitVec.ofNat 32 8) = memLoad32 n2.mem (F + 4 + 4) := by
        rw [show F + 4 + 4 = F + BitVec.ofNat 32 8 by rw [BitVec.add_assoc]; rfl]
        exact memLoad32_congr fun j hj => fr4 _ (by rw [add_ofNat_assoc, fG, eS16]; exact sG (.inl (by omega)) (by decide) (by omega))
          (by rw [add_ofNat_assoc, fG, show F + 0xC = G + BitVec.ofNat 32 0x33C from fG 0xC]
              exact sG (.inr (by omega)) (by decide) (by omega))
      rw [e4, e8, lo2, hi2, g1, pa1, g1, pa2, ha6]
      have t0 := tpL fr1 0 (by decide); rw [add_ofNat_zero] at t0
      rw [t0, show tp + 4 = tp + BitVec.ofNat 32 4 from rfl, tpL fr1 4 (by decide)]
    have dV : accV M5 (F + 0xC) 2 = accV m.mem (tp + 8) 2 := by
      rw [acc2, acc2, show F + 0xC + 4 = F + BitVec.ofNat 32 0x10 by rw [BitVec.add_assoc]; rfl,
        show F + 0xC = F + BitVec.ofNat 32 0xC from rfl, w5 0xC (by decide), w5 0x10 (by decide)]
      rw [show F + BitVec.ofNat 32 0x10 = F + 0xC + 4 by rw [BitVec.add_assoc]; rfl]
      rw [show F + BitVec.ofNat 32 0xC = F + 0xC from rfl, lo4, hi4, g3, l1a1, g3, l1a2, k2 9 (by decide), s1v,
        show tp + 8 = tp + BitVec.ofNat 32 8 from rfl, show tp + (8 + 4) = tp + BitVec.ofNat 32 12 from rfl,
        tpL fr2G 8 (by decide), tpL fr2G 12 (by decide), BitVec.add_assoc]
      rfl
    have miV : accV M5 (F + 0x24) 2 = mlo.toNat + 2 ^ 32 * mhi.toNat := by
      rw [acc2, ← hM5, show F + 0x24 + 4 = F + 0x28 by rw [BitVec.add_assoc]; rfl]
      have hs : Sep (F + 0x28) 4 (F + 0x24) 4 :=
        sep_offsets F (c := 0x28) (n := 4) (d := 0x24) (k := 4) (.inr (by decide)) (by decide) (by decide)
      rw [memLoad32_store32_sep hs, memLoad32_store32_same, memLoad32_store32_same, K4 23 (by decide),
        K4 22 (by decide), g1, ps7, g1, ps6, ha4, ha5]
    refine ⟨σ1, A1, hσ1, ud_sg val7 (by rw [fr5G _ apS]) apV cV (by rw [fr5G _ bpS]) bpV dV, ?_, ?_⟩
    · obtain ⟨L1, -⟩ := ud_lr sgn7 res7 miV mpV
      rw [show out + 0x30 = out + BitVec.ofNat 32 0x30 from rfl, O1 0x30 (by decide)]; exact L1
    · obtain ⟨-, L2⟩ := ud_lr sgn7 res7 miV mpV
      have : accV n17.mem out 12 = accV t7.mem out 12 :=
        accV_congr 12 fun i hi => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact O1 _ (by omega)
      rw [this]; exact L2
  · -- the second row: `e` at `out + 0x34`
    have tpL2 : ∀ {M' : Word → BitVec 8}, (∀ x, Sep G 0x380 x 1 → Sep out 0x65 x 1 → M' x = m.mem x) → ∀ k, k + 4 ≤ 32 →
        memLoad32 M' (tp + BitVec.ofNat 32 k) = memLoad32 m.mem (tp + BitVec.ofNat 32 k) := fun hM' k hk =>
      memLoad32_congr fun j hj => hM' _ (by rw [add_ofNat_assoc]; exact tpS _ (by omega))
        (by rw [add_ofNat_assoc]; exact env.tO.symm.subR (c := k + j) (l := 1) (by omega))
    have aV : ∀ {b : Word}, Sep b 49 G 0x380 → Sep b 49 out 0x65 → accV M12 b 12 = accV m.mem b 12 := fun h1 h2 =>
      accV_congr 12 fun i hi => memLoad32_congr fun j hj => hT12 _ (by
          have := h1.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
        (by have := h2.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
    have mpV2 : accV M12 mp 12 = accV m.mem mp 12 := accV_congr 12 fun i hi => memLoad32_congr fun j hj => hT12 _ (by
        have := env.mG.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
      (by have := env.mO.symm.subR (c := 4 * i + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
    have w12 : ∀ c, c + 4 ≤ 0x24 → memLoad32 M12 (F + BitVec.ofNat 32 c) = memLoad32 n11.mem (F + BitVec.ofNat 32 c) :=
      fun c hc => memLoad32_congr fun j hj => fr12 _ (by
        rw [add_ofNat_assoc, fG, show F + 0x24 = G + BitVec.ofNat 32 0x354 from fG 0x24]
        exact sG (.inr (by omega)) (by decide) (by omega))
    have w11 : ∀ c, 0x14 ≤ c → c + 4 ≤ 0x1C → memLoad32 n11.mem (F + BitVec.ofNat 32 c) = memLoad32 n9.mem (F + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => fr11 _ (by rw [add_ofNat_assoc, fG, eS16]; exact sG (.inl (by omega)) (by decide) (by omega))
        (by rw [add_ofNat_assoc, fG, show F + 0x1C = G + BitVec.ofNat 32 0x34C from fG 0x1C]
            exact sG (.inr (by omega)) (by decide) (by omega))
    have cV2 : accV M12 (F + 0x14) 2 = accV m.mem (tp + 0x10) 2 := by
      rw [acc2, acc2, show F + 0x14 + 4 = F + BitVec.ofNat 32 0x18 by rw [BitVec.add_assoc]; rfl,
        show F + 0x14 = F + BitVec.ofNat 32 0x14 from rfl, w12 0x14 (by decide), w12 0x18 (by decide),
        w11 0x14 (by decide) (by decide), w11 0x18 (by decide) (by decide)]
      rw [show F + BitVec.ofNat 32 0x18 = F + 0x14 + 4 by rw [BitVec.add_assoc]; rfl]
      rw [show F + BitVec.ofNat 32 0x14 = F + 0x14 from rfl, lo9, hi9, g8, l3a1, g8, l3a2, K7 9 (by decide), s1v,
        show tp + 0x10 = tp + BitVec.ofNat 32 0x10 from rfl, show tp + (0x10 + 4) = tp + BitVec.ofNat 32 0x14 from rfl,
        tpL2 hT7 0x10 (by decide), tpL2 hT7 0x14 (by decide), BitVec.add_assoc]
      rfl
    have dV2 : accV M12 (F + 0x1C) 2 = accV m.mem (tp + 0x18) 2 := by
      rw [acc2, acc2, show F + 0x1C + 4 = F + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl,
        show F + 0x1C = F + BitVec.ofNat 32 0x1C from rfl, w12 0x1C (by decide), w12 0x20 (by decide)]
      rw [show F + BitVec.ofNat 32 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]
      rw [show F + BitVec.ofNat 32 0x1C = F + 0x1C from rfl, lo11, hi11, g10, l4a1, g10, l4a2, k9 9 (by decide), g8,
        l3k 9 (by decide), K7 9 (by decide), s1v,
        show tp + 0x18 = tp + BitVec.ofNat 32 0x18 from rfl, show tp + (0x18 + 4) = tp + BitVec.ofNat 32 0x1C from rfl,
        tpL2 hT9 0x18 (by decide), tpL2 hT9 0x1C (by decide), BitVec.add_assoc]
      rfl
    have miV2 : accV M12 (F + 0x24) 2 = mlo.toNat + 2 ^ 32 * mhi.toNat := by
      rw [acc2, ← hM12, show F + 0x24 + 4 = F + 0x28 by rw [BitVec.add_assoc]; rfl]
      have hs : Sep (F + 0x28) 4 (F + 0x24) 4 :=
        sep_offsets F (c := 0x28) (n := 4) (d := 0x24) (k := 4) (.inr (by decide)) (by decide) (by decide)
      rw [memLoad32_store32_sep hs, memLoad32_store32_same, memLoad32_store32_same, K11 23 (by decide),
        K11 22 (by decide), g1, ps7, g1, ps6, ha4, ha5]
    obtain ⟨L1, L2⟩ := ud_lr sgn14 res14 miV2 mpV2
    refine ⟨σ2, A2, hσ2, ud_sg val14 (by rw [hT12 _ apS apO]) (aV env.aG env.aO) cV2 (by rw [hT12 _ bpS bpO])
      (aV env.bG env.bO) dV2, by rw [mem17]; exact L1, by rw [mem17]; exact L2⟩

end C3.RV32
