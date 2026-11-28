import C3BootProofs.Proofs.FeCall

/-!
# `FieldElement2625::conditional_assign`, as compiled

`<FieldElement2625 as ConditionallySelectable>::conditional_assign` replaces
each limb of `self` with `other`'s when `choice` is 1, through the mask
`-choice`: each limb becomes `self ^ ((self ^ other) & mask)`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fca_at_0 : fetchRel feCondAssignCode 0x0 = some (.load .lw a6 a1 0x0, 4) := by decide
theorem fca_at_4 : fetchRel feCondAssignCode 0x4 = some (.load .lw (5 : Fin 32) a0 0x0, 4) := by decide
theorem fca_at_8 : fetchRel feCondAssignCode 0x8 = some (.load .lw (28 : Fin 32) a0 0x4, 4) := by decide
theorem fca_at_c : fetchRel feCondAssignCode 0xC = some (.load .lw (17 : Fin 32) a1 0x4, 4) := by decide
theorem fca_at_10 : fetchRel feCondAssignCode 0x10 = some (.alu .sub a2 x0 a2, 4) := by decide
theorem fca_at_14 : fetchRel feCondAssignCode 0x14 = some (.load .lw (29 : Fin 32) a0 0x8, 4) := by decide
theorem fca_at_18 : fetchRel feCondAssignCode 0x18 = some (.load .lw a4 a0 0xC, 2) := by decide
theorem fca_at_1a : fetchRel feCondAssignCode 0x1A = some (.load .lw (6 : Fin 32) a1 0x8, 4) := by decide
theorem fca_at_1e : fetchRel feCondAssignCode 0x1E = some (.load .lw (7 : Fin 32) a1 0xC, 4) := by decide
theorem fca_at_22 : fetchRel feCondAssignCode 0x22 = some (.alu .xor a5 a6 (5 : Fin 32), 4) := by decide
theorem fca_at_26 : fetchRel feCondAssignCode 0x26 = some (.alu .xor a3 (17 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fca_at_2a : fetchRel feCondAssignCode 0x2A = some (.alu .and a5 a5 a2, 2) := by decide
theorem fca_at_2c : fetchRel feCondAssignCode 0x2C = some (.alu .and a3 a3 a2, 2) := by decide
theorem fca_at_2e : fetchRel feCondAssignCode 0x2E = some (.alu .xor (17 : Fin 32) a5 (5 : Fin 32), 4) := by decide
theorem fca_at_32 : fetchRel feCondAssignCode 0x32 = some (.alu .xor a6 a3 (28 : Fin 32), 4) := by decide
theorem fca_at_36 : fetchRel feCondAssignCode 0x36 = some (.alu .xor a3 (6 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fca_at_3a : fetchRel feCondAssignCode 0x3A = some (.alu .xor a5 (7 : Fin 32) a4, 4) := by decide
theorem fca_at_3e : fetchRel feCondAssignCode 0x3E = some (.alu .and a3 a3 a2, 2) := by decide
theorem fca_at_40 : fetchRel feCondAssignCode 0x40 = some (.alu .and a5 a5 a2, 2) := by decide
theorem fca_at_42 : fetchRel feCondAssignCode 0x42 = some (.alu .xor (5 : Fin 32) a3 (29 : Fin 32), 4) := by decide
theorem fca_at_46 : fetchRel feCondAssignCode 0x46 = some (.alu .xor a4 a4 a5, 2) := by decide
theorem fca_at_48 : fetchRel feCondAssignCode 0x48 = some (.load .lw (28 : Fin 32) a0 0x10, 4) := by decide
theorem fca_at_4c : fetchRel feCondAssignCode 0x4C = some (.load .lw (29 : Fin 32) a0 0x14, 4) := by decide
theorem fca_at_50 : fetchRel feCondAssignCode 0x50 = some (.load .lw (6 : Fin 32) a1 0x10, 4) := by decide
theorem fca_at_54 : fetchRel feCondAssignCode 0x54 = some (.load .lw (7 : Fin 32) a1 0x14, 4) := by decide
theorem fca_at_58 : fetchRel feCondAssignCode 0x58 = some (.store .sw a0 (17 : Fin 32) 0x0, 4) := by decide
theorem fca_at_5c : fetchRel feCondAssignCode 0x5C = some (.store .sw a0 a6 0x4, 4) := by decide
theorem fca_at_60 : fetchRel feCondAssignCode 0x60 = some (.store .sw a0 (5 : Fin 32) 0x8, 4) := by decide
theorem fca_at_64 : fetchRel feCondAssignCode 0x64 = some (.store .sw a0 a4 0xC, 2) := by decide
theorem fca_at_66 : fetchRel feCondAssignCode 0x66 = some (.load .lw a6 a0 0x18, 4) := by decide
theorem fca_at_6a : fetchRel feCondAssignCode 0x6A = some (.load .lw (17 : Fin 32) a0 0x1C, 4) := by decide
theorem fca_at_6e : fetchRel feCondAssignCode 0x6E = some (.load .lw a5 a1 0x18, 2) := by decide
theorem fca_at_70 : fetchRel feCondAssignCode 0x70 = some (.load .lw (5 : Fin 32) a1 0x1C, 4) := by decide
theorem fca_at_74 : fetchRel feCondAssignCode 0x74 = some (.alu .xor a4 (6 : Fin 32) (28 : Fin 32), 4) := by decide
theorem fca_at_78 : fetchRel feCondAssignCode 0x78 = some (.alu .xor a3 (7 : Fin 32) (29 : Fin 32), 4) := by decide
theorem fca_at_7c : fetchRel feCondAssignCode 0x7C = some (.alu .and a4 a4 a2, 2) := by decide
theorem fca_at_7e : fetchRel feCondAssignCode 0x7E = some (.alu .and a3 a3 a2, 2) := by decide
theorem fca_at_80 : fetchRel feCondAssignCode 0x80 = some (.alu .xor (7 : Fin 32) a4 (28 : Fin 32), 4) := by decide
theorem fca_at_84 : fetchRel feCondAssignCode 0x84 = some (.alu .xor (6 : Fin 32) a3 (29 : Fin 32), 4) := by decide
theorem fca_at_88 : fetchRel feCondAssignCode 0x88 = some (.alu .xor a5 a5 a6, 4) := by decide
theorem fca_at_8c : fetchRel feCondAssignCode 0x8C = some (.alu .xor a3 (5 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fca_at_90 : fetchRel feCondAssignCode 0x90 = some (.alu .and (28 : Fin 32) a5 a2, 4) := by decide
theorem fca_at_94 : fetchRel feCondAssignCode 0x94 = some (.alu .and (5 : Fin 32) a3 a2, 4) := by decide
theorem fca_at_98 : fetchRel feCondAssignCode 0x98 = some (.load .lw a4 a0 0x20, 2) := by decide
theorem fca_at_9a : fetchRel feCondAssignCode 0x9A = some (.load .lw a3 a0 0x24, 2) := by decide
theorem fca_at_9c : fetchRel feCondAssignCode 0x9C = some (.load .lw (30 : Fin 32) a1 0x20, 4) := by decide
theorem fca_at_a0 : fetchRel feCondAssignCode 0xA0 = some (.load .lw (29 : Fin 32) a1 0x24, 4) := by decide
theorem fca_at_a4 : fetchRel feCondAssignCode 0xA4 = some (.alu .xor a1 (28 : Fin 32) a6, 4) := by decide
theorem fca_at_a8 : fetchRel feCondAssignCode 0xA8 = some (.alu .xor a5 (5 : Fin 32) (17 : Fin 32), 4) := by decide
theorem fca_at_ac : fetchRel feCondAssignCode 0xAC = some (.store .sw a0 (7 : Fin 32) 0x10, 4) := by decide
theorem fca_at_b0 : fetchRel feCondAssignCode 0xB0 = some (.store .sw a0 (6 : Fin 32) 0x14, 4) := by decide
theorem fca_at_b4 : fetchRel feCondAssignCode 0xB4 = some (.store .sw a0 a1 0x18, 2) := by decide
theorem fca_at_b6 : fetchRel feCondAssignCode 0xB6 = some (.store .sw a0 a5 0x1C, 2) := by decide
theorem fca_at_b8 : fetchRel feCondAssignCode 0xB8 = some (.alu .xor a1 (30 : Fin 32) a4, 4) := by decide
theorem fca_at_bc : fetchRel feCondAssignCode 0xBC = some (.alu .xor a5 (29 : Fin 32) a3, 4) := by decide
theorem fca_at_c0 : fetchRel feCondAssignCode 0xC0 = some (.alu .and a1 a1 a2, 2) := by decide
theorem fca_at_c2 : fetchRel feCondAssignCode 0xC2 = some (.alu .and a2 a2 a5, 2) := by decide
theorem fca_at_c4 : fetchRel feCondAssignCode 0xC4 = some (.alu .xor a1 a1 a4, 2) := by decide
theorem fca_at_c6 : fetchRel feCondAssignCode 0xC6 = some (.alu .xor a2 a2 a3, 2) := by decide
theorem fca_at_c8 : fetchRel feCondAssignCode 0xC8 = some (.store .sw a0 a1 0x20, 2) := by decide
theorem fca_at_ca : fetchRel feCondAssignCode 0xCA = some (.store .sw a0 a2 0x24, 2) := by decide
theorem fca_at_cc : fetchRel feCondAssignCode 0xCC = some (.jalr x0 ra 0x0, 2) := by decide

def fcaA : List BInstr :=
  [.lw a6 a1 0x0,
    .lw (5 : Fin 32) a0 0x0,
    .lw (28 : Fin 32) a0 0x4,
    .lw (17 : Fin 32) a1 0x4,
    .alu .sub a2 x0 a2,
    .lw (29 : Fin 32) a0 0x8,
    .lw a4 a0 0xC,
    .lw (6 : Fin 32) a1 0x8,
    .lw (7 : Fin 32) a1 0xC,
    .alu .xor a5 a6 (5 : Fin 32),
    .alu .xor a3 (17 : Fin 32) (28 : Fin 32),
    .alu .and a5 a5 a2,
    .alu .and a3 a3 a2,
    .alu .xor (17 : Fin 32) a5 (5 : Fin 32),
    .alu .xor a6 a3 (28 : Fin 32),
    .alu .xor a3 (6 : Fin 32) (29 : Fin 32),
    .alu .xor a5 (7 : Fin 32) a4,
    .alu .and a3 a3 a2,
    .alu .and a5 a5 a2,
    .alu .xor (5 : Fin 32) a3 (29 : Fin 32),
    .alu .xor a4 a4 a5,
    .lw (28 : Fin 32) a0 0x10,
    .lw (29 : Fin 32) a0 0x14,
    .lw (6 : Fin 32) a1 0x10,
    .lw (7 : Fin 32) a1 0x14]

theorem fcaA_end : blockEnd feCondAssignCode 0x0 fcaA = some 0x58 := by decide

def fcaS1 : List BInstr :=
  [.sw a0 (17 : Fin 32) 0x0,
    .sw a0 a6 0x4,
    .sw a0 (5 : Fin 32) 0x8,
    .sw a0 a4 0xC]

theorem fcaS1_end : blockEnd feCondAssignCode 0x58 fcaS1 = some 0x66 := by decide

def fcaB : List BInstr :=
  [.lw a6 a0 0x18,
    .lw (17 : Fin 32) a0 0x1C,
    .lw a5 a1 0x18,
    .lw (5 : Fin 32) a1 0x1C,
    .alu .xor a4 (6 : Fin 32) (28 : Fin 32),
    .alu .xor a3 (7 : Fin 32) (29 : Fin 32),
    .alu .and a4 a4 a2,
    .alu .and a3 a3 a2,
    .alu .xor (7 : Fin 32) a4 (28 : Fin 32),
    .alu .xor (6 : Fin 32) a3 (29 : Fin 32),
    .alu .xor a5 a5 a6,
    .alu .xor a3 (5 : Fin 32) (17 : Fin 32),
    .alu .and (28 : Fin 32) a5 a2,
    .alu .and (5 : Fin 32) a3 a2,
    .lw a4 a0 0x20,
    .lw a3 a0 0x24,
    .lw (30 : Fin 32) a1 0x20,
    .lw (29 : Fin 32) a1 0x24,
    .alu .xor a1 (28 : Fin 32) a6,
    .alu .xor a5 (5 : Fin 32) (17 : Fin 32)]

theorem fcaB_end : blockEnd feCondAssignCode 0x66 fcaB = some 0xAC := by decide

def fcaS2 : List BInstr :=
  [.sw a0 (7 : Fin 32) 0x10,
    .sw a0 (6 : Fin 32) 0x14,
    .sw a0 a1 0x18,
    .sw a0 a5 0x1C]

theorem fcaS2_end : blockEnd feCondAssignCode 0xAC fcaS2 = some 0xB8 := by decide

def fcaC : List BInstr :=
  [.alu .xor a1 (30 : Fin 32) a4,
    .alu .xor a5 (29 : Fin 32) a3,
    .alu .and a1 a1 a2,
    .alu .and a2 a2 a5,
    .alu .xor a1 a1 a4,
    .alu .xor a2 a2 a3]

theorem fcaC_end : blockEnd feCondAssignCode 0xB8 fcaC = some 0xC8 := by decide

def fcaS3 : List BInstr :=
  [.sw a0 a1 0x20,
    .sw a0 a2 0x24]

theorem fcaS3_end : blockEnd feCondAssignCode 0xC8 fcaS3 = some 0xCC := by decide

end

theorem fca_mask (c : Word) (hc : c = 0 ∨ c = 1) (i : Nat) (hi : i < 32) :
    (aluEval .sub 0 c).getLsbD i = decide (c = 1) := by
  rcases hc with rfl | rfl
  · show (0 - 0 : Word).getLsbD i = false
    rw [show (0 - 0 : Word) = 0#32 from rfl, BitVec.getLsbD_zero]
  · show (0 - 1 : Word).getLsbD i = true
    exact ones_bit ⟨i, hi⟩

theorem fca_w1 (o s c : Word) (hc : c = 0 ∨ c = 1) :
    aluEval .xor (aluEval .and (aluEval .xor o s) (aluEval .sub 0 c)) s = if c = 1 then o else s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (((o ^^^ s) &&& aluEval .sub 0 c) ^^^ s).getLsbD i = _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor, fca_mask c hc i hi]
  by_cases h : c = 1
  · rw [ite_eq_left h, decide_eq_true h]
    generalize o.getLsbD i = x; generalize s.getLsbD i = y; cases x <;> cases y <;> rfl
  · rw [ite_eq_right h, decide_eq_false h]
    generalize o.getLsbD i = x; generalize s.getLsbD i = y; cases x <;> cases y <;> rfl

theorem fca_w2 (o s c : Word) (hc : c = 0 ∨ c = 1) :
    aluEval .xor s (aluEval .and (aluEval .xor o s) (aluEval .sub 0 c)) = if c = 1 then o else s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (s ^^^ ((o ^^^ s) &&& aluEval .sub 0 c)).getLsbD i = _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor, fca_mask c hc i hi]
  by_cases h : c = 1
  · rw [ite_eq_left h, decide_eq_true h]
    generalize o.getLsbD i = x; generalize s.getLsbD i = y; cases x <;> cases y <;> rfl
  · rw [ite_eq_right h, decide_eq_false h]
    generalize o.getLsbD i = x; generalize s.getLsbD i = y; cases x <;> cases y <;> rfl

theorem fca_w3 (o s c : Word) (hc : c = 0 ∨ c = 1) :
    aluEval .xor (aluEval .and (aluEval .sub 0 c) (aluEval .xor o s)) s = if c = 1 then o else s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((aluEval .sub 0 c &&& (o ^^^ s)) ^^^ s).getLsbD i = _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor, fca_mask c hc i hi]
  by_cases h : c = 1
  · rw [ite_eq_left h, decide_eq_true h]
    generalize o.getLsbD i = x; generalize s.getLsbD i = y; cases x <;> cases y <;> rfl
  · rw [ite_eq_right h, decide_eq_false h]
    generalize o.getLsbD i = x; generalize s.getLsbD i = y; cases x <;> cases y <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `FieldElement2625::conditional_assign`**: with `choice` 0 or
1 in `a2`, it leaves `self`'s limbs when `choice` is 0 and copies `other`'s
when it is 1, and writes nothing else. -/
theorem feCondAssign_correct (m : Machine) {P s o c retAddr : Word} (hc : CodeIn m.mem P feCondAssignCode)
    (hpc : m.pc = P) (ha0 : reg m a0 = s) (ha1 : reg m a1 = o) (ha2 : reg m a2 = c) (hc01 : c = 0 ∨ c = 1)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hs : s.toNat % 4 = 0) (ho : o.toNat % 4 = 0) (hsw : s.toNat + 40 < 2 ^ 32)
    (sSC : Sep s 40 P feCondAssignCode.length) (sSO : Sep s 40 o 40) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (∀ q, q.val ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ i, i < 10 → limbs m'.mem s i = if c = 1 then limbs m.mem o i else limbs m.mem s i) ∧
      ∀ x, Sep s 40 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have alS : ∀ k, k % 4 = 0 → (s + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k h => aligned_add hs h
  have alO : ∀ k, k % 4 = 0 → (o + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k h => aligned_add ho h
  obtain ⟨mA, cA, uA⟩ := St.block fcaA s0 hc fcaA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fcaA, upd_app, ↓reduceIte, and_true]
    rw [ha0, ha1]
    repeat' apply And.intro
    all_goals first | trivial | (refine alS _ ?_; decide) | (refine alO _ ?_; decide))
  simp only [runBlock, BInstr.run, fcaA] at uA
  have rA : ∀ q, reg mA q = _ := uA.regs
  have mA0 : reg mA a0 = s := by rw [rA]; simp +decide only [upd_app, ↓reduceIte]; exact ha0
  have A17 : reg mA 17 = if c = 1 then memLoad32 m.mem (o + 0x0) else memLoad32 m.mem (s + 0x0) := by
    rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, ha1, ha2]; exact fca_w1 _ _ _ hc01
  have A16 : reg mA 16 = if c = 1 then memLoad32 m.mem (o + 0x4) else memLoad32 m.mem (s + 0x4) := by
    rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, ha1, ha2]; exact fca_w1 _ _ _ hc01
  have A5 : reg mA 5 = if c = 1 then memLoad32 m.mem (o + 0x8) else memLoad32 m.mem (s + 0x8) := by
    rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, ha1, ha2]; exact fca_w1 _ _ _ hc01
  have A14 : reg mA 14 = if c = 1 then memLoad32 m.mem (o + 0xC) else memLoad32 m.mem (s + 0xC) := by
    rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, ha1, ha2]; exact fca_w2 _ _ _ hc01
  have A28 : reg mA 28 = memLoad32 m.mem (s + 0x10) := by rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]
  have A29 : reg mA 29 = memLoad32 m.mem (s + 0x14) := by rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]
  have A6 : reg mA 6 = memLoad32 m.mem (o + 0x10) := by rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1]
  have A7 : reg mA 7 = memLoad32 m.mem (o + 0x14) := by rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1]
  have A12 : reg mA 12 = aluEval .sub 0 c := by rw [rA]; simp +decide only [upd_app, ↓reduceIte]; rw [ha2]
  have A11 : reg mA 11 = o := by rw [rA]; simp +decide only [upd_app, ↓reduceIte]; exact ha1
  have kA : ∀ q, q.val ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mA q = reg m q :=
    fun q hq => by
      have h : q.val ≠ 0 ∧ q ≠ 16 ∧ q ≠ 5 ∧ q ≠ 28 ∧ q ≠ 17 ∧ q ≠ 12 ∧ q ≠ 29 ∧ q ≠ 14 ∧ q ≠ 6 ∧ q ≠ 7 ∧
          q ≠ 15 ∧ q ≠ 13 := by revert hq; revert q; decide
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
      rw [rA]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5, upd_ne h0 h6,
        upd_ne h0 h7, upd_ne h0 h8, upd_ne h0 h9, upd_ne h0 h10, upd_ne h0 h11]
  -- the first four limbs
  obtain ⟨m1, c1, u1⟩ := St.block fcaS1 uA.self hc fcaS1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fcaS1, and_true]
    rw [mA0]
    repeat' apply And.intro
    all_goals first | trivial | (refine alS _ ?_; decide) | exact sSC.sub (by decide))
  simp only [runBlock, BInstr.run, fcaS1] at u1
  rw [mA0] at u1
  have hc1 : CodeIn m1.mem P feCondAssignCode := by
    rw [u1.mem]
    exact (((hc.store32 (sSC.sub (by decide))).store32 (sSC.sub (by decide))).store32 (sSC.sub (by decide))).store32
      (sSC.sub (by decide))
  have u1' : St m1.mem P m1 0x66 (reg m1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have r1 : ∀ q, reg m1 q = reg mA q := u1.regs
  -- loads below the stored limbs, and from `other`, see the entry memory
  have ld1 : ∀ (b : Word), (∀ k, k ∈ [0, 4, 8, 12] → Sep (s + BitVec.ofNat 32 k) 4 b 4) →
      memLoad32 m1.mem b = memLoad32 m.mem b := fun b h => by
    rw [u1.mem, memLoad32_store32_sep (a := s + 12) (h 12 (by decide)),
      memLoad32_store32_sep (a := s + 8) (h 8 (by decide)), memLoad32_store32_sep (a := s + 4) (h 4 (by decide)),
      memLoad32_store32_sep (a := s + 0) (h 0 (by decide))]
  have sepSS : ∀ k j, k + 4 ≤ j ∨ j + 4 ≤ k → k + 4 ≤ 40 → j + 4 ≤ 40 →
      Sep (s + BitVec.ofNat 32 k) 4 (s + BitVec.ofNat 32 j) 4 := fun k j h h1 h2 =>
    sep_offsets s h (by omega) (by omega)
  have sepSO : ∀ k j, k + 4 ≤ 40 → j + 4 ≤ 40 → Sep (s + BitVec.ofNat 32 k) 4 (o + BitVec.ofNat 32 j) 4 :=
    fun k j h1 h2 => (sSO.sub h1).subR h2
  have ldS1 : ∀ j, 16 ≤ j → j + 4 ≤ 40 → memLoad32 m1.mem (s + BitVec.ofNat 32 j) = memLoad32 m.mem (s + BitVec.ofNat 32 j) :=
    fun j h1 h2 => ld1 _ fun k hk => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact sepSS _ _ (.inl (by omega)) (by decide) h2
  have ldO1 : ∀ j, j + 4 ≤ 40 → memLoad32 m1.mem (o + BitVec.ofNat 32 j) = memLoad32 m.mem (o + BitVec.ofNat 32 j) :=
    fun j h => ld1 _ fun k hk => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact sepSO _ _ (by decide) h
  obtain ⟨mB, cB, uB⟩ := St.block fcaB u1' hc1 fcaB_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fcaB, upd_app, ↓reduceIte, and_true]
    rw [r1 a0, r1 a1, mA0, A11]
    repeat' apply And.intro
    all_goals first | trivial | (refine alS _ ?_; decide) | (refine alO _ ?_; decide))
  simp only [runBlock, BInstr.run, fcaB] at uB
  have rB : ∀ q, reg mB q = _ := uB.regs
  have B7 : reg mB 7 = if c = 1 then memLoad32 m.mem (o + 0x10) else memLoad32 m.mem (s + 0x10) := by
    rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, r1, r1, A6, A28, A12]; exact fca_w1 _ _ _ hc01
  have B6 : reg mB 6 = if c = 1 then memLoad32 m.mem (o + 0x14) else memLoad32 m.mem (s + 0x14) := by
    rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, r1, r1, A7, A29, A12]; exact fca_w1 _ _ _ hc01
  have B11 : reg mB 11 = if c = 1 then memLoad32 m.mem (o + 0x18) else memLoad32 m.mem (s + 0x18) := by
    rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, r1, r1, mA0, A11, A12,
      show memLoad32 m1.mem (s + 0x18) = memLoad32 m.mem (s + 0x18) from ldS1 0x18 (by decide) (by decide),
      show memLoad32 m1.mem (o + 0x18) = memLoad32 m.mem (o + 0x18) from ldO1 0x18 (by decide)]
    exact fca_w1 _ _ _ hc01
  have B15 : reg mB 15 = if c = 1 then memLoad32 m.mem (o + 0x1C) else memLoad32 m.mem (s + 0x1C) := by
    rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, r1, r1, mA0, A11, A12,
      show memLoad32 m1.mem (s + 0x1C) = memLoad32 m.mem (s + 0x1C) from ldS1 0x1C (by decide) (by decide),
      show memLoad32 m1.mem (o + 0x1C) = memLoad32 m.mem (o + 0x1C) from ldO1 0x1C (by decide)]
    exact fca_w1 _ _ _ hc01
  have B14 : reg mB 14 = memLoad32 m.mem (s + 0x20) := by
    rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, mA0]
    exact ldS1 0x20 (by decide) (by decide)
  have B13 : reg mB 13 = memLoad32 m.mem (s + 0x24) := by
    rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, mA0]
    exact ldS1 0x24 (by decide) (by decide)
  have B30 : reg mB 30 = memLoad32 m.mem (o + 0x20) := by
    rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, A11]
    exact ldO1 0x20 (by decide)
  have B29 : reg mB 29 = memLoad32 m.mem (o + 0x24) := by
    rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, A11]
    exact ldO1 0x24 (by decide)
  have B12 : reg mB 12 = aluEval .sub 0 c := by rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, A12]
  have mB0 : reg mB a0 = s := by rw [rB]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, mA0]
  obtain ⟨m2, c2, u2⟩ := St.block fcaS2 uB.self hc1 fcaS2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fcaS2, and_true]
    rw [mB0]
    repeat' apply And.intro
    all_goals first | trivial | (refine alS _ ?_; decide) | exact sSC.sub (by decide))
  simp only [runBlock, BInstr.run, fcaS2] at u2
  rw [mB0] at u2
  have hc2 : CodeIn m2.mem P feCondAssignCode := by
    rw [u2.mem]
    exact (((hc1.store32 (sSC.sub (by decide))).store32 (sSC.sub (by decide))).store32 (sSC.sub (by decide))).store32
      (sSC.sub (by decide))
  have u2' : St m2.mem P m2 0xB8 (reg m2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have r2 : ∀ q, reg m2 q = reg mB q := u2.regs
  obtain ⟨mC, cC, uC⟩ := St.block fcaC u2' hc2 fcaC_end (by simp [BlockOk, BInstr.ok, fcaC])
  simp only [runBlock, BInstr.run, fcaC] at uC
  have rC : ∀ q, reg mC q = _ := uC.regs
  have C11 : reg mC 11 = if c = 1 then memLoad32 m.mem (o + 0x20) else memLoad32 m.mem (s + 0x20) := by
    rw [rC]; simp +decide only [upd_app, ↓reduceIte]; simp only [r2]; rw [B30, B14, B12]
    exact fca_w1 _ _ _ hc01
  have C12 : reg mC 12 = if c = 1 then memLoad32 m.mem (o + 0x24) else memLoad32 m.mem (s + 0x24) := by
    rw [rC]; simp +decide only [upd_app, ↓reduceIte]; simp only [r2]; rw [B29, B13, B12]
    exact fca_w3 _ _ _ hc01
  have mC0 : reg mC a0 = s := by rw [rC]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, mB0]
  obtain ⟨m3, c3, u3⟩ := St.block fcaS3 uC.self hc2 fcaS3_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fcaS3, and_true]
    rw [mC0]
    repeat' apply And.intro
    all_goals first | trivial | (refine alS _ ?_; decide) | exact sSC.sub (by decide))
  simp only [runBlock, BInstr.run, fcaS3] at u3
  rw [mC0] at u3
  have hc3 : CodeIn m3.mem P feCondAssignCode := by
    rw [u3.mem]; exact (hc2.store32 (sSC.sub (by decide))).store32 (sSC.sub (by decide))
  have u3' : St m3.mem P m3 0xCC (reg m3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  obtain ⟨m4, d4, pc4, mem4, regs4⟩ := u3'.jalr hc3 fca_at_cc
  have kC : ∀ q, q.val ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m3 q = reg m q :=
    fun q hq => by
      have h : q.val ≠ 0 ∧ q ≠ 16 ∧ q ≠ 5 ∧ q ≠ 28 ∧ q ≠ 17 ∧ q ≠ 12 ∧ q ≠ 29 ∧ q ≠ 14 ∧ q ≠ 6 ∧ q ≠ 7 ∧
          q ≠ 15 ∧ q ≠ 13 ∧ q ≠ 11 ∧ q ≠ 30 := by revert hq; revert q; decide
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
      rw [u3.regs, rC]
      simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5, upd_ne h0 h6,
        upd_ne h0 h7, upd_ne h0 h8, upd_ne h0 h9, upd_ne h0 h10, upd_ne h0 h11, upd_ne h0 h12, upd_ne h0 h13]
      rw [r2, rB]
      simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5, upd_ne h0 h6,
        upd_ne h0 h7, upd_ne h0 h8, upd_ne h0 h9, upd_ne h0 h10, upd_ne h0 h11, upd_ne h0 h12, upd_ne h0 h13]
      rw [r1]; exact kA q hq
  have hS : ∀ x, Sep s 40 x 1 → ∀ k, k + 4 ≤ 40 → Sep (s + BitVec.ofNat 32 k) 4 x 1 := fun x h k hk => h.sub hk
  refine ⟨m4, (cA.trans (c1.trans (cB.trans (c2.trans (cC.trans (c3.trans (.single d4))))))), ?_,
    fun q hq => by rw [regs4]; exact kC q hq, fun i hi => ?_, fun x hx => ?_⟩
  · rw [pc4, kC ra (by decide), hra, add_lit_zero, hret]
  · rw [mem4]
    match i, hi with
    | 0, _ =>
      show memLoad32 m3.mem (s + 0x0) = if c = 1 then memLoad32 m.mem (o + 0x0) else memLoad32 m.mem (s + 0x0)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0x0) (sepSS 0x24 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x20) (b := s + 0x0) (sepSS 0x20 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [u2.mem]
      rw [memLoad32_store32_sep (a := s + 0x1C) (b := s + 0x0) (sepSS 0x1C 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x18) (b := s + 0x0) (sepSS 0x18 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x14) (b := s + 0x0) (sepSS 0x14 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x10) (b := s + 0x0) (sepSS 0x10 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [u1.mem]
      rw [memLoad32_store32_sep (a := s + 0xC) (b := s + 0x0) (sepSS 0xC 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x8) (b := s + 0x0) (sepSS 0x8 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x4) (b := s + 0x0) (sepSS 0x4 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same, A17]
    | 1, _ =>
      show memLoad32 m3.mem (s + 0x4) = if c = 1 then memLoad32 m.mem (o + 0x4) else memLoad32 m.mem (s + 0x4)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0x4) (sepSS 0x24 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x20) (b := s + 0x4) (sepSS 0x20 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [u2.mem]
      rw [memLoad32_store32_sep (a := s + 0x1C) (b := s + 0x4) (sepSS 0x1C 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x18) (b := s + 0x4) (sepSS 0x18 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x14) (b := s + 0x4) (sepSS 0x14 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x10) (b := s + 0x4) (sepSS 0x10 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [u1.mem]
      rw [memLoad32_store32_sep (a := s + 0xC) (b := s + 0x4) (sepSS 0xC 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x8) (b := s + 0x4) (sepSS 0x8 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same, A16]
    | 2, _ =>
      show memLoad32 m3.mem (s + 0x8) = if c = 1 then memLoad32 m.mem (o + 0x8) else memLoad32 m.mem (s + 0x8)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0x8) (sepSS 0x24 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x20) (b := s + 0x8) (sepSS 0x20 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [u2.mem]
      rw [memLoad32_store32_sep (a := s + 0x1C) (b := s + 0x8) (sepSS 0x1C 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x18) (b := s + 0x8) (sepSS 0x18 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x14) (b := s + 0x8) (sepSS 0x14 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x10) (b := s + 0x8) (sepSS 0x10 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [u1.mem]
      rw [memLoad32_store32_sep (a := s + 0xC) (b := s + 0x8) (sepSS 0xC 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same, A5]
    | 3, _ =>
      show memLoad32 m3.mem (s + 0xC) = if c = 1 then memLoad32 m.mem (o + 0xC) else memLoad32 m.mem (s + 0xC)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0xC) (sepSS 0x24 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x20) (b := s + 0xC) (sepSS 0x20 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [u2.mem]
      rw [memLoad32_store32_sep (a := s + 0x1C) (b := s + 0xC) (sepSS 0x1C 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x18) (b := s + 0xC) (sepSS 0x18 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x14) (b := s + 0xC) (sepSS 0x14 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x10) (b := s + 0xC) (sepSS 0x10 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [u1.mem]
      rw [memLoad32_store32_same, A14]
    | 4, _ =>
      show memLoad32 m3.mem (s + 0x10) = if c = 1 then memLoad32 m.mem (o + 0x10) else memLoad32 m.mem (s + 0x10)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0x10) (sepSS 0x24 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x20) (b := s + 0x10) (sepSS 0x20 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [u2.mem]
      rw [memLoad32_store32_sep (a := s + 0x1C) (b := s + 0x10) (sepSS 0x1C 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x18) (b := s + 0x10) (sepSS 0x18 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x14) (b := s + 0x10) (sepSS 0x14 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same, B7]
    | 5, _ =>
      show memLoad32 m3.mem (s + 0x14) = if c = 1 then memLoad32 m.mem (o + 0x14) else memLoad32 m.mem (s + 0x14)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0x14) (sepSS 0x24 0x14 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x20) (b := s + 0x14) (sepSS 0x20 0x14 (.inr (by decide)) (by decide) (by decide))]
      rw [u2.mem]
      rw [memLoad32_store32_sep (a := s + 0x1C) (b := s + 0x14) (sepSS 0x1C 0x14 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x18) (b := s + 0x14) (sepSS 0x18 0x14 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same, B6]
    | 6, _ =>
      show memLoad32 m3.mem (s + 0x18) = if c = 1 then memLoad32 m.mem (o + 0x18) else memLoad32 m.mem (s + 0x18)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0x18) (sepSS 0x24 0x18 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x20) (b := s + 0x18) (sepSS 0x20 0x18 (.inr (by decide)) (by decide) (by decide))]
      rw [u2.mem]
      rw [memLoad32_store32_sep (a := s + 0x1C) (b := s + 0x18) (sepSS 0x1C 0x18 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same, B11]
    | 7, _ =>
      show memLoad32 m3.mem (s + 0x1C) = if c = 1 then memLoad32 m.mem (o + 0x1C) else memLoad32 m.mem (s + 0x1C)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0x1C) (sepSS 0x24 0x1C (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := s + 0x20) (b := s + 0x1C) (sepSS 0x20 0x1C (.inr (by decide)) (by decide) (by decide))]
      rw [u2.mem]
      rw [memLoad32_store32_same, B15]
    | 8, _ =>
      show memLoad32 m3.mem (s + 0x20) = if c = 1 then memLoad32 m.mem (o + 0x20) else memLoad32 m.mem (s + 0x20)
      rw [u3.mem]
      rw [memLoad32_store32_sep (a := s + 0x24) (b := s + 0x20) (sepSS 0x24 0x20 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same, C11]
    | 9, _ =>
      show memLoad32 m3.mem (s + 0x24) = if c = 1 then memLoad32 m.mem (o + 0x24) else memLoad32 m.mem (s + 0x24)
      rw [u3.mem]
      rw [memLoad32_store32_same, C12]
  · rw [mem4, u3.mem]
    rw [memStore32_get_sep (a := s + 0x24) (hS x hx 0x24 (by decide)), memStore32_get_sep (a := s + 0x20) (hS x hx 0x20 (by decide)), u2.mem,
      memStore32_get_sep (a := s + 0x1C) (hS x hx 0x1C (by decide)), memStore32_get_sep (a := s + 0x18) (hS x hx 0x18 (by decide)),
      memStore32_get_sep (a := s + 0x14) (hS x hx 0x14 (by decide)), memStore32_get_sep (a := s + 0x10) (hS x hx 0x10 (by decide)), u1.mem,
      memStore32_get_sep (a := s + 0xC) (hS x hx 0xC (by decide)), memStore32_get_sep (a := s + 0x8) (hS x hx 0x8 (by decide)),
      memStore32_get_sep (a := s + 0x4) (hS x hx 0x4 (by decide)), memStore32_get_sep (a := s + 0x0) (hS x hx 0x0 (by decide))]

end C3.RV32
