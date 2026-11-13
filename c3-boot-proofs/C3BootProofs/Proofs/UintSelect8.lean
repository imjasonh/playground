import C3BootProofs.Proofs.CondNeg12

/-!
# `Uint<8>::select`, as compiled

The same code as `Uint<12>::select` with an 8-limb buffer and a 0x40-byte
frame, so the proof is that file's with the frame's offsets.
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem u8s_at_0 : fetchRel uintSelect8Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem u8s_at_2 : fetchRel uintSelect8Code 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem u8s_at_4 : fetchRel uintSelect8Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem u8s_at_6 : fetchRel uintSelect8Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem u8s_at_8 : fetchRel uintSelect8Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem u8s_at_a : fetchRel uintSelect8Code 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem u8s_at_c : fetchRel uintSelect8Code 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem u8s_at_e : fetchRel uintSelect8Code 0xE = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem u8s_at_10 : fetchRel uintSelect8Code 0x10 = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem u8s_at_12 : fetchRel uintSelect8Code 0x12 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem u8s_at_14 : fetchRel uintSelect8Code 0x14 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem u8s_at_16 : fetchRel uintSelect8Code 0x16 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem u8s_at_18 : fetchRel uintSelect8Code 0x18 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem u8s_at_1c : fetchRel uintSelect8Code 0x1C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem u8s_at_1e : fetchRel uintSelect8Code 0x1E = some (.aluImm .add (8 : Fin 32) sp 0x4, 2) := by decide
theorem u8s_at_20 : fetchRel uintSelect8Code 0x20 = some (.auipc ra 0x4000, 4) := by decide
theorem u8s_at_24 : fetchRel uintSelect8Code 0x24 = some (.jalr ra ra 0xFFFFFAFA, 4) := by decide
theorem u8s_at_28 : fetchRel uintSelect8Code 0x28 = some (.aluImm .add a0 x0 0x8, 2) := by decide
theorem u8s_at_2a : fetchRel uintSelect8Code 0x2A = some (.aluImm .add a1 sp 0x27, 4) := by decide
theorem u8s_at_2e : fetchRel uintSelect8Code 0x2E = some (.branch .beq a0 x0 0x26, 2) := by decide
theorem u8s_at_30 : fetchRel uintSelect8Code 0x30 = some (.load .lw a2 (9 : Fin 32) 0x0, 2) := by decide
theorem u8s_at_32 : fetchRel uintSelect8Code 0x32 = some (.store .sb sp (19 : Fin 32) 0x27, 4) := by decide
theorem u8s_at_36 : fetchRel uintSelect8Code 0x36 = some (.load .lw a3 (20 : Fin 32) 0x0, 4) := by decide
theorem u8s_at_3a : fetchRel uintSelect8Code 0x3A = some (.load .lbu a4 sp 0x27, 4) := by decide
theorem u8s_at_3e : fetchRel uintSelect8Code 0x3E = some (.alu .xor a3 a3 a2, 2) := by decide
theorem u8s_at_40 : fetchRel uintSelect8Code 0x40 = some (.alu .sub a4 x0 a4, 4) := by decide
theorem u8s_at_44 : fetchRel uintSelect8Code 0x44 = some (.alu .and a3 a3 a4, 2) := by decide
theorem u8s_at_46 : fetchRel uintSelect8Code 0x46 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem u8s_at_48 : fetchRel uintSelect8Code 0x48 = some (.alu .xor a2 a2 a3, 2) := by decide
theorem u8s_at_4a : fetchRel uintSelect8Code 0x4A = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem u8s_at_4c : fetchRel uintSelect8Code 0x4C = some (.store .sw (8 : Fin 32) a2 0x0, 2) := by decide
theorem u8s_at_4e : fetchRel uintSelect8Code 0x4E = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem u8s_at_50 : fetchRel uintSelect8Code 0x50 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem u8s_at_52 : fetchRel uintSelect8Code 0x52 = some (.branch .bne a0 x0 0xFFFFFFDE, 2) := by decide
theorem u8s_at_54 : fetchRel uintSelect8Code 0x54 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem u8s_at_56 : fetchRel uintSelect8Code 0x56 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem u8s_at_5a : fetchRel uintSelect8Code 0x5A = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem u8s_at_5c : fetchRel uintSelect8Code 0x5C = some (.auipc ra 0x4000, 4) := by decide
theorem u8s_at_60 : fetchRel uintSelect8Code 0x60 = some (.jalr ra ra 0xFFFFFB26, 4) := by decide
theorem u8s_at_64 : fetchRel uintSelect8Code 0x64 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem u8s_at_66 : fetchRel uintSelect8Code 0x66 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem u8s_at_68 : fetchRel uintSelect8Code 0x68 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem u8s_at_6a : fetchRel uintSelect8Code 0x6A = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem u8s_at_6c : fetchRel uintSelect8Code 0x6C = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem u8s_at_6e : fetchRel uintSelect8Code 0x6E = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem u8s_at_70 : fetchRel uintSelect8Code 0x70 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem u8s_at_72 : fetchRel uintSelect8Code 0x72 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem cnt8_dec : ∀ i : Nat, i < 8 → BitVec.ofNat 32 (8 - i) + 0xFFFFFFFF = BitVec.ofNat 32 (8 - (i + 1)) := by
  decide

theorem cnt8_ne : ∀ i : Nat, i < 8 → (BitVec.ofNat 32 (8 - (i + 1)) != 0) = decide (i + 1 < 8) := by decide

/-- What `Uint<8>::select` saves in its frame, at offsets from its `sp`. -/
abbrev sel8Ps : List (Fin 32 × Word) :=
  [(ra, 0x3C), ((8 : Fin 32), 0x38), ((9 : Fin 32), 0x34), ((18 : Fin 32), 0x30), ((19 : Fin 32), 0x2C),
   ((20 : Fin 32), 0x28)]

/-- The prologue, from 0: open the frame, save registers, keep the
arguments, and set up the call to `memset`. -/
def sel8Pro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFC0, .sw sp ra 0x3C, .sw sp (8 : Fin 32) 0x38, .sw sp (9 : Fin 32) 0x34,
   .sw sp (18 : Fin 32) 0x30, .sw sp (19 : Fin 32) 0x2C, .sw sp (20 : Fin 32) 0x28, .alu .add (19 : Fin 32) x0 a3,
   .alu .add (20 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 4,
   .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0, .aluImm .add (8 : Fin 32) sp 4]

/-- The loop's loads, from 0x30: the two limbs, and the choice through a
byte of the frame. -/
def sel8It : List BInstr :=
  [.lw a2 (9 : Fin 32) 0, .sb sp (19 : Fin 32) 0x27, .lw a3 (20 : Fin 32) 0, .lbu a4 sp 0x27]

/-- From 0x54: set up the call to `memcpy`. -/
def sel8Post : List BInstr := [.aluImm .add a1 sp 4, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (18 : Fin 32)]

/-- The epilogue, from 0x64: restore registers and close the frame. -/
def sel8Epi : List BInstr :=
  [.lw ra sp 0x3C, .lw (8 : Fin 32) sp 0x38, .lw (9 : Fin 32) sp 0x34, .lw (18 : Fin 32) sp 0x30,
   .lw (19 : Fin 32) sp 0x2C, .lw (20 : Fin 32) sp 0x28, .aluImm .add sp sp 0x40]

section
set_option maxRecDepth 20000
theorem sel8Pro_end : blockEnd uintSelect8Code 0 sel8Pro = some 0x20 := by decide
theorem sel8It_end : blockEnd uintSelect8Code 0x30 sel8It = some 0x3E := by decide
theorem sel8Step_end : blockEnd uintSelect8Code 0x3E selStep = some 0x52 := by decide
theorem sel8Post_end : blockEnd uintSelect8Code 0x54 sel8Post = some 0x5C := by decide
theorem sel8Epi_end : blockEnd uintSelect8Code 0x64 sel8Epi = some 0x72 := by decide
end

set_option maxRecDepth 20000 in
theorem sel8Pro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sel8Pro (M, f)).1 = saveMem M (f sp + 0xFFFFFFC0) f sel8Ps ∧
    (runBlock sel8Pro (M, f)).2 sp = f sp + 0xFFFFFFC0 ∧
    (runBlock sel8Pro (M, f)).2 (19 : Fin 32) = f a3 ∧ (runBlock sel8Pro (M, f)).2 (20 : Fin 32) = f a2 ∧
    (runBlock sel8Pro (M, f)).2 (9 : Fin 32) = f a1 ∧ (runBlock sel8Pro (M, f)).2 (18 : Fin 32) = f a0 ∧
    (runBlock sel8Pro (M, f)).2 a0 = f sp + 0xFFFFFFC0 + 4 ∧ (runBlock sel8Pro (M, f)).2 a2 = 0x20 ∧
    (runBlock sel8Pro (M, f)).2 a1 = 0 ∧ (runBlock sel8Pro (M, f)).2 (8 : Fin 32) = f sp + 0xFFFFFFC0 + 4 ∧
    ∀ q, proKeep q = true → (runBlock sel8Pro (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sel8Pro]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte, saveMem]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := sp) hq rfl, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := 9) hq rfl,
        pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := 18) hq rfl,
        pkeep_ne (r := 19) hq rfl, pkeep_ne (r := 20) hq rfl]

theorem sel8Pro_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hF : (f sp + 0xFFFFFFC0).toNat % 4 = 0) (hS : Sep (f sp + 0xFFFFFFC0) 0x40 base len) :
    BlockOk base len sel8Pro (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, sel8Pro, upd, ↓reduceIte, true_and, and_true]
  exact ⟨⟨aligned_add hF (k := 0x3C) (by decide), hS.sub (c := 0x3C) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x38) (by decide), hS.sub (c := 0x38) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x34) (by decide), hS.sub (c := 0x34) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x30) (by decide), hS.sub (c := 0x30) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x2C) (by decide), hS.sub (c := 0x2C) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x28) (by decide), hS.sub (c := 0x28) (l := 4) (by decide)⟩⟩

set_option maxRecDepth 20000 in
theorem sel8It_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sel8It (M, f)).1 = memStore8 M (f sp + 0x27) ((f (19 : Fin 32)).extractLsb' 0 8) ∧
    (runBlock sel8It (M, f)).2 a2 = memLoad32 M (f (9 : Fin 32) + 0) ∧
    (runBlock sel8It (M, f)).2 a3 =
      memLoad32 (memStore8 M (f sp + 0x27) ((f (19 : Fin 32)).extractLsb' 0 8)) (f (20 : Fin 32) + 0) ∧
    (runBlock sel8It (M, f)).2 a4 =
      (memStore8 M (f sp + 0x27) ((f (19 : Fin 32)).extractLsb' 0 8) (f sp + 0x27)).zeroExtend 32 ∧
    ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → (runBlock sel8It (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sel8It]
  refine ⟨?_, ?_, ?_, ?_, fun q q2 q3 q4 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q3, q4]

theorem sel8It_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h9 : (f (9 : Fin 32) + 0).toNat % 4 = 0) (h20 : (f (20 : Fin 32) + 0).toNat % 4 = 0)
    (hs : Sep (f sp + 0x27) 1 base len) : BlockOk base len sel8It (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, sel8It, upd, ↓reduceIte, and_true]
  exact ⟨h9, hs, h20⟩

/-- **One limb of the select**, from 0x30: store limb `i` of `b` or `a` to
the buffer. -/
theorem sel8_iter {M : Word → BitVec 8} {S F ap bp c : Word} {n : Machine} {i : Nat}
    (s : St M S n 0x30 (reg n)) (hc : CodeIn M S uintSelect8Code) (hi : i < 8)
    (hcc : c = 0 ∨ c = 1) (hap : ap.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0) (hF : F.toNat % 4 = 0)
    (sB : Sep (F + 0x27) 1 (bp + BitVec.ofNat 32 (4 * i)) 4)
    (sC1 : Sep (F + 0x27) 1 S uintSelect8Code.length)
    (sC2 : Sep (F + 4 + BitVec.ofNat 32 (4 * i)) 4 S uintSelect8Code.length)
    (rsp : reg n sp = F) (r9 : reg n (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * i))
    (r20 : reg n (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * i))
    (r8 : reg n (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * i))
    (ra0 : reg n a0 = BitVec.ofNat 32 (8 - i)) (r19 : reg n (19 : Fin 32) = c) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore8 M (F + 0x27) (c.extractLsb' 0 8)) (F + 4 + BitVec.ofNat 32 (4 * i))
          (if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))))
        S n' (if i + 1 < 8 then 0x30 else 0x54) (reg n') ∧
      reg n' (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a0 = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
        reg n' q = reg n q := by
  have hz := s.zero
  have ok1 := sel8It_ok (M := M) (f := reg n) (base := S) (len := uintSelect8Code.length)
    (by rw [r9, add_lit_zero]; exact aligned_add hap (by omega))
    (by rw [r20, add_lit_zero]; exact aligned_add hbp (by omega)) (by rw [rsp]; exact sC1)
  obtain ⟨n1, c1, u1⟩ := St.block sel8It s hc sel8It_end ok1
  obtain ⟨em1, e2, e3, e4, fr1⟩ := sel8It_run (M := M) (f := reg n) hz
  rw [em1, rsp, r19] at u1
  rw [rsp, r19] at e3 e4
  rw [r9, add_lit_zero] at e2
  rw [r20, add_lit_zero, memLoad32_store8_sep sB] at e3
  rw [choice_byte M _ c hcc] at e4
  have hc1 := CodeIn.store8 (v := c.extractLsb' 0 8) hc sC1
  obtain ⟨g1, hg1⟩ : ∃ g1, (runBlock sel8It (M, reg n)).2 = g1 := ⟨_, rfl⟩
  rw [hg1] at u1 e2 e3 e4 fr1
  have g8 : g1 (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * i) := by
    rw [fr1 _ (by decide) (by decide) (by decide), r8]
  have okS := selStep_ok (M := memStore8 M (F + 0x27) (c.extractLsb' 0 8)) (f := g1) (base := S)
    (len := uintSelect8Code.length)
    (by rw [g8, add_lit_zero]; exact aligned_add (aligned_add hF (k := 4) (by decide)) (by omega))
    (by rw [g8, add_lit_zero]; exact sC2)
  obtain ⟨em2, f9, f20, f8, fa0, fr2⟩ := selStep_run (M := memStore8 M (F + 0x27) (c.extractLsb' 0 8))
    (f := g1) u1.zero
  obtain ⟨n2, c2, u2⟩ := St.block selStep u1 hc1 sel8Step_end okS
  have u2' := u2.self
  rw [em2, g8, add_lit_zero, e2, e3, e4, selWord_eq _ _ c hcc] at u2'
  obtain ⟨g2, hg2⟩ : ∃ g2, (runBlock selStep (memStore8 M (F + 0x27) (c.extractLsb' 0 8), g1)).2 = g2 :=
    ⟨_, rfl⟩
  rw [hg2] at f9 f20 f8 fa0 fr2
  have v2 : ∀ q, reg n2 q = g2 q := fun q => by rw [u2.regs, hg2]
  have hc2 := CodeIn.store32 (v := if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i))
    else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) hc1 sC2
  have ea0 : reg n2 a0 = BitVec.ofNat 32 (8 - (i + 1)) := by
    rw [v2, fa0, fr1 _ (by decide) (by decide) (by decide), ra0, cnt8_dec i hi]
  have hb : branchTaken .bne (reg n2 a0) (reg n2 x0) = decide (i + 1 < 8) := by
    rw [ea0, u2'.zero]; exact cnt8_ne i hi
  have post : ∀ n3 : Machine, (∀ q, reg n3 q = reg n2 q) →
      reg n3 (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 a0 = BitVec.ofNat 32 (8 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
        reg n3 q = reg n q := fun n3 h3 => by
    refine ⟨?_, ?_, ?_, by rw [h3, ea0], fun q q0 q2 q3 q4 q9 q20 q8 => ?_⟩
    · rw [h3, v2, f9, fr1 _ (by decide) (by decide) (by decide), r9, ptr4]
    · rw [h3, v2, f20, fr1 _ (by decide) (by decide) (by decide), r20, ptr4]
    · rw [h3, v2, f8, g8, ptr4]
    · rw [h3, v2, fr2 q q2 q3 q4 q9 q20 q8 q0, fr1 q q2 q3 q4]
  by_cases hl : i + 1 < 8
  · obtain ⟨n3, d3, u3⟩ := u2'.taken hc2 0x30 u8s_at_52 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n3, c1.trans (c2.trans (.single d3)), by rw [ite_eq_left hl]; exact u3.self, post n3 u3.regs⟩
  · obtain ⟨n3, d3, u3⟩ := u2'.notTaken hc2 0x54 u8s_at_52 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n3, c1.trans (c2.trans (.single d3)), by rw [ite_eq_right hl]; exact u3.self, post n3 u3.regs⟩

theorem slot27 (F : Word) : F + 4 + BitVec.ofNat 32 0x23 = F + 0x27 := by rw [BitVec.add_assoc]; rfl

/-- What one limb of the loop does to memory, apart from the registers. -/
theorem sel8_mem {M MB : Word → BitVec 8} {F ap bp c : Word} {v : BitVec 8} {i : Nat} (hi : i < 8) (hw : F.toNat + 0x40 ≤ 2 ^ 32)
    (sA : Sep (F + 4) 0x24 ap 32) (sB : Sep (F + 4) 0x24 bp 32)
    (hfr : ∀ x, Sep (F + 4) 0x24 x 1 → M x = MB x)
    (hwd : ∀ j, j < i → memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * j)) =
      if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) :
    (∀ x, Sep (F + 4) 0x24 x 1 → memStore32 (memStore8 M (F + 0x27) v) (F + 4 + BitVec.ofNat 32 (4 * i))
      (if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) x =
        MB x) ∧
    ∀ j, j < i + 1 → memLoad32 (memStore32 (memStore8 M (F + 0x27) v) (F + 4 + BitVec.ofNat 32 (4 * i))
      (if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))))
        (F + 4 + BitVec.ofNat 32 (4 * j)) =
      if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j)) := by
  have hF4 : (F + 4).toNat + 0x24 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; omega
  refine ⟨fun x hx => ?_, fun j hj => ?_⟩
  · have h8 : x ≠ F + 0x27 := fun e => by
      have := hx.point (i := 0x23) (j := 0) (by decide) (by decide)
      rw [slot27, add_ofNat_zero] at this; exact this e.symm
    rw [memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), memStore8_ne h8, hfr x hx]
  · by_cases hji : j = i
    · subst hji
      rw [memLoad32_store32_same, load_frame hfr (sB.subR (by omega)), load_frame hfr (sA.subR (by omega))]
    · rw [memLoad32_store32_sep (sep_offsets (F + 4) (c := 4 * i) (n := 4) (d := 4 * j) (k := 4) (by omega)
          (by omega) (by omega)), memLoad32_store8_sep (by
          rw [← slot27]; exact sep_offsets (F + 4) (c := 0x23) (n := 1) (d := 4 * j) (k := 4) (.inr (by omega))
            (by omega) (by omega)), hwd j (by omega)]

/-- **The select loop**, from limb `i` to its end at 0x54: the buffer at
`F + 4` gets limbs `i..7` of `b` or `a`. -/
theorem sel8_loop {S F ap bp c : Word} {MB : Word → BitVec 8} (hcc : c = 0 ∨ c = 1)
    (hap : ap.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0) (hF : F.toNat % 4 = 0) (hw : F.toNat + 0x40 ≤ 2 ^ 32)
    (sA : Sep (F + 4) 0x24 ap 32) (sB : Sep (F + 4) 0x24 bp 32)
    (sC : Sep (F + 4) 0x24 S uintSelect8Code.length) :
    ∀ m i, i + m + 1 = 8 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M S n 0x30 (reg n) → CodeIn M S uintSelect8Code →
      (∀ x, Sep (F + 4) 0x24 x 1 → M x = MB x) →
      (∀ j, j < i → memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * j)) =
        if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) →
      reg n sp = F → reg n (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * i) →
      reg n (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * i) →
      reg n a0 = BitVec.ofNat 32 (8 - i) → reg n (19 : Fin 32) = c →
      ∃ n' M', Steps n n' ∧ St M' S n' 0x54 (reg n') ∧ CodeIn M' S uintSelect8Code ∧
        (∀ x, Sep (F + 4) 0x24 x 1 → M' x = MB x) ∧
        (∀ j, j < 8 → memLoad32 M' (F + 4 + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) ∧
        ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
          reg n' q = reg n q := by
  have hF4 : (F + 4).toNat + 0x24 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; omega
  have hb27 : ∀ {b : Word} {len : Nat}, Sep (F + 4) 0x24 b len → Sep (F + 0x27) 1 b len := fun h => by
    rw [← slot27]; exact h.sub (by decide)
  have step : ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M S n 0x30 (reg n) → CodeIn M S uintSelect8Code →
      (∀ x, Sep (F + 4) 0x24 x 1 → M x = MB x) →
      (∀ j, j < i → memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * j)) =
        if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) →
      reg n sp = F → reg n (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * i) →
      reg n (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * i) →
      reg n a0 = BitVec.ofNat 32 (8 - i) → reg n (19 : Fin 32) = c →
      ∃ n' M', Steps n n' ∧ St M' S n' (if i + 1 < 8 then 0x30 else 0x54) (reg n') ∧
        CodeIn M' S uintSelect8Code ∧
        (∀ x, Sep (F + 4) 0x24 x 1 → M' x = MB x) ∧
        (∀ j, j < i + 1 → memLoad32 M' (F + 4 + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) ∧
        reg n' (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' a0 = BitVec.ofNat 32 (8 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
          reg n' q = reg n q := by
    intro i hi M n s hc hfr hwd rsp r9 r20 r8 ra0 r19
    obtain ⟨n1, c1, u1, e9, e20, e8, ea0, fr⟩ := sel8_iter (i := i) s hc hi hcc hap hbp hF
      (hb27 sB |>.subR (by omega)) (hb27 sC) (sC.sub (by omega))
      rsp r9 r20 r8 ra0 r19
    obtain ⟨m1, m2⟩ := sel8_mem (v := c.extractLsb' 0 8) hi hw sA sB hfr hwd
    exact ⟨n1, _, c1, u1, CodeIn.store32 (CodeIn.store8 hc (hb27 sC)) (sC.sub (by omega)), m1, m2, e9, e20, e8,
      ea0, fr⟩
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hwd rsp r9 r20 r8 ra0 r19
    have i7 : i = 7 := Nat.succ.inj hi
    subst i7
    obtain ⟨n1, M1, c1, u1, hc1, hf1, hw1, _, _, _, _, fr⟩ :=
      step 7 (by decide) s hc hfr hwd rsp r9 r20 r8 ra0 r19
    exact ⟨n1, M1, c1, u1, hc1, hf1, hw1, fr⟩
  | succ m ih =>
    intro i hi M n s hc hfr hwd rsp r9 r20 r8 ra0 r19
    have hl : i + 1 < 8 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, hw1, e9, e20, e8, ea0, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hfr hwd rsp r9 r20 r8 ra0 r19
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hw', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hf1 hw1
      (by rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rsp])
      e9 e20 e8 ea0
      (by rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19])
    exact ⟨n', M', c1.trans c', u', hc', hf', hw', fun q q0 q2 q3 q4 q9 q20 q8 => by
      rw [fr' q q0 q2 q3 q4 q9 q20 q8, fr q q0 q2 q3 q4 q9 q20 q8]⟩

set_option maxRecDepth 20000 in
theorem sel8Epi_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sel8Epi (M, f)).1 = M ∧
    (runBlock sel8Epi (M, f)).2 ra = memLoad32 M (f sp + 0x3C) ∧
    (runBlock sel8Epi (M, f)).2 (8 : Fin 32) = memLoad32 M (f sp + 0x38) ∧
    (runBlock sel8Epi (M, f)).2 (9 : Fin 32) = memLoad32 M (f sp + 0x34) ∧
    (runBlock sel8Epi (M, f)).2 (18 : Fin 32) = memLoad32 M (f sp + 0x30) ∧
    (runBlock sel8Epi (M, f)).2 (19 : Fin 32) = memLoad32 M (f sp + 0x2C) ∧
    (runBlock sel8Epi (M, f)).2 (20 : Fin 32) = memLoad32 M (f sp + 0x28) ∧
    (runBlock sel8Epi (M, f)).2 sp = f sp + 0x40 ∧
    ∀ q, proKeep q = true → q ≠ ra → (runBlock sel8Epi (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sel8Epi]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq hr => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, hr, pkeep_ne (r := sp) hq rfl, pkeep_ne (r := 8) hq rfl,
        pkeep_ne (r := 9) hq rfl, pkeep_ne (r := 18) hq rfl, pkeep_ne (r := 19) hq rfl, pkeep_ne (r := 20) hq rfl]

theorem sel8Epi_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hF : (f sp).toNat % 4 = 0) : BlockOk base len sel8Epi (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, sel8Epi, upd, ↓reduceIte, and_true]
  exact ⟨aligned_add hF (k := 0x3C) (by decide), aligned_add hF (k := 0x38) (by decide),
    aligned_add hF (k := 0x34) (by decide), aligned_add hF (k := 0x30) (by decide),
    aligned_add hF (k := 0x2C) (by decide), aligned_add hF (k := 0x28) (by decide)⟩

theorem sel8Post_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sel8Post (M, f)).1 = M ∧ (runBlock sel8Post (M, f)).2 a1 = f sp + 4 ∧
    (runBlock sel8Post (M, f)).2 a2 = 0x20 ∧ (runBlock sel8Post (M, f)).2 a0 = f (18 : Fin 32) ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → (runBlock sel8Post (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sel8Post]
  refine ⟨trivial, ?_, ?_, ?_, fun q q0 q1 q2 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2]

/-- Where `Uint<8>::select` runs: its code and its callees' at their
offsets, its 0x40-byte frame below `sp0`, and the result and operands,
aligned and apart from what each must not touch. -/
structure Sel8Env (M : Word → BitVec 8) (S sp0 out ap bp : Word) : Prop where
  hS : S.toNat % 2 = 0
  code : CodeIn M S uintSelect8Code
  mset : CodeIn M (S + 0x3B1A) memsetCode
  stub : CodeIn M (S + 0x3B82) memcpyStubCode
  body : CodeIn M (S + 0x3B8A) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  h40 : 0x40 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hwo : out.toNat + 32 < 2 ^ 32
  sFC : Sep (sp0 + 0xFFFFFFC0) 0x40 S uintSelect8Code.length
  sFM : Sep (sp0 + 0xFFFFFFC0) 0x40 (S + 0x3B1A) memsetCode.length
  sFU : Sep (sp0 + 0xFFFFFFC0) 0x40 (S + 0x3B82) memcpyStubCode.length
  sFB : Sep (sp0 + 0xFFFFFFC0) 0x40 (S + 0x3B8A) memcpyBodyCode.length
  sOF : Sep out 32 (sp0 + 0xFFFFFFC0) 0x40
  sOC : Sep out 32 S uintSelect8Code.length
  sOB : Sep out 32 (S + 0x3B8A) memcpyBodyCode.length
  sAF : Sep ap 32 (sp0 + 0xFFFFFFC0) 0x40
  sBF : Sep bp 32 (sp0 + 0xFFFFFFC0) 0x40

theorem frame40 (sp0 : Word) (h : 0x40 ≤ sp0.toNat) : (sp0 + 0xFFFFFFC0).toNat + 0x40 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFFC0 : Word).toNat = 0xFFFFFFC0 := rfl
  rw [this]; have := sp0.isLt; omega

/-- **The compiled `Uint<8>::select`.** It writes `b`'s 8 limbs to `out`
when `choice` is 1 and `a`'s when it is 0, returns with `sp` and the
callee-saved registers restored, and writes only `out` and its frame. -/
theorem uintSelect8_correct (m : Machine) {S out ap bp c retAddr : Word}
    (E : Sel8Env m.mem S (reg m sp) out ap bp) (hpc : m.pc = S) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) (ha3 : reg m a3 = c) (hcc : c = 0 ∨ c = 1) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ i, i < 8 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 m.mem (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 m.mem (ap + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (reg m sp + 0xFFFFFFC0) 0x40 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x) ∧
      ∀ r, selKeep r = true → reg m' r = reg m r := by
  obtain ⟨F, hFd⟩ : ∃ F, reg m sp + 0xFFFFFFC0 = F := ⟨_, rfl⟩
  have sFC := E.sFC; have sFM := E.sFM; have sFU := E.sFU; have sFB := E.sFB
  have sOF := E.sOF; have sAF := E.sAF; have sBF := E.sBF
  rw [hFd] at sFC sFM sFU sFB sOF sAF sBF
  rw [hFd]
  have hFa : F.toNat % 4 = 0 := by rw [← hFd]; exact aligned_add E.hsp (k := 0xFFFFFFC0) (by decide)
  have hFw : F.toNat + 0x40 = (reg m sp).toNat := by rw [← hFd]; exact frame40 _ E.h40
  have hF4a : (F + 4).toNat % 4 = 0 := aligned_add hFa (k := 4) (by decide)
  have hF4w : (F + 4).toNat + 32 < 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; have := (reg m sp).isLt; omega
  have hsub : ∀ x, Sep F 0x40 x 1 → Sep (F + 4) 0x24 x 1 := fun x hx => hx.sub (c := 4) (l := 0x24) (by decide)
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep F 0x40 b code.length → (∀ x, Sep F 0x40 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem S m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- prologue
  have ok0 := sel8Pro_ok (M := m.mem) (f := reg m) (base := S) (len := uintSelect8Code.length)
    (by rw [hFd]; exact hFa) (by rw [hFd]; exact sFC)
  obtain ⟨n1, c1, u1⟩ := St.block sel8Pro s0 E.code sel8Pro_end ok0
  obtain ⟨em1, p_sp, p19, p20, p9, p18, pa0, pa2, pa1, p8, pk⟩ := sel8Pro_run (M := m.mem) (f := reg m) hz
  have u1' := u1.self
  rw [em1, hFd] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock sel8Pro (m.mem, reg m)).2 q := u1.regs
  have I1 : ∀ x, Sep F 0x40 x 1 → saveMem m.mem F (reg m) sel8Ps x = m.mem x :=
    fun x hx => saveMem_outside sel8Ps fun q hq => by
      simp only [sel8Ps, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hx.sub (by decide)
  -- memset of the buffer at F + 4
  obtain ⟨n2, c2, u2, a02, fr2⟩ := u1'.memsetW (B := S + 0x3B1A) (w := 8) (dst := F + 4)
    (even_at S E.hS 0x3B1A (by decide)) (codeS E.code sFC I1) (codeS E.mset sFM I1) u8s_at_20 u8s_at_24
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at S E.hS (0x20 + 8) (by decide)) (by decide) hF4w
    (by decide) hF4a (sFM.sub (c := 4) (l := 32) (by decide)) (by rw [g1, pa0, hFd]) (by rw [g1, pa1])
    (by rw [g1, pa2]; rfl)
  have I2 : ∀ x, Sep F 0x40 x 1 → fillWords (saveMem m.mem F (reg m) sel8Ps) (F + 4) 0 8 x = m.mem x :=
    fun x hx => by
      rw [fillWords_outside (dst := F + 4) 8 (hx.sub (c := 4) (l := 32) (by decide)), I1 x hx]
  have hc2 := codeS E.code sFC I2
  have k2 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n2 q = reg n1 q := fr2
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc2 u8s_at_28 (off' := 0x2A) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc2 u8s_at_2a (off' := 0x2E) (by decide)
  have z2 : reg n2 x0 = 0 := u2.zero
  have g4 : ∀ q, q ≠ a0 → q ≠ a1 → reg n4 q = reg n2 q := fun q q0 q1 => by
    rw [u4.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, z2]
    · simp [upd, h0, q0, q1]
  have v4 : reg n4 a0 = BitVec.ofNat 32 (8 - 0) := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte, z2]
  obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc2 0x30 u8s_at_2e (by decide) (by rw [v4, u4.self.zero]; decide)
  -- the loop
  have r5 : ∀ q, reg n5 q = reg n4 q := u5.regs
  have k1 : ∀ q, proKeep q = true → q.val ∉ [12, 13, 14, 15, 16, 1, 10, 11] → reg n5 q = reg m q := by
    intro q hq hq2
    have n12 : q ≠ a2 := fun e => hq2 (by subst e; decide)
    have n13 : q ≠ a3 := fun e => hq2 (by subst e; decide)
    have n14 : q ≠ a4 := fun e => hq2 (by subst e; decide)
    have n15 : q ≠ a5 := fun e => hq2 (by subst e; decide)
    have n16 : q ≠ a6 := fun e => hq2 (by subst e; decide)
    have n1' : q ≠ ra := fun e => hq2 (by subst e; decide)
    have n10 : q ≠ a0 := fun e => hq2 (by subst e; decide)
    have n11 : q ≠ a1 := fun e => hq2 (by subst e; decide)
    rw [r5, g4 q n10 n11, k2 q n12 n13 n14 n15 n16 n1', g1, pk q hq]
  have sp5 : reg n5 sp = F := by
    rw [r5, g4 _ (by decide) (by decide), k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g1, p_sp, hFd]
  have kp : ∀ q, q.val ∉ [12, 13, 14, 15, 16, 1, 10, 11] → reg n5 q = reg n1 q := fun q hq2 => by
    rw [r5, g4 q (fun e => hq2 (by subst e; decide)) (fun e => hq2 (by subst e; decide)),
      k2 q (fun e => hq2 (by subst e; decide)) (fun e => hq2 (by subst e; decide)) (fun e => hq2 (by subst e; decide))
        (fun e => hq2 (by subst e; decide)) (fun e => hq2 (by subst e; decide)) (fun e => hq2 (by subst e; decide))]
  obtain ⟨n6, M6, c6, u6, hc6, hf6, hw6, fr6⟩ :=
    sel8_loop (MB := fillWords (saveMem m.mem F (reg m) sel8Ps) (F + 4) 0 8) hcc E.hap E.hbp hFa (by omega)
      (sAF.symm.sub (c := 4) (l := 0x24) (by decide)) (sBF.symm.sub (c := 4) (l := 0x24) (by decide))
      (sFC.sub (c := 4) (l := 0x24) (by decide))
      7 0 (by decide) u5.self hc2 (fun _ _ => rfl) (fun j hj => absurd hj (Nat.not_lt_zero j))
      sp5 (by rw [kp _ (by decide), g1, p9, ha1, Nat.mul_zero, add_ofNat_zero])
      (by rw [kp _ (by decide), g1, p20, ha2, Nat.mul_zero, add_ofNat_zero])
      (by rw [kp _ (by decide), g1, p8, hFd, Nat.mul_zero, add_ofNat_zero])
      (by rw [r5, v4]) (by rw [kp _ (by decide), g1, p19, ha3])
  have hM6 : ∀ x, Sep F 0x40 x 1 → M6 x = m.mem x := fun x hx => by rw [hf6 x (hsub x hx), I2 x hx]
  -- copy the buffer out
  have okP : BlockOk S uintSelect8Code.length sel8Post (M6, reg n6) := by
    simp only [BlockOk, BInstr.ok, sel8Post]; exact ⟨trivial, trivial, trivial, trivial⟩
  obtain ⟨n7, c7, u7⟩ := St.block sel8Post u6 hc6 sel8Post_end okP
  obtain ⟨em7, b1, b2, b0, bk⟩ := sel8Post_run (M := M6) (f := reg n6) u6.zero
  rw [em7] at u7
  have k6 : ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
      reg n6 q = reg n5 q := fr6
  have sp6 : reg n6 sp = F := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp5]
  have e18 : reg n6 (18 : Fin 32) = out := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      kp _ (by decide), g1, p18, ha0]
  have e8 : S + 0x3B82 + 8 = S + 0x3B8A := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n8, c8, u8, a08, fr8⟩ := u7.memcpyW (B := S + 0x3B82) (w := 8) (dst := out) (src := F + 4)
    (even_at S E.hS 0x3B82 (by decide)) hc6 (codeS E.stub sFU hM6) (by rw [e8]; exact codeS E.body sFB hM6)
    u8s_at_5c u8s_at_60 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at S E.hS (0x5C + 8) (by decide))
    (by decide) E.hwo (by decide) E.hout hF4a (sOF.subR (c := 4) (l := 32) (by decide)) (by rw [e8]; exact E.sOB)
    (by rw [b0, e18]) (by rw [b1, sp6]) (by rw [b2]; rfl)
  have hM8 : ∀ x, Sep F 0x40 x 1 → Sep out 32 x 1 → copyWords M6 out (F + 4) 8 x = m.mem x := fun x hx ho => by
    rw [copyWords_outside 8 ho, hM6 x hx]
  have hc8 : CodeIn (copyWords M6 out (F + 4) 8) S uintSelect8Code := fun i hi => by
    rw [hM8 _ (sFC.subR (c := i) (l := 1) (by omega)) (E.sOC.subR (c := i) (l := 1) (by omega))]; exact E.code i hi
  have k8 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
      reg n8 q = (runBlock sel8Post (M6, reg n6)).2 q := fr8
  have sp8 : reg n8 sp = F := by
    rw [k8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), bk _ (by decide) (by decide) (by decide), sp6]
  -- the epilogue
  obtain ⟨n9, c9, u9⟩ := St.block sel8Epi u8 hc8 sel8Epi_end (sel8Epi_ok (by rw [sp8]; exact hFa))
  obtain ⟨em9, l1, l8, l9, l18, l19, l20, lsp, lk⟩ := sel8Epi_run (M := copyWords M6 out (F + 4) 8) (f := reg n8)
    u8.zero
  rw [em9] at u9
  have slot : ∀ (r : Fin 32) (o : Word), (r, o) ∈ sel8Ps → 0x28 ≤ o.toNat → o.toNat + 4 ≤ 0x40 →
      (∀ p ∈ sel8Ps, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
        p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32)) →
      memLoad32 (copyWords M6 out (F + 4) 8) (reg n8 sp + o) = reg m r := fun r o hm h1 h2 hp => by
    have hFo : F + BitVec.ofNat 32 o.toNat = F + o := by rw [ofNat_toNat_self]
    rw [sp8, ← hFo, copyWords_load_sep (sOF.subR (c := o.toNat) (l := 4) (by omega)),
      load_frame hf6 (sep_offsets F (c := 4) (n := 0x24) (d := o.toNat) (k := 4) (.inl (by omega)) (by omega)
        (by omega)),
      fillWords_load_sep (dst := F + 4) (sep_offsets F (c := 4) (n := 32) (d := o.toNat) (k := 4) (.inl (by omega))
        (by omega) (by omega)), hFo]
    exact saveMem_slot sel8Ps _ hm hp
  have hz9 : reg n9 x0 = 0 := u9.self.zero
  obtain ⟨m', e10, pc10, mem10, regs10⟩ := u9.jalr hc8 u8s_at_72
  have hra' : (runBlock sel8Epi (copyWords M6 out (F + 4) 8, reg n8)).2 ra = retAddr := by
    rw [l1, slot ra 0x3C (by decide) (by decide) (by decide) (by decide), hra]
  refine ⟨m', c1.trans (c2.trans (.cons d3 (.cons d4 (.cons d5 (c6.trans (c7.trans (c8.trans (c9.trans
    (.single e10))))))))), ?_, ?_, fun i hi => ?_, fun x hx ho => ?_, fun r hr => ?_⟩
  · rw [pc10, hra', add_lit_zero, hret]
  · rw [regs10, lsp, sp8, ← hFd, BitVec.add_assoc]; exact BitVec.add_zero _
  · have hwo := E.hwo
    rw [mem10, copyWords_load 8 i hi (by omega), hw6 i hi, load_frame I2 (sBF.symm.subR (by omega)),
      load_frame I2 (sAF.symm.subR (by omega))]
  · rw [mem10, hM8 x hx ho]
  · have key : ∀ r : Fin 32, selKeep r = true → r = ra ∨ r = sp ∨ r = (8 : Fin 32) ∨ r = (9 : Fin 32) ∨
        r = (18 : Fin 32) ∨ r = (19 : Fin 32) ∨ r = (20 : Fin 32) ∨
        (proKeep r = true ∧ r ≠ ra ∧ r.val ∉ [12, 13, 14, 15, 16, 1, 10, 11] ∧ r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧
          r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ a6 ∧ r ≠ a7 ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ (9 : Fin 32) ∧ r ≠ (20 : Fin 32) ∧
          r ≠ (8 : Fin 32)) := by decide
    rw [regs10]
    rcases key r hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      ⟨hp, hnr, hnl, n0, n1', n2', n3', n4', n5', n6', n7', nt0, nt1, n9', n20', n8'⟩
    · exact hra'.trans hra.symm
    · rw [lsp, sp8, ← hFd, BitVec.add_assoc]; exact BitVec.add_zero _
    · rw [l8, slot 8 0x38 (by decide) (by decide) (by decide) (by decide)]
    · rw [l9, slot 9 0x34 (by decide) (by decide) (by decide) (by decide)]
    · rw [l18, slot 18 0x30 (by decide) (by decide) (by decide) (by decide)]
    · rw [l19, slot 19 0x2C (by decide) (by decide) (by decide) (by decide)]
    · rw [l20, slot 20 0x28 (by decide) (by decide) (by decide) (by decide)]
    · rw [lk r hp hnr, k8 r n1' n2' n3' n4' n5' n6' n7' nt0 nt1 hnr, bk r n0 n1' n2',
        k6 r n0 n2' n3' n4' n9' n20' n8', k1 r hp hnl]

end C3.RV32
