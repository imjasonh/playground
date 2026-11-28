import C3BootProofs.Proofs.UintSelect12

/-!
# `Uint<2>::select`, as compiled

`crypto_bigint`'s `Uint::select(a, b, choice)` for two limbs, which
`safegcd`'s `conditional_negate_in_place_wide` calls. The compiled code
builds the result in an 8-byte buffer on its stack, one limb per pass of a
two-pass loop, with the masking of `Uint<12>::select` (`selWord`), then
stores both words to the result.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem u2s_at_0 : fetchRel uintSelect2Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem u2s_at_2 : fetchRel uintSelect2Code 0x2 = some (.store .sw sp x0 0x0, 2) := by decide
theorem u2s_at_4 : fetchRel uintSelect2Code 0x4 = some (.store .sw sp x0 0x4, 2) := by decide
theorem u2s_at_6 : fetchRel uintSelect2Code 0x6 = some (.alu .add (17 : Fin 32) x0 sp, 2) := by decide
theorem u2s_at_8 : fetchRel uintSelect2Code 0x8 = some (.aluImm .add (5 : Fin 32) x0 0x2, 2) := by decide
theorem u2s_at_a : fetchRel uintSelect2Code 0xA = some (.aluImm .add a6 sp 0xF, 4) := by decide
theorem u2s_at_e : fetchRel uintSelect2Code 0xE = some (.branch .beq (5 : Fin 32) x0 0x30, 4) := by decide
theorem u2s_at_12 : fetchRel uintSelect2Code 0x12 = some (.load .lw a4 a1 0x0, 2) := by decide
theorem u2s_at_14 : fetchRel uintSelect2Code 0x14 = some (.store .sb sp a3 0xF, 4) := by decide
theorem u2s_at_18 : fetchRel uintSelect2Code 0x18 = some (.load .lw (6 : Fin 32) a2 0x0, 4) := by decide
theorem u2s_at_1c : fetchRel uintSelect2Code 0x1C = some (.load .lbu (7 : Fin 32) sp 0xF, 4) := by decide
theorem u2s_at_20 : fetchRel uintSelect2Code 0x20 = some (.alu .xor (6 : Fin 32) (6 : Fin 32) a4, 4) := by decide
theorem u2s_at_24 : fetchRel uintSelect2Code 0x24 = some (.alu .sub a5 x0 (7 : Fin 32), 4) := by decide
theorem u2s_at_28 : fetchRel uintSelect2Code 0x28 = some (.alu .and a5 (6 : Fin 32) a5, 4) := by decide
theorem u2s_at_2c : fetchRel uintSelect2Code 0x2C = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem u2s_at_2e : fetchRel uintSelect2Code 0x2E = some (.alu .xor a4 a4 a5, 2) := by decide
theorem u2s_at_30 : fetchRel uintSelect2Code 0x30 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem u2s_at_32 : fetchRel uintSelect2Code 0x32 = some (.store .sw (17 : Fin 32) a4 0x0, 4) := by decide
theorem u2s_at_36 : fetchRel uintSelect2Code 0x36 = some (.aluImm .add (17 : Fin 32) (17 : Fin 32) 0x4, 2) := by decide
theorem u2s_at_38 : fetchRel uintSelect2Code 0x38 = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem u2s_at_3a : fetchRel uintSelect2Code 0x3A = some (.branch .bne (5 : Fin 32) x0 0xFFFFFFD8, 4) := by decide
theorem u2s_at_3e : fetchRel uintSelect2Code 0x3E = some (.load .lw a1 sp 0x0, 2) := by decide
theorem u2s_at_40 : fetchRel uintSelect2Code 0x40 = some (.load .lw a2 sp 0x4, 2) := by decide
theorem u2s_at_42 : fetchRel uintSelect2Code 0x42 = some (.store .sw a0 a1 0x0, 2) := by decide
theorem u2s_at_44 : fetchRel uintSelect2Code 0x44 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem u2s_at_46 : fetchRel uintSelect2Code 0x46 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem u2s_at_48 : fetchRel uintSelect2Code 0x48 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The prologue, from 0: the buffer zeroed, and the loop's pointer and
counter. -/
def u2Pro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .sw sp x0 0x0, .sw sp x0 0x4, .alu .add (17 : Fin 32) x0 sp,
   .aluImm .add (5 : Fin 32) x0 0x2, .aluImm .add a6 sp 0xF]

/-- The loop's loads, from 0x12: the two limbs, and the choice through a
byte of the frame. -/
def u2It : List BInstr := [.lw a4 a1 0x0, .sb sp a3 0xF, .lw (6 : Fin 32) a2 0x0, .lbu (7 : Fin 32) sp 0xF]

/-- From 0x20: one limb of the select. -/
def u2Step : List BInstr :=
  [.alu .xor (6 : Fin 32) (6 : Fin 32) a4, .alu .sub a5 x0 (7 : Fin 32), .alu .and a5 (6 : Fin 32) a5,
   .aluImm .add a1 a1 0x4, .alu .xor a4 a4 a5, .aluImm .add a2 a2 0x4, .sw (17 : Fin 32) a4 0x0,
   .aluImm .add (17 : Fin 32) (17 : Fin 32) 0x4, .aluImm .add (5 : Fin 32) (5 : Fin 32) 0xFFFFFFFF]

/-- The epilogue, from 0x3E: the buffer to the result, and the frame's
release. -/
def u2Epi : List BInstr := [.lw a1 sp 0x0, .lw a2 sp 0x4, .sw a0 a1 0x0, .sw a0 a2 0x4, .aluImm .add sp sp 0x10]

section
set_option maxRecDepth 20000
theorem u2Pro_end : blockEnd uintSelect2Code 0 u2Pro = some 0xE := by decide
theorem u2It_end : blockEnd uintSelect2Code 0x12 u2It = some 0x20 := by decide
theorem u2Step_end : blockEnd uintSelect2Code 0x20 u2Step = some 0x3A := by decide
theorem u2Epi_end : blockEnd uintSelect2Code 0x3E u2Epi = some 0x48 := by decide
end

set_option maxRecDepth 20000 in
theorem u2Pro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock u2Pro (M, f)).1 = memStore32 (memStore32 M (f sp + 0xFFFFFFF0 + 0) 0) (f sp + 0xFFFFFFF0 + 4) 0 ∧
    (runBlock u2Pro (M, f)).2 sp = f sp + 0xFFFFFFF0 ∧
    (runBlock u2Pro (M, f)).2 (17 : Fin 32) = f sp + 0xFFFFFFF0 ∧
    (runBlock u2Pro (M, f)).2 (5 : Fin 32) = 2 ∧
    ∀ q, q ≠ sp → q ≠ (17 : Fin 32) → q ≠ (5 : Fin 32) → q ≠ a6 → (runBlock u2Pro (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, u2Pro]
  refine ⟨?_, ?_, ?_, ?_, fun q q1 q2 q3 q4 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1, q2, q3, q4]

theorem u2Pro_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base G : Word} {len : Nat}
    (hG : f sp + 0xFFFFFFF0 = G) (hGa : G.toNat % 4 = 0) (hS : Sep G 16 base len) :
    BlockOk base len u2Pro (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, u2Pro, upd, ↓reduceIte, true_and, and_true]
  rw [show aluEval AluOp.add (f sp) 0xFFFFFFF0 = G from hG]
  exact ⟨⟨aligned_add hGa (k := 0) (by decide), hS.sub (c := 0) (l := 4) (by decide)⟩,
    ⟨aligned_add hGa (k := 4) (by decide), hS.sub (c := 4) (l := 4) (by decide)⟩⟩

set_option maxRecDepth 20000 in
theorem u2It_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock u2It (M, f)).1 = memStore8 M (f sp + 0xF) ((f a3).extractLsb' 0 8) ∧
    (runBlock u2It (M, f)).2 a4 = memLoad32 M (f a1 + 0) ∧
    (runBlock u2It (M, f)).2 (6 : Fin 32) = memLoad32 (memStore8 M (f sp + 0xF) ((f a3).extractLsb' 0 8)) (f a2 + 0) ∧
    (runBlock u2It (M, f)).2 (7 : Fin 32) =
      (memStore8 M (f sp + 0xF) ((f a3).extractLsb' 0 8) (f sp + 0xF)).zeroExtend 32 ∧
    ∀ q, q.val ≠ 0 → q ≠ a4 → q ≠ (6 : Fin 32) → q ≠ (7 : Fin 32) → (runBlock u2It (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, u2It]
  refine ⟨?_, ?_, ?_, ?_, fun q h0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp [upd, h0, q1, q2, q3]

theorem u2It_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h11 : (f a1 + 0).toNat % 4 = 0) (h12 : (f a2 + 0).toNat % 4 = 0)
    (hs : Sep (f sp + 0xF) 1 base len) : BlockOk base len u2It (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, u2It, upd, ↓reduceIte, and_true]
  exact ⟨h11, hs, h12⟩

set_option maxRecDepth 20000 in
theorem u2Step_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock u2Step (M, f)).1 = memStore32 M (f (17 : Fin 32) + 0) (selWord (f a4) (f (6 : Fin 32)) (f (7 : Fin 32))) ∧
    (runBlock u2Step (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock u2Step (M, f)).2 a2 = f a2 + 4 ∧
    (runBlock u2Step (M, f)).2 (17 : Fin 32) = f (17 : Fin 32) + 4 ∧
    (runBlock u2Step (M, f)).2 (5 : Fin 32) = f (5 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q.val ≠ 0 → q ≠ (6 : Fin 32) → q ≠ a5 → q ≠ a1 → q ≠ a4 → q ≠ a2 → q ≠ (17 : Fin 32) →
      q ≠ (5 : Fin 32) → (runBlock u2Step (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, u2Step]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q h0 q1 q2 q3 q4 q5 q6 q7 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp [upd, h0, q1, q2, q3, q4, q5, q6, q7]

theorem u2Step_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h17 : (f (17 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (17 : Fin 32) + 0) 4 base len) :
    BlockOk base len u2Step (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, u2Step, upd, ↓reduceIte, true_and, and_true]
  exact ⟨h17, hs⟩

set_option maxRecDepth 20000 in
theorem u2Epi_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock u2Epi (M, f)).1 = memStore32 (memStore32 M (f a0 + 0) (memLoad32 M (f sp + 0)))
      (f a0 + 4) (memLoad32 M (f sp + 4)) ∧
    (runBlock u2Epi (M, f)).2 sp = f sp + 0x10 ∧
    ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ sp → (runBlock u2Epi (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, u2Epi]
  refine ⟨?_, ?_, fun q h0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp [upd, h0, q1, q2, q3]

theorem u2Epi_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hsp : (f sp).toNat % 4 = 0) (h10 : (f a0).toNat % 4 = 0) (hs : Sep (f a0) 8 base len) :
    BlockOk base len u2Epi (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, u2Epi, upd, ↓reduceIte, and_true]
  exact ⟨aligned_add hsp (k := 0) (by decide), aligned_add hsp (k := 4) (by decide),
    ⟨aligned_add h10 (k := 0) (by decide), hs.sub (c := 0) (l := 4) (by decide)⟩,
    ⟨aligned_add h10 (k := 4) (by decide), hs.sub (c := 4) (l := 4) (by decide)⟩⟩

theorem cnt2_dec : ∀ i : Nat, i < 2 → BitVec.ofNat 32 (2 - i) + 0xFFFFFFFF = BitVec.ofNat 32 (2 - (i + 1)) := by
  decide

theorem cnt2_ne : ∀ i : Nat, i < 2 → (BitVec.ofNat 32 (2 - (i + 1)) != 0) = decide (i + 1 < 2) := by decide

/-- **One limb of the select**, from 0x12: limb `i` of `b` or `a` to the
buffer at `G`. -/
theorem u2_iter {M : Word → BitVec 8} {S G ap bp c : Word} {n : Machine} {i : Nat}
    (s : St M S n 0x12 (reg n)) (hc : CodeIn M S uintSelect2Code) (hi : i < 2)
    (hcc : c = 0 ∨ c = 1) (hap : ap.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0) (hG : G.toNat % 4 = 0)
    (sB : Sep (G + 0xF) 1 (bp + BitVec.ofNat 32 (4 * i)) 4)
    (sC1 : Sep (G + 0xF) 1 S uintSelect2Code.length)
    (sC2 : Sep (G + BitVec.ofNat 32 (4 * i)) 4 S uintSelect2Code.length)
    (rsp : reg n sp = G) (r11 : reg n a1 = ap + BitVec.ofNat 32 (4 * i))
    (r12 : reg n a2 = bp + BitVec.ofNat 32 (4 * i))
    (r17 : reg n (17 : Fin 32) = G + BitVec.ofNat 32 (4 * i))
    (r5 : reg n (5 : Fin 32) = BitVec.ofNat 32 (2 - i)) (r13 : reg n a3 = c) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore8 M (G + 0xF) (c.extractLsb' 0 8)) (G + BitVec.ofNat 32 (4 * i))
          (if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))))
        S n' (if i + 1 < 2 then 0x12 else 0x3E) (reg n') ∧
      reg n' a1 = ap + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a2 = bp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (17 : Fin 32) = G + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (5 : Fin 32) = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) →
        q ≠ (7 : Fin 32) → q ≠ (17 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  have ok1 := u2It_ok (M := M) (f := reg n) (base := S) (len := uintSelect2Code.length)
    (by rw [r11, add_lit_zero]; exact aligned_add hap (by omega))
    (by rw [r12, add_lit_zero]; exact aligned_add hbp (by omega)) (by rw [rsp]; exact sC1)
  obtain ⟨n1, c1, u1⟩ := St.block u2It s hc u2It_end ok1
  obtain ⟨em1, e4, e6, e7, fr1⟩ := u2It_run (M := M) (f := reg n)
  rw [em1, rsp, r13] at u1
  rw [rsp, r13] at e6 e7
  rw [r11, add_lit_zero] at e4
  rw [r12, add_lit_zero, memLoad32_store8_sep sB] at e6
  rw [choice_byte M _ c hcc] at e7
  have hc1 := CodeIn.store8 (v := c.extractLsb' 0 8) hc sC1
  obtain ⟨g1, hg1⟩ : ∃ g1, (runBlock u2It (M, reg n)).2 = g1 := ⟨_, rfl⟩
  rw [hg1] at u1 e4 e6 e7 fr1
  have g17 : g1 (17 : Fin 32) = G + BitVec.ofNat 32 (4 * i) := by
    rw [fr1 _ (by decide) (by decide) (by decide) (by decide), r17]
  have okS := u2Step_ok (M := memStore8 M (G + 0xF) (c.extractLsb' 0 8)) (f := g1) (base := S)
    (len := uintSelect2Code.length)
    (by rw [g17, add_lit_zero]; exact aligned_add hG (by omega))
    (by rw [g17, add_lit_zero]; exact sC2)
  obtain ⟨em2, f11, f12, f17, f5, fr2⟩ := u2Step_run (M := memStore8 M (G + 0xF) (c.extractLsb' 0 8)) (f := g1)
  obtain ⟨n2, c2, u2⟩ := St.block u2Step u1 hc1 u2Step_end okS
  have u2' := u2.self
  rw [em2, g17, add_lit_zero, e4, e6, e7, selWord_eq _ _ c hcc] at u2'
  obtain ⟨g2, hg2⟩ : ∃ g2, (runBlock u2Step (memStore8 M (G + 0xF) (c.extractLsb' 0 8), g1)).2 = g2 :=
    ⟨_, rfl⟩
  rw [hg2] at f11 f12 f17 f5 fr2
  have v2 : ∀ q, reg n2 q = g2 q := fun q => by rw [u2.regs, hg2]
  have hc2 := CodeIn.store32 (v := if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i))
    else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) hc1 sC2
  have e5 : reg n2 (5 : Fin 32) = BitVec.ofNat 32 (2 - (i + 1)) := by
    rw [v2, f5, fr1 _ (by decide) (by decide) (by decide) (by decide), r5, cnt2_dec i hi]
  have hb : branchTaken .bne (reg n2 (5 : Fin 32)) (reg n2 x0) = decide (i + 1 < 2) := by
    rw [e5, u2'.zero]; exact cnt2_ne i hi
  have post : ∀ n3 : Machine, (∀ q, reg n3 q = reg n2 q) →
      reg n3 a1 = ap + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 a2 = bp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 (17 : Fin 32) = G + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 (5 : Fin 32) = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) →
        q ≠ (7 : Fin 32) → q ≠ (17 : Fin 32) → reg n3 q = reg n q := fun n3 h3 => by
    refine ⟨?_, ?_, ?_, by rw [h3, e5], fun q h0 q1 q2 q4 q5 q5' q6 q7 q17 => ?_⟩
    · rw [h3, v2, f11, fr1 _ (by decide) (by decide) (by decide) (by decide), r11, ptr4]
    · rw [h3, v2, f12, fr1 _ (by decide) (by decide) (by decide) (by decide), r12, ptr4]
    · rw [h3, v2, f17, g17, ptr4]
    · rw [h3, v2, fr2 q h0 q6 q5 q1 q4 q2 q17 q5', fr1 q h0 q4 q6 q7]
  by_cases hl : i + 1 < 2
  · obtain ⟨n3, d3, u3⟩ := u2'.taken hc2 0x12 u2s_at_3a (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n3, c1.trans (c2.trans (.single d3)), by rw [ite_eq_left hl]; exact u3.self, post n3 u3.regs⟩
  · obtain ⟨n3, d3, u3⟩ := u2'.notTaken hc2 0x3E u2s_at_3a (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n3, c1.trans (c2.trans (.single d3)), by rw [ite_eq_right hl]; exact u3.self, post n3 u3.regs⟩

theorem u2_slot0 (a : Word) : a + BitVec.ofNat 32 (4 * 0) = a := BitVec.add_zero a

theorem u2_slot1 (a : Word) : a + BitVec.ofNat 32 (4 * (0 + 1)) = a + 4 := rfl

theorem u2_slot1' (a : Word) : a + BitVec.ofNat 32 (4 * 1) = a + 4 := rfl

set_option maxHeartbeats 4000000 in
/-- **The compiled `Uint<2>::select`**, called with the result at `out`,
operands at `ap` and `bp`, and a choice `c` of 0 or 1: it stores `b`'s two
limbs at `out` when `c` is 1 and `a`'s when it is 0. It returns with `sp`
as it was, changes no register but `t0` through `t2`, `a1`, `a2`, and `a4`
through `a7`, and changes no memory outside the 16 bytes below `sp` and the
8 bytes at `out`. The operands are read before the result is written, so
they may overlap it. -/
theorem uintSelect2_correct (m : Machine) {P sp0 out ap bp c retAddr : Word}
    (hc : CodeIn m.mem P uintSelect2Code) (hpc : m.pc = P) (hsp : reg m sp = sp0)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp) (ha3 : reg m a3 = c)
    (hcc : c = 0 ∨ c = 1) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hs4 : sp0.toNat % 4 = 0) (hs16 : 16 ≤ sp0.toNat) (hap : ap.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0)
    (hout : out.toNat % 4 = 0)
    (sFC : Sep (sp0 + 0xFFFFFFF0) 16 P uintSelect2Code.length) (sOC : Sep out 8 P uintSelect2Code.length)
    (sAF : Sep ap 8 (sp0 + 0xFFFFFFF0) 16) (sBF : Sep bp 8 (sp0 + 0xFFFFFFF0) 16) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∉ [5, 6, 7, 11, 12, 14, 15, 16, 17] → reg m' q = reg m q) ∧
      (∀ i, i < 2 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 m.mem (bp + BitVec.ofNat 32 (4 * i))
        else memLoad32 m.mem (ap + BitVec.ofNat 32 (4 * i))) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFF0) 16 x 1 → Sep out 8 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hGd⟩ : ∃ G, sp0 + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hGd] at sFC sAF sBF ⊢
  have hGa : G.toNat % 4 = 0 := by rw [← hGd]; exact aligned_add hs4 (k := 0xFFFFFFF0) (by decide)
  have hGw : G.toNat + 16 = sp0.toNat := by
    rw [← hGd, BitVec.toNat_add]
    have : (0xFFFFFFF0 : Word).toNat = 0xFFFFFFF0 := rfl
    rw [this]; have := sp0.isLt; omega
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the prologue
  have sG0 : Sep G 4 P uintSelect2Code.length := by
    have := sFC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have sG4 : Sep (G + 4) 4 P uintSelect2Code.length := sFC.sub (c := 4) (l := 4) (by decide)
  have sGF : Sep (G + 0xF) 1 P uintSelect2Code.length := sFC.sub (c := 0xF) (l := 1) (by decide)
  obtain ⟨n1, c1, u1⟩ := St.block u2Pro s0 hc u2Pro_end (u2Pro_ok (by rw [hsp, hGd]) hGa sFC)
  obtain ⟨em1, p_sp, p17, p5, pk⟩ := u2Pro_run (M := m.mem) (f := reg m) hz
  rw [hsp, hGd] at em1 p_sp p17
  rw [em1, add_lit_zero] at u1
  obtain ⟨g, hg⟩ : ∃ g, (runBlock u2Pro (m.mem, reg m)).2 = g := ⟨_, rfl⟩
  rw [hg] at u1 p_sp p17 p5 pk
  have hc1 : CodeIn (memStore32 (memStore32 m.mem G 0) (G + 4) 0) P uintSelect2Code :=
    (hc.store32 sG0).store32 sG4
  obtain ⟨n2, d2, u2⟩ := u1.notTaken hc1 0x12 u2s_at_e (by decide) (by rw [p5, u1.zero]; rfl)
  have v2 : ∀ q, reg n2 q = g q := u2.regs
  have u2s := u2.self
  -- the two passes
  have sBi : ∀ i, i < 2 → Sep (G + 0xF) 1 (bp + BitVec.ofNat 32 (4 * i)) 4 := fun i hi =>
    (sBF.symm.sub (c := 0xF) (l := 1) (by decide)).subR (by omega)
  obtain ⟨n3, c3, u3, e11, e12, e17, e5, fr3⟩ := u2_iter (i := 0) u2s hc1 (by decide) hcc hap hbp hGa
    (sBi 0 (by decide)) sGF (by rw [u2_slot0]; exact sG0)
    (by rw [v2, p_sp]) (by rw [v2, pk _ (by decide) (by decide) (by decide) (by decide), ha1, u2_slot0])
    (by rw [v2, pk _ (by decide) (by decide) (by decide) (by decide), ha2, u2_slot0])
    (by rw [v2, p17, u2_slot0]) (by rw [v2, p5]; rfl)
    (by rw [v2, pk _ (by decide) (by decide) (by decide) (by decide), ha3])
  rw [show (if 0 + 1 < 2 then 0x12 else 0x3E : Nat) = 0x12 from rfl, u2_slot0, u2_slot0, u2_slot0] at u3
  rw [u2_slot1] at e11 e12 e17
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore8 (memStore32 (memStore32 m.mem G 0) (G + 4) 0) (G + 0xF)
      (c.extractLsb' 0 8)) G (if c = 1 then memLoad32 (memStore32 (memStore32 m.mem G 0) (G + 4) 0) bp
        else memLoad32 (memStore32 (memStore32 m.mem G 0) (G + 4) 0) ap) = M2 := ⟨_, rfl⟩
  rw [hM2] at u3
  have hc3 : CodeIn M2 P uintSelect2Code := by rw [← hM2]; exact (hc1.store8 sGF).store32 sG0
  obtain ⟨n4, c4, u4, -, -, -, -, fr4⟩ := u2_iter (i := 1) u3 hc3 (by decide) hcc hap hbp hGa
    (sBi 1 (by decide)) sGF (by rw [u2_slot1']; exact sG4)
    (by rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v2, p_sp])
    (by rw [u2_slot1']; exact e11) (by rw [u2_slot1']; exact e12) (by rw [u2_slot1']; exact e17) e5
    (by rw [fr3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v2, pk _ (by decide) (by decide) (by decide) (by decide), ha3])
  rw [show (if 1 + 1 < 2 then 0x12 else 0x3E : Nat) = 0x3E from rfl, u2_slot1', u2_slot1', u2_slot1'] at u4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore8 M2 (G + 0xF) (c.extractLsb' 0 8)) (G + 4)
      (if c = 1 then memLoad32 M2 (bp + 4) else memLoad32 M2 (ap + 4)) = M3 := ⟨_, rfl⟩
  rw [hM3] at u4
  have hc4 : CodeIn M3 P uintSelect2Code := by rw [← hM3]; exact (hc3.store8 sGF).store32 sG4
  -- registers through the passes
  have k4 : ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) →
      q ≠ (7 : Fin 32) → q ≠ (17 : Fin 32) → reg n4 q = reg n2 q := fun q h0 h1 h2 h4 h5 h5' h6 h7 h17 => by
    rw [fr4 q h0 h1 h2 h4 h5 h5' h6 h7 h17, fr3 q h0 h1 h2 h4 h5 h5' h6 h7 h17]
  have r4sp : reg n4 sp = G := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), v2, p_sp]
  have r4a0 : reg n4 a0 = out := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), v2, pk _ (by decide) (by decide) (by decide) (by decide), ha0]
  -- the epilogue
  have sO0 : Sep out 4 P uintSelect2Code.length := by
    have := sOC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have sO4 : Sep (out + 4) 4 P uintSelect2Code.length := sOC.sub (c := 4) (l := 4) (by decide)
  obtain ⟨n5, c5, u5⟩ := St.block u2Epi u4 hc4 u2Epi_end
    (u2Epi_ok (by rw [r4sp]; exact hGa) (by rw [r4a0]; exact hout) (by rw [r4a0]; exact sOC))
  obtain ⟨em5, q_sp, qk⟩ := u2Epi_run (M := M3) (f := reg n4)
  rw [r4sp, r4a0, add_lit_zero, add_lit_zero] at em5
  rw [r4sp] at q_sp
  rw [em5] at u5
  obtain ⟨g5, hg5⟩ : ∃ g5, (runBlock u2Epi (M3, reg n4)).2 = g5 := ⟨_, rfl⟩
  rw [hg5] at u5 q_sp qk
  have hc5 := (hc4.store32 (v := memLoad32 M3 G) sO0).store32 (v := memLoad32 M3 (G + 4)) sO4
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc5 u2s_at_48
  have keep : ∀ q, q.val ∉ [5, 6, 7, 11, 12, 14, 15, 16, 17] → q ≠ sp → reg n6 q = reg m q := fun q hq hs => by
    have hm : ∀ v, v ∈ [5, 6, 7, 11, 12, 14, 15, 16, 17] → q.val ≠ v := fun v hv e => hq (e ▸ hv)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [regs6, u5.zero, s0.zero]
    · have ne : ∀ v : Fin 32, v.val ∈ [5, 6, 7, 11, 12, 14, 15, 16, 17] → q ≠ v := fun v hv e => hm _ hv (e ▸ rfl)
      rw [regs6, qk q h0 (ne a1 (by decide)) (ne a2 (by decide)) hs,
        k4 q h0 (ne a1 (by decide)) (ne a2 (by decide)) (ne a4 (by decide)) (ne a5 (by decide))
          (ne 5 (by decide)) (ne 6 (by decide)) (ne 7 (by decide)) (ne 17 (by decide)), v2,
        pk q hs (ne 17 (by decide)) (ne 5 (by decide)) (ne a6 (by decide))]
  -- memory
  have fr1 : ∀ x, Sep G 16 x 1 → memStore32 (memStore32 m.mem G 0) (G + 4) 0 x = m.mem x := fun x hx => by
    have h0 : Sep G 4 x 1 := by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have h4 : Sep (G + 4) 4 x 1 := hx.sub (c := 4) (l := 4) (by decide)
    rw [memStore32_get_sep h4, memStore32_get_sep h0]
  have fstep : ∀ {Ma Mb : Word → BitVec 8} (a : Word) (k : Nat) (v : Word), a = G + BitVec.ofNat 32 k →
      k + 4 ≤ 12 → (∀ x, Sep G 16 x 1 → Ma x = Mb x) →
      ∀ x, Sep G 16 x 1 → memStore32 (memStore8 Ma (G + 0xF) (c.extractLsb' 0 8)) a v x =
        Mb x := fun a k v ha hk hf x hx => by
    rw [ha]
    have h8 : x ≠ G + 0xF := fun e => by
      have := hx.point (i := 0xF) (j := 0) (by decide) (by decide)
      rw [add_ofNat_zero] at this; exact this e.symm
    rw [memStore32_get_sep (hx.sub (c := k) (l := 4) (by omega)), memStore8_ne h8, hf x hx]
  have fr2 : ∀ x, Sep G 16 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2]; exact fstep G 0 _ (add_ofNat_zero G).symm (by decide) fr1 x hx
  have fr3' : ∀ x, Sep G 16 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3]; exact fstep (G + 4) 4 _ rfl (by decide) fr2 x hx
  have lA0 : memLoad32 (memStore32 (memStore32 m.mem G 0) (G + 4) 0) ap = memLoad32 m.mem ap :=
    load_frame fr1 (by have := sAF.symm.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  have lB0 : memLoad32 (memStore32 (memStore32 m.mem G 0) (G + 4) 0) bp = memLoad32 m.mem bp :=
    load_frame fr1 (by have := sBF.symm.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
  have lA4 : memLoad32 M2 (ap + 4) = memLoad32 m.mem (ap + 4) :=
    load_frame fr2 (sAF.symm.subR (c := 4) (l := 4) (by decide))
  have lB4 : memLoad32 M2 (bp + 4) = memLoad32 m.mem (bp + 4) :=
    load_frame fr2 (sBF.symm.subR (c := 4) (l := 4) (by decide))
  have sGG4 : Sep G 4 (G + 4) 4 := by
    have := sep_offsets G (c := 0) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have sGF0 : Sep (G + 0xF) 1 G 4 := by
    have := sep_offsets G (c := 0xF) (n := 1) (d := 0) (k := 4) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have sGF4 : Sep (G + 0xF) 1 (G + 4) 4 :=
    sep_offsets G (c := 0xF) (n := 1) (d := 4) (k := 4) (by decide) (by decide) (by decide)
  have w0 : memLoad32 M3 G = if c = 1 then memLoad32 m.mem bp else memLoad32 m.mem ap := by
    rw [← hM3, memLoad32_store32_sep sGG4.symm, memLoad32_store8_sep sGF0, ← hM2, memLoad32_store32_same, lA0, lB0]
  have w1 : memLoad32 M3 (G + 4) = if c = 1 then memLoad32 m.mem (bp + 4) else memLoad32 m.mem (ap + 4) := by
    rw [← hM3, memLoad32_store32_same, lA4, lB4]
  have sOO : Sep out 4 (out + 4) 4 := by
    have := sep_offsets out (c := 0) (n := 4) (d := 4) (k := 4) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨n6, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.single d6))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc6, ← regs6, keep ra (by decide) (by decide), add_lit_zero, hra, hret]
  · rw [regs6, q_sp, ← hGd, BitVec.add_assoc]; exact BitVec.add_zero sp0
  · intro q hq
    by_cases hs : q = sp
    · subst hs; rw [regs6, q_sp, hsp, ← hGd, BitVec.add_assoc]; exact BitVec.add_zero sp0
    · exact keep q hq hs
  · intro i hi
    rw [mem6]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [u2_slot0, u2_slot0, u2_slot0, memLoad32_store32_sep sOO.symm, memLoad32_store32_same, w0]
    · rw [u2_slot1', u2_slot1', u2_slot1', memLoad32_store32_same, w1]
  · intro x hS hO
    have h4 : Sep (out + 4) 4 x 1 := hO.sub (c := 4) (l := 4) (by decide)
    rw [mem6, memStore32_get_sep h4,
      memStore32_get_sep (by have := hO.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this),
      fr3' x hS]

end C3.RV32
