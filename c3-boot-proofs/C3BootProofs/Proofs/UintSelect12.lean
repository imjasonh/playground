import C3BootProofs.Proofs.MontMul12
import C3BootProofs.Proofs.FieldWideMulMain

/-!
# `Uint<12>::select`, as compiled

`crypto_bigint`'s `Uint::select(a, b, choice)` returns `b` when `choice` is
set and `a` otherwise, limb by limb with masks so it takes the same path
either way. The compiled `Uint<12>::select` builds the result in a zeroed
buffer on its stack, one limb per call to an outlined helper, and copies it
out with `memcpy`.
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem us_at_0 : fetchRel uintSelect12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem us_at_2 : fetchRel uintSelect12Code 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem us_at_4 : fetchRel uintSelect12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem us_at_6 : fetchRel uintSelect12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem us_at_8 : fetchRel uintSelect12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem us_at_a : fetchRel uintSelect12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem us_at_c : fetchRel uintSelect12Code 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem us_at_e : fetchRel uintSelect12Code 0xE = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem us_at_10 : fetchRel uintSelect12Code 0x10 = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem us_at_12 : fetchRel uintSelect12Code 0x12 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem us_at_14 : fetchRel uintSelect12Code 0x14 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem us_at_16 : fetchRel uintSelect12Code 0x16 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem us_at_18 : fetchRel uintSelect12Code 0x18 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem us_at_1c : fetchRel uintSelect12Code 0x1C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem us_at_1e : fetchRel uintSelect12Code 0x1E = some (.aluImm .add (8 : Fin 32) sp 0x4, 2) := by decide
theorem us_at_20 : fetchRel uintSelect12Code 0x20 = some (.auipc ra 0xD000, 4) := by decide
theorem us_at_24 : fetchRel uintSelect12Code 0x24 = some (.jalr ra ra 0x176, 4) := by decide
theorem us_at_28 : fetchRel uintSelect12Code 0x28 = some (.aluImm .add a0 x0 0xC, 2) := by decide
theorem us_at_2a : fetchRel uintSelect12Code 0x2A = some (.aluImm .add a1 sp 0x37, 4) := by decide
theorem us_at_2e : fetchRel uintSelect12Code 0x2E = some (.branch .beq a0 x0 0x1A, 2) := by decide
theorem us_at_30 : fetchRel uintSelect12Code 0x30 = some (.load .lw a2 (9 : Fin 32) 0x0, 2) := by decide
theorem us_at_32 : fetchRel uintSelect12Code 0x32 = some (.store .sb sp (19 : Fin 32) 0x37, 4) := by decide
theorem us_at_36 : fetchRel uintSelect12Code 0x36 = some (.load .lw a3 (20 : Fin 32) 0x0, 4) := by decide
theorem us_at_3a : fetchRel uintSelect12Code 0x3A = some (.load .lbu a4 sp 0x37, 4) := by decide
theorem us_at_3e : fetchRel uintSelect12Code 0x3E = some (.auipc (5 : Fin 32) 0xD000, 4) := by decide
theorem us_at_42 : fetchRel uintSelect12Code 0x42 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFFB0, 4) := by decide
theorem us_at_46 : fetchRel uintSelect12Code 0x46 = some (.branch .bne a0 x0 0xFFFFFFEA, 2) := by decide
theorem us_at_48 : fetchRel uintSelect12Code 0x48 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem us_at_4a : fetchRel uintSelect12Code 0x4A = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem us_at_4e : fetchRel uintSelect12Code 0x4E = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem us_at_50 : fetchRel uintSelect12Code 0x50 = some (.auipc ra 0xD000, 4) := by decide
theorem us_at_54 : fetchRel uintSelect12Code 0x54 = some (.jalr ra ra 0x1AE, 4) := by decide
theorem us_at_58 : fetchRel uintSelect12Code 0x58 = some (.load .lw ra sp 0x4C, 2) := by decide
theorem us_at_5a : fetchRel uintSelect12Code 0x5A = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem us_at_5c : fetchRel uintSelect12Code 0x5C = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem us_at_5e : fetchRel uintSelect12Code 0x5E = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem us_at_60 : fetchRel uintSelect12Code 0x60 = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem us_at_62 : fetchRel uintSelect12Code 0x62 = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem us_at_64 : fetchRel uintSelect12Code 0x64 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem us_at_66 : fetchRel uintSelect12Code 0x66 = some (.jalr x0 ra 0x0, 2) := by decide
theorem uss_at_14 : fetchRel uintSelect12StepCode 0x14 = some (.jalr x0 (5 : Fin 32) 0x0, 2) := by decide

end

theorem CodeIn.runBlock {base : Word} {code : List Nat} :
    ∀ (is : List BInstr) {M : Word → BitVec 8} {f : Fin 32 → Word}, CodeIn M base code →
      BlockOk base code.length is (M, f) → CodeIn (runBlock is (M, f)).1 base code
  | [], _, _, hc, _ => hc
  | i :: is, M, f, hc, hok => by
    have h1 := CodeIn.run i hc hok.1
    exact CodeIn.runBlock is (M := (i.run (M, f)).1) (f := (i.run (M, f)).2) h1 hok.2

/-- A caller's `auipc t0, imm; jalr t0, o(t0)` into a helper at `b` that
runs the block `is` and returns with `jr t0`, run from offset `off` to
`off + 8` of the caller. -/
theorem St.callBlock {M : Word → BitVec 8} {base b : Word} {code hcode : List Nat} {m : Machine}
    {off : Nat} {f : Fin 32 → Word} (s : St M base m off f) (hc : CodeIn M base code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc t0 imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr t0 t0 o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = b) (hbe : b.toNat % 2 = 0)
    (hl : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hh : CodeIn M b hcode) (is : List BInstr) {e : Nat} (he : blockEnd hcode 0 is = some e)
    (hj : fetchRel hcode e = some (.jalr x0 t0 0, 2))
    (hok : BlockOk b hcode.length is (M, upd f t0 (base + BitVec.ofNat 32 (off + 8))))
    (ht : (runBlock is (M, upd f t0 (base + BitVec.ofNat 32 (off + 8)))).2 t0 = base + BitVec.ofNat 32 (off + 8)) :
    ∃ m', Steps m m' ∧ St (runBlock is (M, upd f t0 (base + BitVec.ofNat 32 (off + 8)))).1 base m' (off + 8)
      (runBlock is (M, upd f t0 (base + BitVec.ofNat 32 (off + 8)))).2 := by
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  have hg : ∀ r, reg m2 r = upd f t0 (base + BitVec.ofNat 32 (off + 8)) r := fun r => by
    rw [regs2, hL]
    by_cases hr : r.val = 0
    · simp [upd, hr]
    · by_cases ht : r = t0
      · subst ht; simp [upd]
      · simp [upd, hr, ht]
  have hp2 : m2.pc = b := by
    rw [pc2, show upd f t0 (base + BitVec.ofNat 32 off + imm) t0 = base + BitVec.ofNat 32 off + imm from
      by simp +decide [upd], hb]; exact even_clear _ hbe
  have u : St M b m2 0 (upd f t0 (base + BitVec.ofNat 32 (off + 8))) := ⟨by rw [hp2]; simp, mem2, hg⟩
  obtain ⟨m3, c3, u3⟩ := St.block is u hh he hok
  have hc3 := CodeIn.runBlock is hh hok
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := u3.jalr hc3 hj
  refine ⟨m4, .cons e1 (.cons e2 (c3.trans (.single e4))), ⟨?_, mem4, regs4⟩⟩
  rw [pc4, ht, add_lit_zero]; exact even_clear _ hl

theorem saveMem_load_out {G a : Word} {f : Fin 32 → Word} :
    ∀ (ps : List (Fin 32 × Word)) (M : Word → BitVec 8), (∀ p ∈ ps, Sep (G + p.2) 4 a 4) →
      memLoad32 (saveMem M G f ps) a = memLoad32 M a
  | [], _, _ => rfl
  | p :: ps, M, h => by
    simp only [saveMem]
    rw [saveMem_load_out ps _ (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      memLoad32_store32_sep (h p List.mem_cons_self)]

theorem sep_word_offsets (G c d : Word) (h : c.toNat + 4 ≤ d.toNat ∨ d.toNat + 4 ≤ c.toNat)
    (hc : c.toNat + 4 ≤ 2 ^ 32) (hd : d.toNat + 4 ≤ 2 ^ 32) : Sep (G + c) 4 (G + d) 4 := by
  have := sep_offsets G (c := c.toNat) (n := 4) (d := d.toNat) (k := 4) h hc hd
  rwa [ofNat_toNat_self, ofNat_toNat_self] at this

/-- **A saved slot holds its register**, when the other slots of the list
are apart from it. -/
theorem saveMem_slot {G : Word} {f : Fin 32 → Word} {r : Fin 32} {o : Word} :
    ∀ (ps : List (Fin 32 × Word)) (M : Word → BitVec 8), (r, o) ∈ ps →
      (∀ p ∈ ps, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
        p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32)) →
      memLoad32 (saveMem M G f ps) (G + o) = f r
  | [], _, h, _ => absurd h List.not_mem_nil
  | p :: ps, M, hm, h => by
    simp only [saveMem]
    by_cases hin : (r, o) ∈ ps
    · exact saveMem_slot ps _ hin (fun q hq => h q (List.mem_cons_of_mem _ hq))
    · have hp : p = (r, o) := by
        rcases List.mem_cons.mp hm with e | e
        · exact e.symm
        · exact absurd e hin
      subst hp
      rw [saveMem_load_out ps _ (fun q hq => ?_), memLoad32_store32_same]
      rcases h q (List.mem_cons_of_mem _ hq) with e | ⟨h1, h2, h3⟩
      · exact absurd (e ▸ hq) hin
      · exact sep_word_offsets G _ _ h1 h2 h3

/-- What `Uint<12>::select` saves in its frame, at offsets from its `sp`. -/
abbrev selPs : List (Fin 32 × Word) :=
  [(ra, 0x4C), ((8 : Fin 32), 0x48), ((9 : Fin 32), 0x44), ((18 : Fin 32), 0x40), ((19 : Fin 32), 0x3C),
   ((20 : Fin 32), 0x38)]

/-- The prologue, from 0: open the frame, save registers, keep the
arguments, and set up the call to `memset`. -/
def selPro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFB0, .sw sp ra 0x4C, .sw sp (8 : Fin 32) 0x48, .sw sp (9 : Fin 32) 0x44,
   .sw sp (18 : Fin 32) 0x40, .sw sp (19 : Fin 32) 0x3C, .sw sp (20 : Fin 32) 0x38, .alu .add (19 : Fin 32) x0 a3,
   .alu .add (20 : Fin 32) x0 a2, .alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 4,
   .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0, .aluImm .add (8 : Fin 32) sp 4]

/-- The loop's loads, from 0x30: the two limbs, and the choice through a
byte of the frame. -/
def selIt : List BInstr :=
  [.lw a2 (9 : Fin 32) 0, .sb sp (19 : Fin 32) 0x37, .lw a3 (20 : Fin 32) 0, .lbu a4 sp 0x37]

/-- The outlined helper `OUTLINED_FUNCTION_83`: one limb of the select. -/
def selStep : List BInstr :=
  [.alu .xor a3 a3 a2, .alu .sub a4 x0 a4, .alu .and a3 a3 a4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4,
   .alu .xor a2 a2 a3, .aluImm .add (20 : Fin 32) (20 : Fin 32) 4, .sw (8 : Fin 32) a2 0,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 4, .aluImm .add a0 a0 0xFFFFFFFF]

/-- From 0x48: set up the call to `memcpy`. -/
def selPost : List BInstr := [.aluImm .add a1 sp 4, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]

/-- The epilogue, from 0x58: restore registers and close the frame. -/
def selEpi : List BInstr :=
  [.lw ra sp 0x4C, .lw (8 : Fin 32) sp 0x48, .lw (9 : Fin 32) sp 0x44, .lw (18 : Fin 32) sp 0x40,
   .lw (19 : Fin 32) sp 0x3C, .lw (20 : Fin 32) sp 0x38, .aluImm .add sp sp 0x50]

section
set_option maxRecDepth 20000
theorem selPro_end : blockEnd uintSelect12Code 0 selPro = some 0x20 := by decide
theorem selIt_end : blockEnd uintSelect12Code 0x30 selIt = some 0x3E := by decide
theorem selStep_end : blockEnd uintSelect12StepCode 0 selStep = some 0x14 := by decide
theorem selPost_end : blockEnd uintSelect12Code 0x48 selPost = some 0x50 := by decide
theorem selEpi_end : blockEnd uintSelect12Code 0x58 selEpi = some 0x66 := by decide
end

/-- The limb the select keeps: `a` when the mask is clear, `b` when set. -/
def selWord (a b c : Word) : Word := a ^^^ ((b ^^^ a) &&& (0 - c))

theorem ones_bit : ∀ i : Fin 32, (0 - 1 : Word).getLsbD i.val = true := by decide

theorem selWord_eq (a b c : Word) (hc : c = 0 ∨ c = 1) : selWord a b c = if c = 1 then b else a := by
  unfold selWord
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases hc with rfl | rfl
  · have h0 : (0 : Word).getLsbD i = false := BitVec.getLsbD_zero
    rw [ite_eq_right (by decide), show (0 - 0 : Word) = 0 from rfl, BitVec.getLsbD_xor, BitVec.getLsbD_and,
      h0, Bool.and_false, Bool.xor_false]
  · have h1 : (0 - 1 : Word).getLsbD i = true := ones_bit ⟨i, hi⟩
    rw [ite_eq_left rfl, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor, h1, Bool.and_true]
    generalize a.getLsbD i = x
    generalize b.getLsbD i = y
    cases x <;> cases y <;> rfl

/-- The registers the prologue leaves alone. -/
def proKeep (q : Fin 32) : Bool := q.val ∉ [2, 8, 9, 10, 11, 12, 18, 19, 20]

set_option maxRecDepth 20000 in
theorem selPro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock selPro (M, f)).1 = saveMem M (f sp + 0xFFFFFFB0) f selPs ∧
    (runBlock selPro (M, f)).2 sp = f sp + 0xFFFFFFB0 ∧
    (runBlock selPro (M, f)).2 (19 : Fin 32) = f a3 ∧ (runBlock selPro (M, f)).2 (20 : Fin 32) = f a2 ∧
    (runBlock selPro (M, f)).2 (9 : Fin 32) = f a1 ∧ (runBlock selPro (M, f)).2 (18 : Fin 32) = f a0 ∧
    (runBlock selPro (M, f)).2 a0 = f sp + 0xFFFFFFB0 + 4 ∧ (runBlock selPro (M, f)).2 a2 = 0x30 ∧
    (runBlock selPro (M, f)).2 a1 = 0 ∧ (runBlock selPro (M, f)).2 (8 : Fin 32) = f sp + 0xFFFFFFB0 + 4 ∧
    ∀ q, proKeep q = true → (runBlock selPro (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, selPro]
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

theorem selPro_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hF : (f sp + 0xFFFFFFB0).toNat % 4 = 0) (hS : Sep (f sp + 0xFFFFFFB0) 0x50 base len) :
    BlockOk base len selPro (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, selPro, upd, ↓reduceIte, true_and, and_true]
  exact ⟨⟨aligned_add hF (k := 0x4C) (by decide), hS.sub (c := 0x4C) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x48) (by decide), hS.sub (c := 0x48) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x44) (by decide), hS.sub (c := 0x44) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x40) (by decide), hS.sub (c := 0x40) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x3C) (by decide), hS.sub (c := 0x3C) (l := 4) (by decide)⟩,
    ⟨aligned_add hF (k := 0x38) (by decide), hS.sub (c := 0x38) (l := 4) (by decide)⟩⟩

set_option maxRecDepth 20000 in
theorem selIt_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock selIt (M, f)).1 = memStore8 M (f sp + 0x37) ((f (19 : Fin 32)).extractLsb' 0 8) ∧
    (runBlock selIt (M, f)).2 a2 = memLoad32 M (f (9 : Fin 32) + 0) ∧
    (runBlock selIt (M, f)).2 a3 =
      memLoad32 (memStore8 M (f sp + 0x37) ((f (19 : Fin 32)).extractLsb' 0 8)) (f (20 : Fin 32) + 0) ∧
    (runBlock selIt (M, f)).2 a4 =
      (memStore8 M (f sp + 0x37) ((f (19 : Fin 32)).extractLsb' 0 8) (f sp + 0x37)).zeroExtend 32 ∧
    ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → (runBlock selIt (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, selIt]
  refine ⟨?_, ?_, ?_, ?_, fun q q2 q3 q4 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q3, q4]

theorem selIt_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h9 : (f (9 : Fin 32) + 0).toNat % 4 = 0) (h20 : (f (20 : Fin 32) + 0).toNat % 4 = 0)
    (hs : Sep (f sp + 0x37) 1 base len) : BlockOk base len selIt (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, selIt, upd, ↓reduceIte, and_true]
  exact ⟨h9, hs, h20⟩

set_option maxRecDepth 20000 in
theorem selStep_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock selStep (M, f)).1 = memStore32 M (f (8 : Fin 32) + 0) (selWord (f a2) (f a3) (f a4)) ∧
    (runBlock selStep (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock selStep (M, f)).2 (20 : Fin 32) = f (20 : Fin 32) + 4 ∧
    (runBlock selStep (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 4 ∧
    (runBlock selStep (M, f)).2 a0 = f a0 + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ a0 →
      (runBlock selStep (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, selStep]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q q2 q3 q4 q9 q20 q8 q0 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q3, q4, q9, q20, q8, q0]

theorem selStep_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h8 : (f (8 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (8 : Fin 32) + 0) 4 base len) :
    BlockOk base len selStep (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, selStep, upd, ↓reduceIte, true_and, and_true]
  exact ⟨h8, hs⟩

theorem cnt12_dec : ∀ i : Nat, i < 12 → BitVec.ofNat 32 (12 - i) + 0xFFFFFFFF = BitVec.ofNat 32 (12 - (i + 1)) := by
  decide

theorem cnt12_ne : ∀ i : Nat, i < 12 → (BitVec.ofNat 32 (12 - (i + 1)) != 0) = decide (i + 1 < 12) := by decide

theorem choice_byte (M : Word → BitVec 8) (a c : Word) (hc : c = 0 ∨ c = 1) :
    (memStore8 M a (c.extractLsb' 0 8) a).zeroExtend 32 = c := by
  unfold memStore8; rw [ite_eq_left rfl]; rcases hc with rfl | rfl <;> decide

theorem upd_t0 (f : Fin 32 → Word) (v : Word) : upd f t0 v t0 = v := by simp +decide [upd]

/-- **One limb of the select**, from 0x30: store limb `i` of `b` or `a` to
the buffer, through the outlined helper. -/
theorem sel_iter {M : Word → BitVec 8} {S F ap bp c : Word} {n : Machine} {i : Nat}
    (s : St M S n 0x30 (reg n)) (hc : CodeIn M S uintSelect12Code)
    (hcs : CodeIn M (S + 0xCFEE) uintSelect12StepCode) (hS : S.toNat % 2 = 0) (hi : i < 12)
    (hcc : c = 0 ∨ c = 1) (hap : ap.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0) (hF : F.toNat % 4 = 0)
    (sB : Sep (F + 0x37) 1 (bp + BitVec.ofNat 32 (4 * i)) 4)
    (sC1 : Sep (F + 0x37) 1 S uintSelect12Code.length)
    (sC2 : Sep (F + 4 + BitVec.ofNat 32 (4 * i)) 4 S uintSelect12Code.length)
    (sC3 : Sep (F + 4 + BitVec.ofNat 32 (4 * i)) 4 (S + 0xCFEE) uintSelect12StepCode.length)
    (sC4 : Sep (F + 0x37) 1 (S + 0xCFEE) uintSelect12StepCode.length)
    (rsp : reg n sp = F) (r9 : reg n (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * i))
    (r20 : reg n (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * i))
    (r8 : reg n (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * i))
    (ra0 : reg n a0 = BitVec.ofNat 32 (12 - i)) (r19 : reg n (19 : Fin 32) = c) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore8 M (F + 0x37) (c.extractLsb' 0 8)) (F + 4 + BitVec.ofNat 32 (4 * i))
          (if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))))
        S n' (if i + 1 < 12 then 0x30 else 0x48) (reg n') ∧
      reg n' (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
        q ≠ t0 → reg n' q = reg n q := by
  have hz := s.zero
  have ok1 := selIt_ok (M := M) (f := reg n) (base := S) (len := uintSelect12Code.length)
    (by rw [r9, add_lit_zero]; exact aligned_add hap (by omega))
    (by rw [r20, add_lit_zero]; exact aligned_add hbp (by omega)) (by rw [rsp]; exact sC1)
  obtain ⟨n1, c1, u1⟩ := St.block selIt s hc selIt_end ok1
  obtain ⟨em1, e2, e3, e4, fr1⟩ := selIt_run (M := M) (f := reg n) hz
  rw [em1, rsp, r19] at u1
  rw [rsp, r19] at e3 e4
  rw [r9, add_lit_zero] at e2
  rw [r20, add_lit_zero, memLoad32_store8_sep sB] at e3
  rw [choice_byte M _ c hcc] at e4
  have hc1 := CodeIn.store8 (v := c.extractLsb' 0 8) hc sC1
  have hcs1 := CodeIn.store8 (v := c.extractLsb' 0 8) hcs sC4
  obtain ⟨g1, hg1⟩ : ∃ g1, (runBlock selIt (M, reg n)).2 = g1 := ⟨_, rfl⟩
  rw [hg1] at u1 e2 e3 e4 fr1
  have g8 : upd g1 t0 (S + BitVec.ofNat 32 (0x3E + 8)) (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * i) := by
    rw [upd_ne (by decide) (by decide), fr1 _ (by decide) (by decide) (by decide), r8]
  have okS := selStep_ok (M := memStore8 M (F + 0x37) (c.extractLsb' 0 8))
    (f := upd g1 t0 (S + BitVec.ofNat 32 (0x3E + 8))) (base := S + 0xCFEE) (len := uintSelect12StepCode.length)
    (by rw [g8, add_lit_zero]; exact aligned_add (aligned_add hF (k := 4) (by decide)) (by omega))
    (by rw [g8, add_lit_zero]; exact sC3)
  have hzg : upd g1 t0 (S + BitVec.ofNat 32 (0x3E + 8)) 0 = 0 := upd_zero _ _ _
  obtain ⟨em2, f9, f20, f8, fa0, fr2⟩ := selStep_run (M := memStore8 M (F + 0x37) (c.extractLsb' 0 8))
    (f := upd g1 t0 (S + BitVec.ofNat 32 (0x3E + 8))) hzg
  obtain ⟨n2, c2, u2⟩ := u1.callBlock hc1 us_at_3e us_at_42 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at S hS 0xCFEE (by decide)) (even_at S hS (0x3E + 8) (by decide)) hcs1 selStep selStep_end uss_at_14 okS
    (by rw [fr2 t0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), upd_t0])
  have u2' := u2.self
  rw [em2, g8, add_lit_zero, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide),
    upd_ne (by decide) (by decide), e2, e3, e4, selWord_eq _ _ c hcc] at u2'
  obtain ⟨g2, hg2⟩ : ∃ g2, (runBlock selStep (memStore8 M (F + 0x37) (c.extractLsb' 0 8),
      upd g1 t0 (S + BitVec.ofNat 32 (0x3E + 8)))).2 = g2 := ⟨_, rfl⟩
  rw [hg2] at f9 f20 f8 fa0 fr2
  have v2 : ∀ q, reg n2 q = g2 q := fun q => by rw [u2.regs, hg2]
  have hc2 := CodeIn.store32 (v := if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i))
    else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) hc1 sC2
  have ea0 : reg n2 a0 = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [v2, fa0, upd_ne (by decide) (by decide), fr1 _ (by decide) (by decide) (by decide), ra0, cnt12_dec i hi]
  have hb : branchTaken .bne (reg n2 a0) (reg n2 x0) = decide (i + 1 < 12) := by
    rw [ea0, u2'.zero]; exact cnt12_ne i hi
  have post : ∀ n3 : Machine, (∀ q, reg n3 q = reg n2 q) →
      reg n3 (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n3 a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
        q ≠ t0 → reg n3 q = reg n q := fun n3 h3 => by
    refine ⟨?_, ?_, ?_, by rw [h3, ea0], fun q q0 q2 q3 q4 q9 q20 q8 qt => ?_⟩
    · rw [h3, v2, f9, upd_ne (by decide) (by decide), fr1 _ (by decide) (by decide) (by decide), r9, ptr4]
    · rw [h3, v2, f20, upd_ne (by decide) (by decide), fr1 _ (by decide) (by decide) (by decide), r20, ptr4]
    · rw [h3, v2, f8, g8, ptr4]
    · rw [h3, v2, fr2 q q2 q3 q4 q9 q20 q8 q0]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; rw [upd_zero, hz]
      · rw [upd_ne h0 qt, fr1 q q2 q3 q4]
  by_cases hl : i + 1 < 12
  · obtain ⟨n3, d3, u3⟩ := u2'.taken hc2 0x30 us_at_46 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n3, c1.trans (c2.trans (.single d3)), by rw [ite_eq_left hl]; exact u3.self, post n3 u3.regs⟩
  · obtain ⟨n3, d3, u3⟩ := u2'.notTaken hc2 0x48 us_at_46 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n3, c1.trans (c2.trans (.single d3)), by rw [ite_eq_right hl]; exact u3.self, post n3 u3.regs⟩

theorem slot37 (F : Word) : F + 4 + BitVec.ofNat 32 0x33 = F + 0x37 := by rw [BitVec.add_assoc]; rfl

/-- What one limb of the loop does to memory, apart from the registers. -/
theorem sel_mem {M MB : Word → BitVec 8} {F ap bp c : Word} {v : BitVec 8} {i : Nat} (hi : i < 12) (hw : F.toNat + 0x50 ≤ 2 ^ 32)
    (sA : Sep (F + 4) 0x34 ap 48) (sB : Sep (F + 4) 0x34 bp 48)
    (hfr : ∀ x, Sep (F + 4) 0x34 x 1 → M x = MB x)
    (hwd : ∀ j, j < i → memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * j)) =
      if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) :
    (∀ x, Sep (F + 4) 0x34 x 1 → memStore32 (memStore8 M (F + 0x37) v) (F + 4 + BitVec.ofNat 32 (4 * i))
      (if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))) x =
        MB x) ∧
    ∀ j, j < i + 1 → memLoad32 (memStore32 (memStore8 M (F + 0x37) v) (F + 4 + BitVec.ofNat 32 (4 * i))
      (if c = 1 then memLoad32 M (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 M (ap + BitVec.ofNat 32 (4 * i))))
        (F + 4 + BitVec.ofNat 32 (4 * j)) =
      if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j)) := by
  have hF4 : (F + 4).toNat + 0x34 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; omega
  refine ⟨fun x hx => ?_, fun j hj => ?_⟩
  · have h8 : x ≠ F + 0x37 := fun e => by
      have := hx.point (i := 0x33) (j := 0) (by decide) (by decide)
      rw [slot37, add_ofNat_zero] at this; exact this e.symm
    rw [memStore32_get_sep (hx.sub (c := 4 * i) (l := 4) (by omega)), memStore8_ne h8, hfr x hx]
  · by_cases hji : j = i
    · subst hji
      rw [memLoad32_store32_same, load_frame hfr (sB.subR (by omega)), load_frame hfr (sA.subR (by omega))]
    · rw [memLoad32_store32_sep (sep_offsets (F + 4) (c := 4 * i) (n := 4) (d := 4 * j) (k := 4) (by omega)
          (by omega) (by omega)), memLoad32_store8_sep (by
          rw [← slot37]; exact sep_offsets (F + 4) (c := 0x33) (n := 1) (d := 4 * j) (k := 4) (.inr (by omega))
            (by omega) (by omega)), hwd j (by omega)]

theorem sel_lt {i m n : Nat} (h : i + m + 1 = n) : i < n := by omega

theorem sel_succ {i m n : Nat} (h : i + (m + 1) + 1 = n) : i + 1 + m + 1 = n := by omega

theorem sel_lt1 {i m n : Nat} (h : i + (m + 1) + 1 = n) : i + 1 < n := by omega

/-- **The select loop**, from limb `i` to its end at 0x48: the buffer at
`F + 4` gets limbs `i..11` of `b` or `a`. -/
theorem sel_loop {S F ap bp c : Word} {MB : Word → BitVec 8} (hS : S.toNat % 2 = 0) (hcc : c = 0 ∨ c = 1)
    (hap : ap.toNat % 4 = 0) (hbp : bp.toNat % 4 = 0) (hF : F.toNat % 4 = 0) (hw : F.toNat + 0x50 ≤ 2 ^ 32)
    (sA : Sep (F + 4) 0x34 ap 48) (sB : Sep (F + 4) 0x34 bp 48)
    (sC : Sep (F + 4) 0x34 S uintSelect12Code.length)
    (sD : Sep (F + 4) 0x34 (S + 0xCFEE) uintSelect12StepCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M S n 0x30 (reg n) → CodeIn M S uintSelect12Code → CodeIn M (S + 0xCFEE) uintSelect12StepCode →
      (∀ x, Sep (F + 4) 0x34 x 1 → M x = MB x) →
      (∀ j, j < i → memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * j)) =
        if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) →
      reg n sp = F → reg n (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * i) →
      reg n (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * i) →
      reg n a0 = BitVec.ofNat 32 (12 - i) → reg n (19 : Fin 32) = c →
      ∃ n' M', Steps n n' ∧ St M' S n' 0x48 (reg n') ∧ CodeIn M' S uintSelect12Code ∧
        CodeIn M' (S + 0xCFEE) uintSelect12StepCode ∧ (∀ x, Sep (F + 4) 0x34 x 1 → M' x = MB x) ∧
        (∀ j, j < 12 → memLoad32 M' (F + 4 + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) ∧
        ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
          q ≠ t0 → reg n' q = reg n q := by
  have hF4 : (F + 4).toNat + 0x34 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; omega
  have hb37 : ∀ {b : Word} {len : Nat}, Sep (F + 4) 0x34 b len → Sep (F + 0x37) 1 b len := fun h => by
    rw [← slot37]; exact h.sub (by decide)
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M S n 0x30 (reg n) → CodeIn M S uintSelect12Code → CodeIn M (S + 0xCFEE) uintSelect12StepCode →
      (∀ x, Sep (F + 4) 0x34 x 1 → M x = MB x) →
      (∀ j, j < i → memLoad32 M (F + 4 + BitVec.ofNat 32 (4 * j)) =
        if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) →
      reg n sp = F → reg n (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * i) →
      reg n (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * i) → reg n (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * i) →
      reg n a0 = BitVec.ofNat 32 (12 - i) → reg n (19 : Fin 32) = c →
      ∃ n' M', Steps n n' ∧ St M' S n' (if i + 1 < 12 then 0x30 else 0x48) (reg n') ∧
        CodeIn M' S uintSelect12Code ∧ CodeIn M' (S + 0xCFEE) uintSelect12StepCode ∧
        (∀ x, Sep (F + 4) 0x34 x 1 → M' x = MB x) ∧
        (∀ j, j < i + 1 → memLoad32 M' (F + 4 + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then memLoad32 MB (bp + BitVec.ofNat 32 (4 * j)) else memLoad32 MB (ap + BitVec.ofNat 32 (4 * j))) ∧
        reg n' (9 : Fin 32) = ap + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (20 : Fin 32) = bp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = F + 4 + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' a0 = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
          q ≠ t0 → reg n' q = reg n q := by
    intro i hi M n s hc hcs hfr hwd rsp r9 r20 r8 ra0 r19
    obtain ⟨n1, c1, u1, e9, e20, e8, ea0, fr⟩ := sel_iter (i := i) s hc hcs hS hi hcc hap hbp hF
      (hb37 sB |>.subR (by omega)) (hb37 sC) (sC.sub (by omega)) (sD.sub (by omega)) (hb37 sD)
      rsp r9 r20 r8 ra0 r19
    obtain ⟨m1, m2⟩ := sel_mem (v := c.extractLsb' 0 8) hi hw sA sB hfr hwd
    exact ⟨n1, _, c1, u1, CodeIn.store32 (CodeIn.store8 hc (hb37 sC)) (sC.sub (by omega)),
      CodeIn.store32 (CodeIn.store8 hcs (hb37 sD)) (sD.sub (by omega)), m1, m2, e9, e20, e8, ea0, fr⟩
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hcs hfr hwd rsp r9 r20 r8 ra0 r19
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hcs1, hf1, hw1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hcs hfr hwd rsp r9 r20 r8 ra0 r19
    exact ⟨n1, M1, c1, u1, hc1, hcs1, hf1, hw1, fr⟩
  | succ m ih =>
    intro i hi M n s hc hcs hfr hwd rsp r9 r20 r8 ra0 r19
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hcs1, hf1, hw1, e9, e20, e8, ea0, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hcs hfr hwd rsp r9 r20 r8 ra0 r19
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hcs', hf', hw', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hcs1 hf1 hw1
      (by rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rsp])
      e9 e20 e8 ea0
      (by rw [fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19])
    exact ⟨n', M', c1.trans c', u', hc', hcs', hf', hw', fun q q0 q2 q3 q4 q9 q20 q8 qt => by
      rw [fr' q q0 q2 q3 q4 q9 q20 q8 qt, fr q q0 q2 q3 q4 q9 q20 q8 qt]⟩

/-- A call to `memset` at `B` that zeroes `4 w` bytes at an aligned `dst`. -/
theorem St.memsetW {P B : Word} {code : List Nat} {Mx : Word → BitVec 8} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} {imm o dst : Word} {w : Nat} (hB : B.toNat % 2 = 0) (s : St Mx P m off f)
    (hc : CodeIn Mx P code) (hms : CodeIn Mx B memsetCode)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = B) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hw : 4 ≤ w) (hwd : dst.toNat + 4 * w < 2 ^ 32)
    (hmask : BitVec.ofNat 32 (4 * w) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * w))
    (hdst : dst.toNat % 4 = 0) (hsep : Sep dst (4 * w) B memsetCode.length)
    (ha0 : f a0 = dst) (ha1 : f a1 = 0) (ha2 : f a2 = BitVec.ofNat 32 (4 * w)) :
    ∃ m', Steps m m' ∧ St (fillWords Mx dst 0 w) P m' (off + 8) (reg m') ∧ reg m' a0 = dst ∧
      ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra → reg m' r = f r := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb hB
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, mem2, a02, fr2⟩ := memset_aligned m1 B (P + BitVec.ofNat 32 (off + 8)) dst 0 w
    (fun i hi => by rw [mem1]; exact hms i hi) hB pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) hw hwd hmask hdst hsep
  rw [mem1, fillWord_zero] at mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], mem2, fun _ => rfl⟩, a02, fun r q2 q3 q4 q5 q6 q7 => ?_⟩
  rw [fr2 r q2 q3 q4 q5 q6, r1 r q7]

/-- A call to `memcpy`'s stub at `B` that copies `4 w` bytes between aligned
buffers. -/
theorem St.memcpyW {P B : Word} {code : List Nat} {Mx : Word → BitVec 8} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} {imm o dst src : Word} {w : Nat} (hB : B.toNat % 2 = 0) (s : St Mx P m off f)
    (hc : CodeIn Mx P code) (hst : CodeIn Mx B memcpyStubCode) (hbd : CodeIn Mx (B + 8) memcpyBodyCode)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = B) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hw : 4 ≤ w) (hwd : dst.toNat + 4 * w < 2 ^ 32)
    (hmask : BitVec.ofNat 32 (4 * w) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * w))
    (hdst : dst.toNat % 4 = 0) (hsrc : src.toNat % 4 = 0) (hds : Sep dst (4 * w) src (4 * w))
    (hsep : Sep dst (4 * w) (B + 8) memcpyBodyCode.length)
    (ha0 : f a0 = dst) (ha1 : f a1 = src) (ha2 : f a2 = BitVec.ofNat 32 (4 * w)) :
    ∃ m', Steps m m' ∧ St (copyWords Mx dst src w) P m' (off + 8) (reg m') ∧ reg m' a0 = dst ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 → r ≠ ra →
        reg m' r = f r := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb hB
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, mem2, a02, fr2⟩ := memcpy_aligned m1 B (P + BitVec.ofNat 32 (off + 8)) dst src w
    (fun i hi => by rw [mem1]; exact hst i hi) (fun i hi => by rw [mem1]; exact hbd i hi) hB pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) hw hwd hmask hdst hsrc hds hsep
  rw [mem1] at mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], mem2, fun _ => rfl⟩, a02, fun r q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 => ?_⟩
  rw [fr2 r q1 q2 q3 q4 q5 q6 q7 q8 q9, r1 r q10]

set_option maxRecDepth 20000 in
theorem selEpi_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock selEpi (M, f)).1 = M ∧
    (runBlock selEpi (M, f)).2 ra = memLoad32 M (f sp + 0x4C) ∧
    (runBlock selEpi (M, f)).2 (8 : Fin 32) = memLoad32 M (f sp + 0x48) ∧
    (runBlock selEpi (M, f)).2 (9 : Fin 32) = memLoad32 M (f sp + 0x44) ∧
    (runBlock selEpi (M, f)).2 (18 : Fin 32) = memLoad32 M (f sp + 0x40) ∧
    (runBlock selEpi (M, f)).2 (19 : Fin 32) = memLoad32 M (f sp + 0x3C) ∧
    (runBlock selEpi (M, f)).2 (20 : Fin 32) = memLoad32 M (f sp + 0x38) ∧
    (runBlock selEpi (M, f)).2 sp = f sp + 0x50 ∧
    ∀ q, proKeep q = true → q ≠ ra → (runBlock selEpi (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, selEpi]
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

theorem selEpi_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hF : (f sp).toNat % 4 = 0) : BlockOk base len selEpi (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, selEpi, upd, ↓reduceIte, and_true]
  exact ⟨aligned_add hF (k := 0x4C) (by decide), aligned_add hF (k := 0x48) (by decide),
    aligned_add hF (k := 0x44) (by decide), aligned_add hF (k := 0x40) (by decide),
    aligned_add hF (k := 0x3C) (by decide), aligned_add hF (k := 0x38) (by decide)⟩

theorem selPost_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock selPost (M, f)).1 = M ∧ (runBlock selPost (M, f)).2 a1 = f sp + 4 ∧
    (runBlock selPost (M, f)).2 a2 = 0x30 ∧ (runBlock selPost (M, f)).2 a0 = f (18 : Fin 32) ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → (runBlock selPost (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, selPost]
  refine ⟨trivial, ?_, ?_, ?_, fun q q0 q1 q2 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2]

/-- The registers `Uint<12>::select` may change. -/
def selKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 10, 11, 12, 13, 14, 15, 16, 17]

/-- Where `Uint<12>::select` runs: its code and its callees' at their
offsets, its 0x50-byte frame below `sp0`, and the result and operands,
aligned and apart from what each must not touch. -/
structure SelEnv (M : Word → BitVec 8) (S sp0 out ap bp : Word) : Prop where
  hS : S.toNat % 2 = 0
  code : CodeIn M S uintSelect12Code
  mset : CodeIn M (S + 0xD196) memsetCode
  stub : CodeIn M (S + 0xD1FE) memcpyStubCode
  body : CodeIn M (S + 0xD206) memcpyBodyCode
  step : CodeIn M (S + 0xCFEE) uintSelect12StepCode
  hsp : sp0.toNat % 4 = 0
  h50 : 0x50 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sFC : Sep (sp0 + 0xFFFFFFB0) 0x50 S uintSelect12Code.length
  sFM : Sep (sp0 + 0xFFFFFFB0) 0x50 (S + 0xD196) memsetCode.length
  sFU : Sep (sp0 + 0xFFFFFFB0) 0x50 (S + 0xD1FE) memcpyStubCode.length
  sFB : Sep (sp0 + 0xFFFFFFB0) 0x50 (S + 0xD206) memcpyBodyCode.length
  sFS : Sep (sp0 + 0xFFFFFFB0) 0x50 (S + 0xCFEE) uintSelect12StepCode.length
  sOF : Sep out 48 (sp0 + 0xFFFFFFB0) 0x50
  sOC : Sep out 48 S uintSelect12Code.length
  sOB : Sep out 48 (S + 0xD206) memcpyBodyCode.length
  sAF : Sep ap 48 (sp0 + 0xFFFFFFB0) 0x50
  sBF : Sep bp 48 (sp0 + 0xFFFFFFB0) 0x50

theorem frame50 (sp0 : Word) (h : 0x50 ≤ sp0.toNat) : (sp0 + 0xFFFFFFB0).toNat + 0x50 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFFB0 : Word).toNat = 0xFFFFFFB0 := rfl
  rw [this]; have := sp0.isLt; omega

/-- **The compiled `Uint<12>::select`.** It writes `b`'s 12 limbs to `out`
when `choice` is 1 and `a`'s when it is 0, returns with `sp` and the
callee-saved registers restored, and writes only `out` and its frame. -/
theorem uintSelect12_correct (m : Machine) {S out ap bp c retAddr : Word}
    (E : SelEnv m.mem S (reg m sp) out ap bp) (hpc : m.pc = S) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) (ha3 : reg m a3 = c) (hcc : c = 0 ∨ c = 1) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ i, i < 12 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 m.mem (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 m.mem (ap + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (reg m sp + 0xFFFFFFB0) 0x50 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x) ∧
      ∀ r, selKeep r = true → reg m' r = reg m r := by
  obtain ⟨F, hFd⟩ : ∃ F, reg m sp + 0xFFFFFFB0 = F := ⟨_, rfl⟩
  have sFC := E.sFC; have sFM := E.sFM; have sFU := E.sFU; have sFB := E.sFB; have sFS := E.sFS
  have sOF := E.sOF; have sAF := E.sAF; have sBF := E.sBF
  rw [hFd] at sFC sFM sFU sFB sFS sOF sAF sBF
  rw [hFd]
  have hFa : F.toNat % 4 = 0 := by rw [← hFd]; exact aligned_add E.hsp (k := 0xFFFFFFB0) (by decide)
  have hFw : F.toNat + 0x50 = (reg m sp).toNat := by rw [← hFd]; exact frame50 _ E.h50
  have hF4a : (F + 4).toNat % 4 = 0 := aligned_add hFa (k := 4) (by decide)
  have hF4w : (F + 4).toNat + 48 < 2 ^ 32 := by
    rw [BitVec.toNat_add]; have : (4 : Word).toNat = 4 := rfl; rw [this]; have := (reg m sp).isLt; omega
  have hsub : ∀ x, Sep F 0x50 x 1 → Sep (F + 4) 0x34 x 1 := fun x hx => hx.sub (c := 4) (l := 0x34) (by decide)
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep F 0x50 b code.length → (∀ x, Sep F 0x50 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem S m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- prologue
  have ok0 := selPro_ok (M := m.mem) (f := reg m) (base := S) (len := uintSelect12Code.length)
    (by rw [hFd]; exact hFa) (by rw [hFd]; exact sFC)
  obtain ⟨n1, c1, u1⟩ := St.block selPro s0 E.code selPro_end ok0
  obtain ⟨em1, p_sp, p19, p20, p9, p18, pa0, pa2, pa1, p8, pk⟩ := selPro_run (M := m.mem) (f := reg m) hz
  have u1' := u1.self
  rw [em1, hFd] at u1'
  have g1 : ∀ q, reg n1 q = (runBlock selPro (m.mem, reg m)).2 q := u1.regs
  have I1 : ∀ x, Sep F 0x50 x 1 → saveMem m.mem F (reg m) selPs x = m.mem x :=
    fun x hx => saveMem_outside selPs fun q hq => by
      simp only [selPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hx.sub (by decide)
  -- memset of the buffer at F + 4
  obtain ⟨n2, c2, u2, a02, fr2⟩ := u1'.memsetW (B := S + 0xD196) (w := 12) (dst := F + 4)
    (even_at S E.hS 0xD196 (by decide)) (codeS E.code sFC I1) (codeS E.mset sFM I1) us_at_20 us_at_24
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at S E.hS (0x20 + 8) (by decide)) (by decide) hF4w
    (by decide) hF4a (sFM.sub (c := 4) (l := 48) (by decide)) (by rw [g1, pa0, hFd]) (by rw [g1, pa1])
    (by rw [g1, pa2]; rfl)
  have I2 : ∀ x, Sep F 0x50 x 1 → fillWords (saveMem m.mem F (reg m) selPs) (F + 4) 0 12 x = m.mem x :=
    fun x hx => by
      rw [fillWords_outside (dst := F + 4) 12 (hx.sub (c := 4) (l := 48) (by decide)), I1 x hx]
  have hc2 := codeS E.code sFC I2
  have k2 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n2 q = reg n1 q := fr2
  obtain ⟨n3, d3, u3⟩ := u2.aluImm hc2 us_at_28 (off' := 0x2A) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc2 us_at_2a (off' := 0x2E) (by decide)
  have z2 : reg n2 x0 = 0 := u2.zero
  have g4 : ∀ q, q ≠ a0 → q ≠ a1 → reg n4 q = reg n2 q := fun q q0 q1 => by
    rw [u4.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, z2]
    · simp [upd, h0, q0, q1]
  have v4 : reg n4 a0 = BitVec.ofNat 32 (12 - 0) := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte, z2]
  obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc2 0x30 us_at_2e (by decide) (by rw [v4, u4.self.zero]; decide)
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
  obtain ⟨n6, M6, c6, u6, hc6, hcs6, hf6, hw6, fr6⟩ :=
    sel_loop (MB := fillWords (saveMem m.mem F (reg m) selPs) (F + 4) 0 12) E.hS hcc E.hap E.hbp hFa (by omega)
      (sAF.symm.sub (c := 4) (l := 0x34) (by decide)) (sBF.symm.sub (c := 4) (l := 0x34) (by decide))
      (sFC.sub (c := 4) (l := 0x34) (by decide)) (sFS.sub (c := 4) (l := 0x34) (by decide))
      11 0 (by decide) u5.self hc2 (codeS E.step sFS I2) (fun _ _ => rfl) (fun j hj => absurd hj (Nat.not_lt_zero j))
      sp5 (by rw [kp _ (by decide), g1, p9, ha1, Nat.mul_zero, add_ofNat_zero])
      (by rw [kp _ (by decide), g1, p20, ha2, Nat.mul_zero, add_ofNat_zero])
      (by rw [kp _ (by decide), g1, p8, hFd, Nat.mul_zero, add_ofNat_zero])
      (by rw [r5, v4]) (by rw [kp _ (by decide), g1, p19, ha3])
  have hM6 : ∀ x, Sep F 0x50 x 1 → M6 x = m.mem x := fun x hx => by rw [hf6 x (hsub x hx), I2 x hx]
  -- copy the buffer out
  have okP : BlockOk S uintSelect12Code.length selPost (M6, reg n6) := by
    simp only [BlockOk, BInstr.ok, selPost]; exact ⟨trivial, trivial, trivial, trivial⟩
  obtain ⟨n7, c7, u7⟩ := St.block selPost u6 hc6 selPost_end okP
  obtain ⟨em7, b1, b2, b0, bk⟩ := selPost_run (M := M6) (f := reg n6) u6.zero
  rw [em7] at u7
  have k6 : ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (8 : Fin 32) →
      q ≠ t0 → reg n6 q = reg n5 q := fr6
  have sp6 : reg n6 sp = F := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp5]
  have e18 : reg n6 (18 : Fin 32) = out := by
    rw [k6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      kp _ (by decide), g1, p18, ha0]
  have e8 : S + 0xD1FE + 8 = S + 0xD206 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n8, c8, u8, a08, fr8⟩ := u7.memcpyW (B := S + 0xD1FE) (w := 12) (dst := out) (src := F + 4)
    (even_at S E.hS 0xD1FE (by decide)) hc6 (codeS E.stub sFU hM6) (by rw [e8]; exact codeS E.body sFB hM6)
    us_at_50 us_at_54 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at S E.hS (0x50 + 8) (by decide))
    (by decide) E.hwo (by decide) E.hout hF4a (sOF.subR (c := 4) (l := 48) (by decide)) (by rw [e8]; exact E.sOB)
    (by rw [b0, e18]) (by rw [b1, sp6]) (by rw [b2]; rfl)
  have hM8 : ∀ x, Sep F 0x50 x 1 → Sep out 48 x 1 → copyWords M6 out (F + 4) 12 x = m.mem x := fun x hx ho => by
    rw [copyWords_outside 12 ho, hM6 x hx]
  have hc8 : CodeIn (copyWords M6 out (F + 4) 12) S uintSelect12Code := fun i hi => by
    rw [hM8 _ (sFC.subR (c := i) (l := 1) (by omega)) (E.sOC.subR (c := i) (l := 1) (by omega))]; exact E.code i hi
  have k8 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ ra →
      reg n8 q = (runBlock selPost (M6, reg n6)).2 q := fr8
  have sp8 : reg n8 sp = F := by
    rw [k8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), bk _ (by decide) (by decide) (by decide), sp6]
  -- the epilogue
  obtain ⟨n9, c9, u9⟩ := St.block selEpi u8 hc8 selEpi_end (selEpi_ok (by rw [sp8]; exact hFa))
  obtain ⟨em9, l1, l8, l9, l18, l19, l20, lsp, lk⟩ := selEpi_run (M := copyWords M6 out (F + 4) 12) (f := reg n8)
    u8.zero
  rw [em9] at u9
  have slot : ∀ (r : Fin 32) (o : Word), (r, o) ∈ selPs → 0x38 ≤ o.toNat → o.toNat + 4 ≤ 0x50 →
      (∀ p ∈ selPs, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
        p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32)) →
      memLoad32 (copyWords M6 out (F + 4) 12) (reg n8 sp + o) = reg m r := fun r o hm h1 h2 hp => by
    have hFo : F + BitVec.ofNat 32 o.toNat = F + o := by rw [ofNat_toNat_self]
    rw [sp8, ← hFo, copyWords_load_sep (sOF.subR (c := o.toNat) (l := 4) (by omega)),
      load_frame hf6 (sep_offsets F (c := 4) (n := 0x34) (d := o.toNat) (k := 4) (.inl (by omega)) (by omega)
        (by omega)),
      fillWords_load_sep (dst := F + 4) (sep_offsets F (c := 4) (n := 48) (d := o.toNat) (k := 4) (.inl (by omega))
        (by omega) (by omega)), hFo]
    exact saveMem_slot selPs _ hm hp
  have hz9 : reg n9 x0 = 0 := u9.self.zero
  obtain ⟨m', e10, pc10, mem10, regs10⟩ := u9.jalr hc8 us_at_66
  have hra' : (runBlock selEpi (copyWords M6 out (F + 4) 12, reg n8)).2 ra = retAddr := by
    rw [l1, slot ra 0x4C (by decide) (by decide) (by decide) (by decide), hra]
  refine ⟨m', c1.trans (c2.trans (.cons d3 (.cons d4 (.cons d5 (c6.trans (c7.trans (c8.trans (c9.trans
    (.single e10))))))))), ?_, ?_, fun i hi => ?_, fun x hx ho => ?_, fun r hr => ?_⟩
  · rw [pc10, hra', add_lit_zero, hret]
  · rw [regs10, lsp, sp8, ← hFd, BitVec.add_assoc]; exact BitVec.add_zero _
  · have hwo := E.hwo
    rw [mem10, copyWords_load 12 i hi (by omega), hw6 i hi, load_frame I2 (sBF.symm.subR (by omega)),
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
    · rw [l8, slot 8 0x48 (by decide) (by decide) (by decide) (by decide)]
    · rw [l9, slot 9 0x44 (by decide) (by decide) (by decide) (by decide)]
    · rw [l18, slot 18 0x40 (by decide) (by decide) (by decide) (by decide)]
    · rw [l19, slot 19 0x3C (by decide) (by decide) (by decide) (by decide)]
    · rw [l20, slot 20 0x38 (by decide) (by decide) (by decide) (by decide)]
    · rw [lk r hp hnr, k8 r n1' n2' n3' n4' n5' n6' n7' nt0 nt1 hnr, bk r n0 n1' n2',
        k6 r n0 n2' n3' n4' n9' n20' n8' nt0, k1 r hp hnl]

end C3.RV32
