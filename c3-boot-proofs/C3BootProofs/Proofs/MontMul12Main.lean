import C3BootProofs.Proofs.UintSelect12

/-!
# P-384's Montgomery multiplication, end to end

`mul_montgomery_form::<12>` runs the loop of `MontMul12` on an accumulator
it zeroes on its stack, then subtracts the modulus once if the sum is at
least the modulus: `borrowing_sub` limb by limb into a second buffer, and
`Uint<12>::select` between the two.
-/

namespace C3.RV32

open C3.Image

/-- What `mul_montgomery_form::<12>`'s save helper stores and its restore
helper loads. -/
abbrev mmPs : List (Fin 32 × Word) :=
  [(ra, 0x9C), ((8 : Fin 32), 0x98), ((9 : Fin 32), 0x94), ((18 : Fin 32), 0x90), ((19 : Fin 32), 0x8C),
   ((20 : Fin 32), 0x88), ((21 : Fin 32), 0x84), ((22 : Fin 32), 0x80), ((23 : Fin 32), 0x7C),
   ((24 : Fin 32), 0x78), ((25 : Fin 32), 0x74), ((26 : Fin 32), 0x70)]

theorem mmSave_shape : SaveAt mulMont12SaveCode 0 mmPs := by simp only [SaveAt]; decide

theorem mmRestore_shape : RestoreAt mulMont12RestoreCode 0 mmPs := by simp only [RestoreAt]; decide

/-- The outlined helper `OUTLINED_FUNCTION_68`: zero the top carry and the
pass count, load the low limbs of the second operand and the modulus, and
point at their next limbs and the accumulator's. -/
def mmSetup : List BInstr :=
  [.aluImm .add (22 : Fin 32) x0 0, .aluImm .add (28 : Fin 32) x0 0, .aluImm .add (29 : Fin 32) x0 0,
   .lw (6 : Fin 32) (21 : Fin 32) 0, .lw (7 : Fin 32) (23 : Fin 32) 0, .aluImm .add (21 : Fin 32) (21 : Fin 32) 4,
   .aluImm .add a6 sp 0x10, .aluImm .add (17 : Fin 32) (23 : Fin 32) 4]

section
set_option maxRecDepth 20000
theorem mmSetup_end : blockEnd mulMont12SetupCode 0 mmSetup = some 0x18 := by decide
theorem mst_at_18 : fetchRel mulMont12SetupCode 0x18 = some (.jalr x0 (5 : Fin 32) 0x0, 2) := by decide
end

/-- The registers the setup helper leaves alone. -/
def setupKeep (q : Fin 32) : Bool := q.val ∉ [6, 7, 16, 17, 21, 22, 28, 29]

set_option maxRecDepth 20000 in
theorem mmSetup_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmSetup (M, f)).1 = M ∧
    (runBlock mmSetup (M, f)).2 (22 : Fin 32) = 0 ∧ (runBlock mmSetup (M, f)).2 (28 : Fin 32) = 0 ∧
    (runBlock mmSetup (M, f)).2 (29 : Fin 32) = BitVec.ofNat 32 0 ∧
    (runBlock mmSetup (M, f)).2 (6 : Fin 32) = memLoad32 M (f (21 : Fin 32) + 0) ∧
    (runBlock mmSetup (M, f)).2 (7 : Fin 32) = memLoad32 M (f (23 : Fin 32) + 0) ∧
    (runBlock mmSetup (M, f)).2 (21 : Fin 32) = f (21 : Fin 32) + 4 ∧
    (runBlock mmSetup (M, f)).2 a6 = f sp + 0x10 ∧
    (runBlock mmSetup (M, f)).2 (17 : Fin 32) = f (23 : Fin 32) + 4 ∧
    ∀ q, setupKeep q = true → (runBlock mmSetup (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmSetup]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := 6) hq rfl, pkeep_ne (r := 7) hq rfl, pkeep_ne (r := a6) hq rfl,
        pkeep_ne (r := 17) hq rfl, pkeep_ne (r := 21) hq rfl, pkeep_ne (r := 22) hq rfl, pkeep_ne (r := 28) hq rfl,
        pkeep_ne (r := 29) hq rfl]

theorem mmSetup_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h21 : (f (21 : Fin 32) + 0).toNat % 4 = 0) (h23 : (f (23 : Fin 32) + 0).toNat % 4 = 0) :
    BlockOk base len mmSetup (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmSetup, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h21, h23⟩

theorem mb_le1 (b : Word) : maskBit b ≤ 1 := by unfold maskBit; split <;> decide

/-- **`borrowing_sub` as a limb of a subtraction**: the difference and the
borrow out, with the borrow in, add up. -/
theorem bsub_val (l r b : Word) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    (bsubD l r b).toNat + r.toNat + maskBit b = l.toNat + 2 ^ 32 * maskBit (bsubB l r (bsubD l r b)) ∧
    (bsubB l r (bsubD l r b) = 0 ∨ bsubB l r (bsubD l r b) = 0xFFFFFFFF) := by
  rw [bsubB_eq l r b hb]
  have hd := bsubD_toNat l r b hb
  have hm := mb_le1 b
  have hl := l.isLt; have hr := r.isLt
  by_cases h : l.toNat < r.toNat + maskBit b
  · rw [ite_eq_left h, show maskBit 0xFFFFFFFF = 1 from rfl]
    exact ⟨by omega, .inr rfl⟩
  · rw [ite_eq_right h, show maskBit 0 = 0 from rfl]
    exact ⟨by omega, .inl rfl⟩

/-- A call to `borrowing_sub` at `B` with `sp` at `F`. -/
theorem St.bsubCall {Mx : Word → BitVec 8} {P B F : Word} {code : List Nat} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} {imm o : Word} (s : St Mx P m off f) (hc : CodeIn Mx P code)
    (hb : CodeIn Mx B borrowingSubCode) (hB : B.toNat % 2 = 0)
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hcb : P + BitVec.ofNat 32 off + imm + o = B) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = F) (hF : F.toNat % 4 = 0) (hsep : Sep (F + 0xFFFFFFFC) 4 B borrowingSubCode.length) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧
      reg m' a0 = bsubD (f a0) (f a1) (f a2) ∧ reg m' a1 = bsubB (f a0) (f a1) (bsubD (f a0) (f a1) (f a2)) ∧
      reg m' sp = F ∧ (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg m' q = f q) ∧
      ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → m'.mem x = Mx x := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hcb hB
  have hz := s.zero
  have r1 : ∀ q, q ≠ ra → reg m1 q = f q := PEnv.reg1 regs1 hz
  obtain ⟨m2, c2, pc2, a02, a12, sp2, fr2, mem2⟩ := borrowingSub_correct m1 B
    (P + BitVec.ofNat 32 (off + 8)) (f a0) (f a1) (f a2) (by show CodeIn m1.mem _ _; rw [mem1]; exact hb) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hl) (by rw [r1 sp (by decide), hsp]; exact hF) (by rw [r1 sp (by decide), hsp]; exact hsep)
  rw [r1 sp (by decide), hsp] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, a12, sp2, fun q q0 q1 q2 q3 q4 qr => ?_,
    fun x hx => by rw [mem2 x hx, mem1]⟩
  rw [fr2 q q0 q1 q2 q3 q4, r1 q qr]

/-- The end of a subtraction round, from 0x10C: keep the borrow, store the
difference, and advance the pointers and the count. -/
def subTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4, .sw (19 : Fin 32) a0 0,
   .aluImm .add (23 : Fin 32) (23 : Fin 32) 4, .aluImm .add (19 : Fin 32) (19 : Fin 32) 4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem subTail_end : blockEnd mulMont12Code 0x10C subTail = some 0x11A := by decide
end

set_option maxRecDepth 20000 in
theorem subTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock subTail (M, f)).1 = memStore32 M (f (19 : Fin 32) + 0) (f a0) ∧
    (runBlock subTail (M, f)).2 a2 = f a1 ∧
    (runBlock subTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock subTail (M, f)).2 (23 : Fin 32) = f (23 : Fin 32) + 4 ∧
    (runBlock subTail (M, f)).2 (19 : Fin 32) = f (19 : Fin 32) + 4 ∧
    (runBlock subTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) →
      (runBlock subTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, subTail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 q9 q23 q19 q8 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q9, q23, q19, q8]

theorem subTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (19 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (19 : Fin 32) + 0) 4 base len) :
    BlockOk base len subTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, subTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

end C3.RV32
