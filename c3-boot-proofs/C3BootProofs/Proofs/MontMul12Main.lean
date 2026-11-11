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

/-- `borrowing_sub`'s offset from `mul_montgomery_form::<12>`. -/
abbrev mmBsub (P : Word) : Word := P + 0xFFFEFF8A

/-- **One round of the final subtraction**, from 0xFE: subtract limb `i` of
the modulus and the borrow from limb `i` of the accumulator, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem sub_iter {M : Word → BitVec 8} {P F acc np D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0xFE (reg n)) (hc : CodeIn M P mulMont12Code) (hb : CodeIn M (mmBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 12) (hF : F.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (mmBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P mulMont12Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P mulMont12Code.length)
    (rsp : reg n sp = F) (r9 : reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i))
    (r23 : reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i)) (r19 : reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (r8 : reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0xFE else 0x11C) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc mm_at_fe (off' := 0x100) (by decide)
    (by rw [r9, add_lit_zero]; exact aligned_add hacc (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc mm_at_100 (off' := 0x104) (by decide)
    (by rw [upd_ne (by decide) (by decide), r23, add_lit_zero]; exact aligned_add hnp (by omega))
  rw [r9, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (23 : Fin 32) + 0)) a0 =
      memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (23 : Fin 32) + 0)) a1 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [r23, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFEFF8A (by decide))
    mm_at_104 mm_at_108 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x104 + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P mulMont12Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have e19 : reg n3 (19 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block subTail u3 hc3 subTail_end
    (subTail_ok (by rw [e19]; exact aligned_add hD (by omega)) (by rw [e19]; exact sDC))
  obtain ⟨em4, t2, t9, t23, t19, t8, tk⟩ := subTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, e19, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock subTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have e8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [g4, t8, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, cnt12_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (8 : Fin 32)) (reg n4 x0) = decide (i + 1 < 12) := by
    rw [e8, u4'.zero]; exact cnt12_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, e8], fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => ?_⟩
    · rw [h5, g4, t9, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, ptr4]
    · rw [h5, g4, t23, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r23, ptr4]
    · rw [h5, g4, t19, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, ptr4]
    · rw [h5, g4, tk q q2 q9 q23 q19 q8, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0xFE mm_at_11a (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x11C mm_at_11a (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

theorem sub_arith {A N Dv P a nn d mb mb' B : Nat} (h1 : A + P * mb = N + Dv) (h2 : d + nn + mb = a + B * mb') :
    A + a * P + P * B * mb' = N + nn * P + (Dv + d * P) := by
  have e : (d + nn + mb) * P = (a + B * mb') * P := by rw [h2]
  simp only [Nat.add_mul] at e
  simp only [Nat.mul_comm, Nat.mul_left_comm] at h1 e ⊢
  omega

theorem load_frame2 {M M0 : Word → BitVec 8} {u v b : Word} {n k : Nat}
    (hf : ∀ x, Sep u n x 1 → Sep v k x 1 → M x = M0 x) (h1 : Sep u n b 4) (h2 : Sep v k b 4) :
    memLoad32 M b = memLoad32 M0 b :=
  memLoad32_congr fun q hq => hf _ (h1.subR (c := q) (l := 1) (by omega)) (h2.subR (c := q) (l := 1) (by omega))

set_option exponentiation.threshold 400 in
/-- **The final subtraction**, from round `i` to its end at 0x11C: the
buffer at `D` gets the accumulator minus the modulus, and `a2` the borrow
out as a mask. -/
theorem sub_loop {P F acc np D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hacc : acc.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 48 ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 acc 48) (sFN : Sep (F + 0xFFFFFFFC) 4 np 48) (sFD : Sep (F + 0xFFFFFFFC) 4 D 48)
    (sDA : Sep D 48 acc 48) (sDN : Sep D 48 np 48)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (mmBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P mulMont12Code.length)
    (sDB : Sep D 48 (mmBsub P) borrowingSubCode.length) (sDC : Sep D 48 P mulMont12Code.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0xFE (reg n) → CodeIn M P mulMont12Code → CodeIn M (mmBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x11C (reg n') ∧ CodeIn M' P mulMont12Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc 12 + 2 ^ (32 * 12) * maskBit (reg n' a2) = accV M0 np 12 + accV M' D 12 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) →
          q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0xFE (reg n) → CodeIn M P mulMont12Code → CodeIn M (mmBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0xFE else 0x11C) (reg n') ∧
        CodeIn M' P mulMont12Code ∧ CodeIn M' (mmBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 np (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) →
          q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, e9, e23, e19, e8, fr⟩ := sub_iter (i := i) s hc hb hP hi hF hacc hnp hD
      sFB sFC (sDC.sub (by omega)) rsp r9 r23 r19 r8 ra2
    have eA : memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFA.subR (by omega)) (sDA.subR (by omega))
    have eN : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (mmBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P mulMont12Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, e9, e23, e19, e8, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e9, e23, e19, e8, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 e9 e23 e19 e8 rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q9 q23 q19 q8, fr q q0 q1 q2 q3 q4 qr q9 q23 q19 q8]⟩

/-- From 0x11C: spill the top carry, and choose the accumulator when the
top carry is zero and the subtraction borrowed, through a byte of the
frame; then set up the call to `borrowing_sub` whose result goes unused. -/
def mmChoice : List BInstr :=
  [.sw sp (22 : Fin 32) 0x6C, .aluImm .add a0 sp 0x6C, .lw a0 sp 0x6C, .aluImm .sltu (9 : Fin 32) a0 1,
   .alu .and (9 : Fin 32) (9 : Fin 32) a2, .sb sp (9 : Fin 32) 0x6C, .aluImm .add a0 sp 0x6C, .lbu a0 sp 0x6C,
   .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a2 a2 a0, .alu .add a0 x0 (22 : Fin 32), .aluImm .add a1 x0 0]

/-- From 0x142: the arguments of `Uint<12>::select`. -/
def mmSelArgs : List BInstr :=
  [.aluImm .add a1 sp 0x3C, .aluImm .add a2 sp 0xC, .alu .add a0 x0 (18 : Fin 32), .alu .add a3 x0 (9 : Fin 32)]

/-- From 0xE2: the arguments of the `memset` that zeroes the difference
buffer, which `s3` also points at. -/
def mmSubPre : List BInstr :=
  [.aluImm .add a0 sp 0x3C, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0, .aluImm .add (19 : Fin 32) sp 0x3C]

/-- From 0xF6: the borrow, the accumulator pointer, and the count. -/
def mmSubInit : List BInstr :=
  [.aluImm .add a2 x0 0, .aluImm .add (9 : Fin 32) sp 0xC, .aluImm .add (8 : Fin 32) x0 0xC]

/-- From 0xA: keep the arguments, and set up the `memset` that zeroes the
accumulator. -/
def mmPro : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a4, .alu .add (23 : Fin 32) x0 a3, .alu .add (21 : Fin 32) x0 a2,
   .alu .add (20 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0x30,
   .aluImm .add a1 x0 0]

section
set_option maxRecDepth 20000
theorem mmChoice_end : blockEnd mulMont12Code 0x11C mmChoice = some 0x13A := by decide
theorem mmSelArgs_end : blockEnd mulMont12Code 0x142 mmSelArgs = some 0x14A := by decide
theorem mmSubPre_end : blockEnd mulMont12Code 0xE2 mmSubPre = some 0xEE := by decide
theorem mmSubInit_end : blockEnd mulMont12Code 0xF6 mmSubInit = some 0xFC := by decide
theorem mmPro_end : blockEnd mulMont12Code 0xA mmPro = some 0x1C := by decide
end

/-- The choice `mul_montgomery_form` passes to `Uint<12>::select`. -/
theorem choice_val (mc b : Word) (hb : b = 0 ∨ b = 0xFFFFFFFF) :
    aluEval .and (aluEval .sltu mc 1) b = if mc.toNat = 0 ∧ maskBit b = 1 then 1 else 0 := by
  have hs : aluEval .sltu mc 1 = if mc.toNat = 0 then 1 else 0 := by
    show (if mc.ult 1 then 1 else 0 : Word) = _
    by_cases h : mc.toNat = 0
    · rw [ite_eq_left h, ite_eq_left (show mc.ult 1 = true from by
        show decide (mc.toNat < (1 : Word).toNat) = true; rw [h]; rfl)]
    · rw [ite_eq_right h, ite_eq_right (show ¬ mc.ult 1 = true from by
        show ¬ decide (mc.toNat < (1 : Word).toNat) = true
        rw [show (1 : Word).toNat = 1 from rfl]
        exact fun e => h (by have := of_decide_eq_true e; omega))]
  rw [hs]
  rcases hb with rfl | rfl
  · rw [show maskBit 0 = 0 from rfl]
    by_cases h : mc.toNat = 0
    · rw [ite_eq_left h, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (by omega)]; rfl
  · rw [show maskBit 0xFFFFFFFF = 1 from rfl]
    by_cases h : mc.toNat = 0
    · rw [ite_eq_left h, ite_eq_left ⟨h, rfl⟩]; rfl
    · rw [ite_eq_right h, ite_eq_right (fun e => h e.1)]; rfl

set_option maxRecDepth 20000 in
theorem mmChoice_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmChoice (M, f)).1 = memStore8 (memStore32 M (f sp + 0x6C) (f (22 : Fin 32))) (f sp + 0x6C)
      ((aluEval .and (aluEval .sltu (f (22 : Fin 32)) 1) (f a2)).extractLsb' 0 8) ∧
    (runBlock mmChoice (M, f)).2 (9 : Fin 32) = aluEval .and (aluEval .sltu (f (22 : Fin 32)) 1) (f a2) ∧
    (runBlock mmChoice (M, f)).2 a0 = f (22 : Fin 32) ∧ (runBlock mmChoice (M, f)).2 a1 = 0 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (9 : Fin 32) → (runBlock mmChoice (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmChoice]
  refine ⟨?_, ?_, ?_, ?_, fun q q0 q1 q2 q9 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rw [memLoad32_store32_same]
  · simp +decide only [upd, ↓reduceIte]; rw [memLoad32_store32_same]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q9]

theorem mmChoice_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f sp + 0x6C).toNat % 4 = 0) (hs : Sep (f sp + 0x6C) 4 base len) : BlockOk base len mmChoice (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, mmChoice, upd, ↓reduceIte, and_true, true_and]
  exact ⟨⟨h, hs⟩, h, hs.sub (c := 0) (l := 1) (by decide) |> fun h' => by rwa [add_ofNat_zero] at h'⟩

theorem mmSelArgs_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmSelArgs (M, f)).1 = M ∧ (runBlock mmSelArgs (M, f)).2 a1 = f sp + 0x3C ∧
    (runBlock mmSelArgs (M, f)).2 a2 = f sp + 0xC ∧ (runBlock mmSelArgs (M, f)).2 a0 = f (18 : Fin 32) ∧
    (runBlock mmSelArgs (M, f)).2 a3 = f (9 : Fin 32) ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → (runBlock mmSelArgs (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmSelArgs]
  refine ⟨trivial, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q3]

theorem mmSubPre_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmSubPre (M, f)).1 = M ∧ (runBlock mmSubPre (M, f)).2 a0 = f sp + 0x3C ∧
    (runBlock mmSubPre (M, f)).2 a2 = 0x30 ∧ (runBlock mmSubPre (M, f)).2 a1 = 0 ∧
    (runBlock mmSubPre (M, f)).2 (19 : Fin 32) = f sp + 0x3C ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (19 : Fin 32) → (runBlock mmSubPre (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmSubPre]
  refine ⟨trivial, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q3]

theorem mmSubInit_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmSubInit (M, f)).1 = M ∧ (runBlock mmSubInit (M, f)).2 a2 = 0 ∧
    (runBlock mmSubInit (M, f)).2 (9 : Fin 32) = f sp + 0xC ∧
    (runBlock mmSubInit (M, f)).2 (8 : Fin 32) = BitVec.ofNat 32 (12 - 0) ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → (runBlock mmSubInit (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmSubInit]
  refine ⟨trivial, ?_, ?_, ?_, fun q q2 q9 q8 => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q9, q8]

theorem mmPro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock mmPro (M, f)).1 = M ∧
    (runBlock mmPro (M, f)).2 (19 : Fin 32) = f a4 ∧ (runBlock mmPro (M, f)).2 (23 : Fin 32) = f a3 ∧
    (runBlock mmPro (M, f)).2 (21 : Fin 32) = f a2 ∧ (runBlock mmPro (M, f)).2 (20 : Fin 32) = f a1 ∧
    (runBlock mmPro (M, f)).2 (18 : Fin 32) = f a0 ∧ (runBlock mmPro (M, f)).2 a0 = f sp + 0xC ∧
    (runBlock mmPro (M, f)).2 a2 = 0x30 ∧ (runBlock mmPro (M, f)).2 a1 = 0 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) →
      q ≠ (21 : Fin 32) → q ≠ (23 : Fin 32) → (runBlock mmPro (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, mmPro]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q18 q19 q20 q21 q23 => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q18, q19, q20, q21, q23]

theorem accV_lt (M : Word → BitVec 8) (b : Word) : ∀ n, accV M b n < 2 ^ (32 * n)
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    rw [accV_succ1, pow32_succ]
    have ih := accV_lt M b n
    have hw := (memLoad32 M (b + BitVec.ofNat 32 (4 * n))).isLt
    have : (memLoad32 M (b + BitVec.ofNat 32 (4 * n))).toNat * 2 ^ (32 * n) ≤ (2 ^ 32 - 1) * 2 ^ (32 * n) :=
      Nat.mul_le_mul_right _ (by omega)
    have e : (2 ^ 32 - 1) * 2 ^ (32 * n) + 2 ^ (32 * n) = 2 ^ (32 * n) * 2 ^ 32 := by
      rw [Nat.mul_comm (2 ^ (32 * n)), ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by decide)]
    omega

/-- **The conditional subtraction picks `T mod N`**, for a sum `T` below
`2N` held as the accumulator `A` and the top carry `mc`, and the
subtraction `A - N` into `Dv` with borrow `mb`. -/
theorem mm_final_arith {A mc N Dv mb Bk : Nat} (hD : Dv < Bk) (hN : N < Bk)
    (hT : A + mc * Bk < 2 * N) (hsub : A + Bk * mb = N + Dv) (hmb : mb ≤ 1) :
    (if mc = 0 ∧ mb = 1 then A else Dv) = (A + mc * Bk) % N := by
  have hmb' : mb = 0 ∨ mb = 1 := by omega
  have hc : mc = 0 ∨ mc = 1 ∨ 2 ≤ mc := by omega
  rcases hmb' with rfl | rfl <;> rcases hc with h | h | h
  · subst h
    rw [ite_eq_right (fun e => absurd e.2 (by decide)), Nat.zero_mul, Nat.add_zero]
    rw [Nat.mul_zero, Nat.add_zero] at hsub
    rw [Nat.mod_eq_sub_mod (by omega), show A - N = Dv by omega, Nat.mod_eq_of_lt (by omega)]
  · subst h; exfalso; omega
  · have := Nat.mul_le_mul_right Bk h; exfalso; omega
  · subst h
    rw [ite_eq_left ⟨rfl, rfl⟩, Nat.zero_mul, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · subst h
    rw [ite_eq_right (fun e => Nat.one_ne_zero e.1), Nat.one_mul]
    rw [Nat.mod_eq_sub_mod (by omega), show A + Bk - N = Dv by omega, Nat.mod_eq_of_lt (by omega)]
  · have := Nat.mul_le_mul_right Bk h; exfalso; omega

/-- The Montgomery result's congruence, from the sum's. -/
theorem mont_congr {T N XY U R : Nat} (hR : R = T % N) (h : 2 ^ 384 * T = XY + U * N) :
    R * 2 ^ 384 % N = XY % N := by
  rw [hR, Nat.mod_mul_mod, Nat.mul_comm, h, Nat.add_mul_mod_self_right]

/-- Where `mul_montgomery_form::<12>` runs: its code and its callees' at
their offsets, the 0xF0 bytes of stack below `sp0` that it, `borrowing_sub`,
and `Uint<12>::select` use, and the result and operands, aligned and apart
from what each must not touch. -/
structure MMEnv (M : Word → BitVec 8) (P sp0 out xp yp np : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P mulMont12Code
  save : CodeIn M (P + 0xCB9A) mulMont12SaveCode
  setup : CodeIn M (P + 0xD040) mulMont12SetupCode
  restore : CodeIn M (P + 0xCBE8) mulMont12RestoreCode
  mset : CodeIn M (P + 0xD2F4) memsetCode
  bsub : CodeIn M (mmBsub P) borrowingSubCode
  sel : CodeIn M (P + 0x15E) uintSelect12Code
  stub : CodeIn M (P + 0xD35C) memcpyStubCode
  body : CodeIn M (P + 0xD364) memcpyBodyCode
  step : CodeIn M (P + 0xD14C) uintSelect12StepCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xF0 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hxp : xp.toNat % 4 = 0
  hyp : yp.toNat % 4 = 0
  hnp : np.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF10) 0xF0 P mulMont12Code.length
  sGS : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xCB9A) mulMont12SaveCode.length
  sGT : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xD040) mulMont12SetupCode.length
  sGR : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xCBE8) mulMont12RestoreCode.length
  sGM : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xD2F4) memsetCode.length
  sGB : Sep (sp0 + 0xFFFFFF10) 0xF0 (mmBsub P) borrowingSubCode.length
  sGL : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0x15E) uintSelect12Code.length
  sGU : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xD35C) memcpyStubCode.length
  sGY : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xD364) memcpyBodyCode.length
  sGP : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xD14C) uintSelect12StepCode.length
  sOG : Sep out 48 (sp0 + 0xFFFFFF10) 0xF0
  sOC : Sep out 48 P mulMont12Code.length
  sOR : Sep out 48 (P + 0xCBE8) mulMont12RestoreCode.length
  sOL : Sep out 48 (P + 0x15E) uintSelect12Code.length
  sOY : Sep out 48 (P + 0xD364) memcpyBodyCode.length
  sXG : Sep xp 48 (sp0 + 0xFFFFFF10) 0xF0
  sYG : Sep yp 48 (sp0 + 0xFFFFFF10) 0xF0
  sNG : Sep np 48 (sp0 + 0xFFFFFF10) 0xF0

theorem frameA0 (sp0 : Word) (h : 0xF0 ≤ sp0.toNat) :
    (sp0 + 0xFFFFFF10).toNat + 0xF0 = sp0.toNat ∧ sp0 + 0xFFFFFF60 = sp0 + 0xFFFFFF10 + BitVec.ofNat 32 0x50 ∧
      (sp0 + 0xFFFFFF60).toNat + 0xA0 = sp0.toNat := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.toNat_add]; have : (0xFFFFFF10 : Word).toNat = 0xFFFFFF10 := rfl; rw [this]; have := sp0.isLt; omega
  · rw [BitVec.add_assoc]; rfl
  · rw [BitVec.toNat_add]; have : (0xFFFFFF60 : Word).toNat = 0xFFFFFF60 := rfl; rw [this]; have := sp0.isLt; omega

/-- The frame `[F, F + 0xA0)` of `mul_montgomery_form::<12>` inside its
stack region. -/
theorem MMEnv.frame {M : Word → BitVec 8} {P sp0 out xp yp np : Word} (E : MMEnv M P sp0 out xp yp np)
    {b : Word} {l : Nat} (h : Sep (sp0 + 0xFFFFFF10) 0xF0 b l) : Sep (sp0 + 0xFFFFFF60) 0xA0 b l := by
  rw [(frameA0 sp0 E.hS).2.1]; exact h.sub (by decide)

/-- **The prologue of `mul_montgomery_form::<12>`**, from 0 to the outer
loop at 0x32: open the frame at `F`, save registers, zero the accumulator
at `F + 0xC`, and set up the first pass. -/
theorem mm_pro (m : Machine) {P sp0 out xp yp np K : Word} (E : MMEnv m.mem P sp0 out xp yp np) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (ha2 : reg m a2 = yp) (ha3 : reg m a3 = np) (ha4 : reg m a4 = K)
    (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x32 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ mmPs → memLoad32 M (sp0 + 0xFFFFFF60 + o) = reg m r) ∧
      accV M (sp0 + 0xFFFFFF60 + 0xC) 12 = 0 ∧
      reg n sp = sp0 + 0xFFFFFF60 ∧ reg n (22 : Fin 32) = 0 ∧ reg n (29 : Fin 32) = BitVec.ofNat 32 0 ∧
      reg n (20 : Fin 32) = xp ∧ reg n (6 : Fin 32) = memLoad32 m.mem yp ∧
      reg n (7 : Fin 32) = memLoad32 m.mem np ∧ reg n (19 : Fin 32) = K ∧
      reg n (17 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n a6 = sp0 + 0xFFFFFF60 + 0xC + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n (21 : Fin 32) = yp + BitVec.ofNat 32 (4 * (0 + 1)) ∧ reg n (28 : Fin 32) = 0 ∧
      reg n (5 : Fin 32) = 12 ∧ reg n (18 : Fin 32) = out ∧ reg n (23 : Fin 32) = np ∧
      ∀ q, q.val ∈ [3, 4, 27] → reg n q = reg m q := by
  obtain ⟨hG, hFG, hFw⟩ := frameA0 sp0 E.hS
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hFa : (sp0 + 0xFFFFFF60).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFF60) (by decide)
  have sFC := E.frame E.sGC; have sFS := E.frame E.sGS; have sFT := E.frame E.sGT; have sFM := E.frame E.sGM
  obtain ⟨m1, d1, u1⟩ := s0.aluImm E.code mm_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60) sp = sp0 + 0xFFFFFF60 := by
    simp +decide [upd, hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := u1.callSave E.code mm_at_2 mm_at_6 (b := P + 0xCB9A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP 0xCB9A (by decide))
    (even_at P E.hP 0xA (by decide)) E.save mmSave_shape (by decide) (fun q hq => by
      rw [sp1]
      simp only [mmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, aligned_add hFa (by decide), sFS.sub (by decide)⟩)
  rw [sp1] at u2
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF60) 0xA0 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have I2 : ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 →
      saveMem m.mem (sp0 + 0xFFFFFF60) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs x = m.mem x :=
    fun x hx => saveMem_outside mmPs fun q hq => by
      simp only [mmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hx.sub (by decide)
  have r2 : ∀ q, q ≠ sp → q ≠ t0 → reg m2 q = reg m q := fun q q1 q2 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1, q2]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFF60 := by rw [u2.regs]; simp +decide [upd]; exact sp1
  -- keep the arguments
  have hc2 := codeS E.code sFC I2
  obtain ⟨m3, c3, u3⟩ := St.block mmPro u2.self hc2 mmPro_end (by
    simp only [BlockOk, BInstr.ok, mmPro]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial⟩)
  obtain ⟨em3, p19, p23, p21, p20, p18, pa0, pa2, pa1, pk⟩ := mmPro_run (M := saveMem m.mem (sp0 + 0xFFFFFF60)
    (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs) (f := reg m2) u2.self.zero
  rw [em3] at u3
  have g3 : ∀ q, reg m3 q = (runBlock mmPro (saveMem m.mem (sp0 + 0xFFFFFF60)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs, reg m2)).2 q := u3.regs
  -- zero the accumulator
  obtain ⟨m4, c4, u4, a04, fr4⟩ := u3.self.memsetW (B := P + 0xD2F4) (w := 12) (dst := sp0 + 0xFFFFFF60 + 0xC)
    (even_at P E.hP 0xD2F4 (by decide)) hc2 (codeS E.mset sFM I2) mm_at_1c mm_at_20
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP (0x1C + 8) (by decide)) (by decide)
    (by rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega) (by decide)
    (aligned_add hFa (k := 0xC) (by decide)) (sFM.sub (c := 0xC) (l := 48) (by decide))
    (by rw [g3, pa0, sp2]) (by rw [g3, pa1]) (by rw [g3, pa2]; rfl)
  obtain ⟨M4, hM4⟩ : ∃ M4, fillWords (saveMem m.mem (sp0 + 0xFFFFFF60)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs) (sp0 + 0xFFFFFF60 + 0xC) 0 12 = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have I4 : ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, fillWords_outside (dst := sp0 + 0xFFFFFF60 + 0xC) 12 (hx.sub (c := 0xC) (l := 48) (by decide)), I2 x hx]
  have k4 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m4 q = reg m3 q := fr4
  have e21 : reg m4 (21 : Fin 32) = yp := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3, p21,
      r2 _ (by decide) (by decide), ha2]
  have e23 : reg m4 (23 : Fin 32) = np := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3, p23,
      r2 _ (by decide) (by decide), ha3]
  have sp4 : reg m4 sp = sp0 + 0xFFFFFF60 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3,
      pk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  -- the setup helper
  have hu : ∀ q : Fin 32, q ≠ t0 → upd (reg m4) t0 (P + BitVec.ofNat 32 (0x1C + 8 + 8)) q = reg m4 q := fun q hq => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [upd_zero, u4.self.zero]
    · exact upd_ne h0 hq
  obtain ⟨m5, c5, u5⟩ := u4.self.callBlock (codeS E.code sFC I4) mm_at_24 mm_at_28
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP 0xD040 (by decide))
    (even_at P E.hP (0x1C + 8 + 8) (by decide)) (codeS E.setup sFT I4) mmSetup mmSetup_end mst_at_18
    (mmSetup_ok (by rw [hu _ (by decide), e21, add_lit_zero]; exact E.hyp)
      (by rw [hu _ (by decide), e23, add_lit_zero]; exact E.hnp))
    (by rw [(mmSetup_run (M := M4) (f := upd (reg m4) t0 (P + BitVec.ofNat 32 (0x1C + 8 + 8))) (upd_zero _ _ _)).2.2.2.2.2.2.2.2.2
      t0 rfl, upd_t0])
  obtain ⟨em5, s22, s28, s29, s6, s7, s21, sa6, s17, sk⟩ := mmSetup_run (M := M4)
    (f := upd (reg m4) t0 (P + BitVec.ofNat 32 (0x1C + 8 + 8))) (upd_zero _ _ _)
  rw [em5] at u5
  have g5 : ∀ q, reg m5 q = (runBlock mmSetup (M4, upd (reg m4) t0 (P + BitVec.ofNat 32 (0x1C + 8 + 8)))).2 q := u5.regs
  have hc4 := codeS E.code sFC I4
  obtain ⟨m6, d6, u6⟩ := u5.self.aluImm hc4 mm_at_2c (off' := 0x2E) (by decide)
  have v6 : upd (reg m5) (5 : Fin 32) (aluEval .add (reg m5 x0) 0xC) (5 : Fin 32) = 12 := by
    simp +decide only [upd, ↓reduceIte, u5.self.zero]
  obtain ⟨m7, d7, u7⟩ := u6.notTaken hc4 0x32 mm_at_2e (by decide) (by
    rw [v6]; simp +decide only [upd, ↓reduceIte])
  have g7 : ∀ q, q ≠ (5 : Fin 32) → reg m7 q = reg m5 q := fun q hq => by
    rw [u7.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, u5.self.zero]
    · simp [upd, h0, hq]
  have kk : ∀ q, setupKeep q = true → q ≠ (5 : Fin 32) → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra →
      reg m7 q = (runBlock mmPro (saveMem m.mem (sp0 + 0xFFFFFF60)
        (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs, reg m2)).2 q :=
    fun q hs h5 h2 h3 h4 h5' h6 hr => by rw [g7 q h5, g5, sk q hs, hu q h5, k4 q h2 h3 h4 h5' h6 hr, g3]
  have hyF : Sep (sp0 + 0xFFFFFF60) 0xA0 yp 4 := (E.frame E.sYG.symm).subR (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  have hnF : Sep (sp0 + 0xFFFFFF60) 0xA0 np 4 := (E.frame E.sNG.symm).subR (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  refine ⟨m7, M4, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (.single d7)))))), u7.self, I4,
    fun r o hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · have slot : ∀ (r : Fin 32) (o : Word), (r, o) ∈ mmPs → 0x70 ≤ o.toNat → o.toNat + 4 ≤ 0xA0 →
        (∀ p ∈ mmPs, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
          p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32)) → r ≠ sp →
        memLoad32 M4 (sp0 + 0xFFFFFF60 + o) = reg m r := fun r o hm h1 h2 hp hr => by
      have hFo : sp0 + 0xFFFFFF60 + BitVec.ofNat 32 o.toNat = sp0 + 0xFFFFFF60 + o := by rw [ofNat_toNat_self]
      rw [← hM4, ← hFo, fillWords_load_sep (dst := sp0 + 0xFFFFFF60 + 0xC) (by
        have := sep_offsets (sp0 + 0xFFFFFF60) (c := 0xC) (n := 48) (d := o.toNat) (k := 4) (.inl (by omega))
          (by omega) (by omega)
        exact this), hFo, saveMem_slot mmPs _ hm hp, upd_ne (by
          intro h; apply hr; exact Fin.ext (by
            simp only [mmPs, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
              (rw [Prod.mk.injEq] at h'; rw [h'.1] at h; exact absurd h (by decide)))) hr]
    simp only [mmPs, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
      (rw [Prod.mk.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'; exact slot _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide))
  · have hacw : (sp0 + 0xFFFFFF60 + 0xC).toNat + 4 * 12 ≤ 2 ^ 32 := by
      rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega
    rw [← hM4]
    exact accV_zero 12 fun i hi => fillWords_load 12 i hi hacw
  · rw [g7 _ (by decide), g5, sk _ rfl, hu _ (by decide), sp4]
  · rw [g7 _ (by decide), g5, s22]
  · rw [g7 _ (by decide), g5, s29]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p20,
      r2 _ (by decide) (by decide), ha1]
  · rw [g7 _ (by decide), g5, s6, hu _ (by decide), e21, add_lit_zero, ← hM4,
      fillWords_load_sep (dst := sp0 + 0xFFFFFF60 + 0xC) ((hyF.sub (c := 0xC) (l := 48) (by decide))),
      load_frame I2 hyF]
  · rw [g7 _ (by decide), g5, s7, hu _ (by decide), e23, add_lit_zero, ← hM4,
      fillWords_load_sep (dst := sp0 + 0xFFFFFF60 + 0xC) ((hnF.sub (c := 0xC) (l := 48) (by decide))),
      load_frame I2 hnF]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p19,
      r2 _ (by decide) (by decide), ha4]
  · rw [g7 _ (by decide), g5, s17, hu _ (by decide), e23]; rfl
  · have e : (0xC : Word) + BitVec.ofNat 32 (4 * (0 + 1)) = 0x10 := by decide
    rw [g7 _ (by decide), g5, sa6, hu _ (by decide), sp4, BitVec.add_assoc (sp0 + 0xFFFFFF60) 0xC, e]
  · rw [g7 _ (by decide), g5, s21, hu _ (by decide), e21]; rfl
  · rw [g7 _ (by decide), g5, s28]
  · rw [u7.regs, v6]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p18,
      r2 _ (by decide) (by decide), ha0]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p23,
      r2 _ (by decide) (by decide), ha3]
  · have key : ∀ q : Fin 32, q.val ∈ [3, 4, 27] → setupKeep q = true ∧ q ≠ (5 : Fin 32) ∧ q ≠ a2 ∧ q ≠ a3 ∧
        q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧
        q ≠ (20 : Fin 32) ∧ q ≠ (21 : Fin 32) ∧ q ≠ (23 : Fin 32) ∧ q ≠ sp ∧ q ≠ t0 := by decide
    obtain ⟨hs, h5, h2, h3, h4, h5', h6, hr, h0, h1, h18, h19, h20, h21, h23, hsp', ht0⟩ := key q hq
    rw [kk q hs h5 h2 h3 h4 h5' h6 hr, pk q h0 h1 h2 h18 h19 h20 h21 h23, r2 q hsp' ht0]

theorem maskBit_zero' : maskBit 0 = 0 := by unfold maskBit; decide

theorem sub_inv0 (M M' : Word → BitVec 8) (a b c : Word) :
    accV M a 0 + 2 ^ (32 * 0) * maskBit 0 = accV M b 0 + accV M' c 0 := by
  rw [maskBit_zero']; rfl

/-- The registers the final subtraction leaves alone. -/
def midKeep (q : Fin 32) : Bool := q.val ∉ [1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 23]

set_option exponentiation.threshold 400 in
/-- **The final subtraction of `mul_montgomery_form::<12>`**, from 0xE2 to
0x11C: zero the buffer at `F + 0x3C`, then subtract the modulus from the
accumulator at `F + 0xC` into it. -/
theorem mm_mid {P sp0 out xp yp np : Word} {M0 : Word → BitVec 8} (E : MMEnv M0 P sp0 out xp yp np)
    {M : Word → BitVec 8} {n : Machine} (s : St M P n 0xE2 (reg n))
    (hfr : ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → M x = M0 x)
    (rsp : reg n sp = sp0 + 0xFFFFFF60) (r23 : reg n (23 : Fin 32) = np) :
    ∃ n' M', Steps n n' ∧ St M' P n' 0x11C (reg n') ∧
      (∀ x, Sep (sp0 + 0xFFFFFF5C) 4 x 1 → Sep (sp0 + 0xFFFFFF60 + 0x3C) 48 x 1 → M' x = M x) ∧
      (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
      accV M (sp0 + 0xFFFFFF60 + 0xC) 12 + 2 ^ (32 * 12) * maskBit (reg n' a2) =
        accV M np 12 + accV M' (sp0 + 0xFFFFFF60 + 0x3C) 12 ∧
      reg n' sp = sp0 + 0xFFFFFF60 ∧ ∀ q, midKeep q = true → reg n' q = reg n q := by
  obtain ⟨hG, hFG, hFw⟩ := frameA0 sp0 E.hS
  have hGa : (sp0 + 0xFFFFFF10).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFF10) (by decide)
  have eF4 : sp0 + 0xFFFFFF60 + 0xFFFFFFFC = sp0 + 0xFFFFFF10 + BitVec.ofNat 32 0x4C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eF4' : sp0 + 0xFFFFFF5C = sp0 + 0xFFFFFF10 + BitVec.ofNat 32 0x4C := by rw [BitVec.add_assoc]; rfl
  have eA : sp0 + 0xFFFFFF60 + 0xC = sp0 + 0xFFFFFF10 + BitVec.ofNat 32 0x5C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eD : sp0 + 0xFFFFFF60 + 0x3C = sp0 + 0xFFFFFF10 + BitVec.ofNat 32 0x8C := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have go : ∀ c d k, c + 4 ≤ d ∨ d + k ≤ c → d + k ≤ 0xF0 → c + 4 ≤ 0xF0 →
      Sep (sp0 + 0xFFFFFF10 + BitVec.ofNat 32 c) 4 (sp0 + 0xFFFFFF10 + BitVec.ofNat 32 d) k :=
    fun c d k h h1 h2 => sep_offsets _ h (by omega) (by omega)
  have codeF : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn M0 b code →
      Sep (sp0 + 0xFFFFFF10) 0xF0 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → M' x = M0 x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ ((E.frame hs).subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hc := codeF E.code E.sGC hfr
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := St.block mmSubPre s hc mmSubPre_end (by
    simp only [BlockOk, BInstr.ok, mmSubPre]; exact ⟨trivial, trivial, trivial, trivial, trivial⟩)
  obtain ⟨em1, b0, b2, b1, b19, bk⟩ := mmSubPre_run (M := M) (f := reg n) hz
  rw [em1] at u1
  have g1 : ∀ q, reg n1 q = (runBlock mmSubPre (M, reg n)).2 q := u1.regs
  rw [rsp] at b0 b19
  have hDa : (sp0 + 0xFFFFFF60 + 0x3C).toNat % 4 = 0 := by rw [eD]; exact aligned_add hGa (by decide)
  have hDw : (sp0 + 0xFFFFFF60 + 0x3C).toNat + 48 < 2 ^ 32 := by
    rw [eD, BitVec.toNat_add, BitVec.toNat_ofNat]; have := sp0.isLt; omega
  obtain ⟨n2, c2, u2, a02, fr2⟩ := u1.self.memsetW (B := P + 0xD2F4) (w := 12) (dst := sp0 + 0xFFFFFF60 + 0x3C)
    (even_at P E.hP 0xD2F4 (by decide)) hc (codeF E.mset E.sGM hfr) mm_at_ee mm_at_f2
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP (0xEE + 8) (by decide)) (by decide)
    (by omega) (by decide) hDa (by rw [eD]; exact E.sGM.sub (c := 0x8C) (l := 48) (by decide))
    (by rw [g1, b0]) (by rw [g1, b1]) (by rw [g1, b2]; rfl)
  obtain ⟨MS, hMS⟩ : ∃ MS, fillWords M (sp0 + 0xFFFFFF60 + 0x3C) 0 12 = MS := ⟨_, rfl⟩
  rw [hMS] at u2
  have hS : ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → MS x = M0 x := fun x hx => by
    rw [← hMS, fillWords_outside 12 (by
      have := hx.sub (c := 0x3C) (l := 48) (by decide); exact this), hfr x hx]
  have hcS := codeF E.code E.sGC hS
  obtain ⟨n3, c3, u3⟩ := St.block mmSubInit u2 hcS mmSubInit_end (by
    simp only [BlockOk, BInstr.ok, mmSubInit]; exact ⟨trivial, trivial, trivial, trivial⟩)
  obtain ⟨em3, i2, i9, i8, ik⟩ := mmSubInit_run (M := MS) (f := reg n2) u2.zero
  rw [em3] at u3
  have g3 : ∀ q, reg n3 q = (runBlock mmSubInit (MS, reg n2)).2 q := u3.regs
  obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hcS 0xFE mm_at_fc (by decide) (by rw [g3, i8, u3.self.zero]; decide)
  have k2 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n2 q = (runBlock mmSubPre (M, reg n)).2 q :=
    fun q h2 h3 h4 h5 h6 hr => by rw [fr2 q h2 h3 h4 h5 h6 hr, g1]
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (19 : Fin 32) →
      q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → reg n4 q = reg n q := fun q h0 h1 h2 h3 h4 h5 h6 hr h19 h9 h8 => by
    rw [u4.regs, g3, ik q h2 h9 h8, k2 q h2 h3 h4 h5 h6 hr, bk q h0 h1 h2 h19]
  have sp4 : reg n4 sp = sp0 + 0xFFFFFF60 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), rsp]
  have sDA : Sep (sp0 + 0xFFFFFF60 + 0x3C) 48 (sp0 + 0xFFFFFF60 + 0xC) 48 := by
    rw [eD, eA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide)
  obtain ⟨n5, M5, c5, u5, hc5, hf5, hm5, hv5, sp5, fr5⟩ := sub_loop (M0 := MS) (F := sp0 + 0xFFFFFF60)
    (acc := sp0 + 0xFFFFFF60 + 0xC) (np := np) (D := sp0 + 0xFFFFFF60 + 0x3C) E.hP
    (aligned_add E.hsp (k := 0xFFFFFF60) (by decide)) (by rw [eA]; exact aligned_add hGa (by decide)) E.hnp hDa (Nat.le_of_lt hDw)
    (by rw [eF4, eA]; exact go _ _ _ (.inl (by decide)) (by decide) (by decide))
    (by rw [eF4]; exact E.sNG.symm.sub (c := 0x4C) (l := 4) (by decide))
    (by rw [eF4, eD]; exact go _ _ _ (.inl (by decide)) (by decide) (by decide))
    sDA (by rw [eD]; exact E.sNG.symm.sub (c := 0x8C) (l := 48) (by decide))
    (by rw [eF4]; exact E.sGB.sub (c := 0x4C) (l := 4) (by decide))
    (by rw [eF4]; exact E.sGC.sub (c := 0x4C) (l := 4) (by decide))
    (by rw [eD]; exact E.sGB.sub (c := 0x8C) (l := 48) (by decide))
    (by rw [eD]; exact E.sGC.sub (c := 0x8C) (l := 48) (by decide))
    11 0 (by decide) u4.self hcS (codeF E.bsub E.sGB hS) (fun _ _ _ => rfl) (.inl rfl) (sub_inv0 _ _ _ _ _) sp4
    (by rw [u4.regs, g3, i9, k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      bk _ (by decide) (by decide) (by decide) (by decide), rsp, Nat.mul_zero, add_ofNat_zero])
    (by rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), r23, Nat.mul_zero, add_ofNat_zero])
    (by rw [u4.regs, g3, ik _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), b19, Nat.mul_zero, add_ofNat_zero])
    (by rw [u4.regs, g3, i8]) (by rw [u4.regs, g3, i2])
  have eAcc : accV MS (sp0 + 0xFFFFFF60 + 0xC) 12 = accV M (sp0 + 0xFFFFFF60 + 0xC) 12 :=
    accV_congr 12 fun i hi => by rw [← hMS]; exact fillWords_load_sep (sDA.subR (c := 4 * i) (l := 4) (by omega))
  have sDN : Sep (sp0 + 0xFFFFFF60 + 0x3C) 48 np 48 := by rw [eD]; exact E.sNG.symm.sub (c := 0x8C) (l := 48) (by decide)
  have eNp : accV MS np 12 = accV M np 12 :=
    accV_congr 12 fun i hi => by rw [← hMS]; exact fillWords_load_sep (sDN.subR (c := 4 * i) (l := 4) (by omega))
  refine ⟨n5, M5, c1.trans (c2.trans (c3.trans (.cons d4 c5))), u5, fun x h1 h2 => ?_, hm5, ?_, sp5, fun q hq => ?_⟩
  · rw [hf5 x (by rw [eF4]; rw [eF4'] at h1; exact h1) h2, ← hMS, fillWords_outside 12 h2]
  · rw [← eAcc, ← eNp]; exact hv5
  · have key : ∀ q : Fin 32, midKeep q = true → q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧
        q ≠ ra ∧ q ≠ (19 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (8 : Fin 32) ∧ q ≠ (23 : Fin 32) := by decide
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, hr, h19, h9, h8, h23⟩ := key q hq
    rw [fr5 q h0 h1 h2 h3 h4 hr h9 h23 h19 h8, k4 q h0 h1 h2 h3 h4 h5 h6 hr h19 h9 h8]

end C3.RV32
