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

end C3.RV32
