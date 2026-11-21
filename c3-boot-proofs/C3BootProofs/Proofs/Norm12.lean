import C3BootProofs.Proofs.P384Neg

/-!
# `SignedInt<12>::norm`

The compiled function returns the magnitude of a signed 384-bit value, or
the modulus minus the magnitude when the value's sign differs from `f`'s
and the magnitude isn't zero. It calls the proved `Uint<12>::is_nonzero`,
zeroes a frame buffer with `memset`, subtracts the magnitude from the
modulus into it with 12 `borrowing_sub` calls, and picks the magnitude or
the difference with the proved `Uint<12>::select`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem nm12_at_0 : fetchRel norm12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem nm12_at_2 : fetchRel norm12Code 0x2 = some (.store .sw sp ra 0x5C, 2) := by decide
theorem nm12_at_4 : fetchRel norm12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x58, 2) := by decide
theorem nm12_at_6 : fetchRel norm12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x54, 2) := by decide
theorem nm12_at_8 : fetchRel norm12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x50, 2) := by decide
theorem nm12_at_a : fetchRel norm12Code 0xA = some (.store .sw sp (19 : Fin 32) 0x4C, 2) := by decide
theorem nm12_at_c : fetchRel norm12Code 0xC = some (.store .sw sp (20 : Fin 32) 0x48, 2) := by decide
theorem nm12_at_e : fetchRel norm12Code 0xE = some (.store .sw sp (21 : Fin 32) 0x44, 2) := by decide
theorem nm12_at_10 : fetchRel norm12Code 0x10 = some (.store .sw sp (22 : Fin 32) 0x40, 2) := by decide
theorem nm12_at_12 : fetchRel norm12Code 0x12 = some (.store .sw sp (23 : Fin 32) 0x3C, 2) := by decide
theorem nm12_at_14 : fetchRel norm12Code 0x14 = some (.store .sw sp (24 : Fin 32) 0x38, 2) := by decide
theorem nm12_at_16 : fetchRel norm12Code 0x16 = some (.alu .add (23 : Fin 32) x0 a3, 2) := by decide
theorem nm12_at_18 : fetchRel norm12Code 0x18 = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem nm12_at_1a : fetchRel norm12Code 0x1A = some (.alu .add (22 : Fin 32) x0 a1, 2) := by decide
theorem nm12_at_1c : fetchRel norm12Code 0x1C = some (.load .lbu (20 : Fin 32) a1 0x30, 4) := by decide
theorem nm12_at_20 : fetchRel norm12Code 0x20 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem nm12_at_22 : fetchRel norm12Code 0x22 = some (.alu .add a0 x0 a1, 2) := by decide
theorem nm12_at_24 : fetchRel norm12Code 0x24 = some (.auipc ra 0x0, 4) := by decide
theorem nm12_at_28 : fetchRel norm12Code 0x28 = some (.jalr ra ra 0xFFFFFFC2, 4) := by decide
theorem nm12_at_2c : fetchRel norm12Code 0x2C = some (.aluImm .and (21 : Fin 32) a0 0xFF, 4) := by decide
theorem nm12_at_30 : fetchRel norm12Code 0x30 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem nm12_at_32 : fetchRel norm12Code 0x32 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem nm12_at_36 : fetchRel norm12Code 0x36 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem nm12_at_38 : fetchRel norm12Code 0x38 = some (.aluImm .add (24 : Fin 32) sp 0x8, 4) := by decide
theorem nm12_at_3c : fetchRel norm12Code 0x3C = some (.auipc ra 0x1000, 4) := by decide
theorem nm12_at_40 : fetchRel norm12Code 0x40 = some (.jalr ra ra 0xFFFFFC7A, 4) := by decide
theorem nm12_at_44 : fetchRel norm12Code 0x44 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem nm12_at_46 : fetchRel norm12Code 0x46 = some (.aluImm .add (9 : Fin 32) x0 0xC, 2) := by decide
theorem nm12_at_48 : fetchRel norm12Code 0x48 = some (.alu .add (8 : Fin 32) x0 (22 : Fin 32), 2) := by decide
theorem nm12_at_4a : fetchRel norm12Code 0x4A = some (.branch .beq (9 : Fin 32) x0 0x20, 2) := by decide
theorem nm12_at_4c : fetchRel norm12Code 0x4C = some (.load .lw a0 (23 : Fin 32) 0x0, 4) := by decide
theorem nm12_at_50 : fetchRel norm12Code 0x50 = some (.load .lw a1 (8 : Fin 32) 0x0, 2) := by decide
theorem nm12_at_52 : fetchRel norm12Code 0x52 = some (.auipc ra 0xFFFEE000, 4) := by decide
theorem nm12_at_56 : fetchRel norm12Code 0x56 = some (.jalr ra ra 0x79E, 4) := by decide
theorem nm12_at_5a : fetchRel norm12Code 0x5A = some (.alu .add a2 x0 a1, 2) := by decide
theorem nm12_at_5c : fetchRel norm12Code 0x5C = some (.aluImm .add (23 : Fin 32) (23 : Fin 32) 0x4, 2) := by decide
theorem nm12_at_5e : fetchRel norm12Code 0x5E = some (.store .sw (24 : Fin 32) a0 0x0, 4) := by decide
theorem nm12_at_62 : fetchRel norm12Code 0x62 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem nm12_at_64 : fetchRel norm12Code 0x64 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x4, 2) := by decide
theorem nm12_at_66 : fetchRel norm12Code 0x66 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem nm12_at_68 : fetchRel norm12Code 0x68 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem nm12_at_6a : fetchRel norm12Code 0x6A = some (.alu .xor a0 (20 : Fin 32) (19 : Fin 32), 4) := by decide
theorem nm12_at_6e : fetchRel norm12Code 0x6E = some (.alu .and a3 (21 : Fin 32) a0, 4) := by decide
theorem nm12_at_72 : fetchRel norm12Code 0x72 = some (.aluImm .add a2 sp 0x8, 2) := by decide
theorem nm12_at_74 : fetchRel norm12Code 0x74 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem nm12_at_76 : fetchRel norm12Code 0x76 = some (.alu .add a1 x0 (22 : Fin 32), 2) := by decide
theorem nm12_at_78 : fetchRel norm12Code 0x78 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem nm12_at_7c : fetchRel norm12Code 0x7C = some (.jalr ra ra 0x2C0, 4) := by decide
theorem nm12_at_80 : fetchRel norm12Code 0x80 = some (.load .lw ra sp 0x5C, 2) := by decide
theorem nm12_at_82 : fetchRel norm12Code 0x82 = some (.load .lw (8 : Fin 32) sp 0x58, 2) := by decide
theorem nm12_at_84 : fetchRel norm12Code 0x84 = some (.load .lw (9 : Fin 32) sp 0x54, 2) := by decide
theorem nm12_at_86 : fetchRel norm12Code 0x86 = some (.load .lw (18 : Fin 32) sp 0x50, 2) := by decide
theorem nm12_at_88 : fetchRel norm12Code 0x88 = some (.load .lw (19 : Fin 32) sp 0x4C, 2) := by decide
theorem nm12_at_8a : fetchRel norm12Code 0x8A = some (.load .lw (20 : Fin 32) sp 0x48, 2) := by decide
theorem nm12_at_8c : fetchRel norm12Code 0x8C = some (.load .lw (21 : Fin 32) sp 0x44, 2) := by decide
theorem nm12_at_8e : fetchRel norm12Code 0x8E = some (.load .lw (22 : Fin 32) sp 0x40, 2) := by decide
theorem nm12_at_90 : fetchRel norm12Code 0x90 = some (.load .lw (23 : Fin 32) sp 0x3C, 2) := by decide
theorem nm12_at_92 : fetchRel norm12Code 0x92 = some (.load .lw (24 : Fin 32) sp 0x38, 2) := by decide
theorem nm12_at_94 : fetchRel norm12Code 0x94 = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem nm12_at_96 : fetchRel norm12Code 0x96 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `borrowing_sub`'s offset from `norm`. -/
abbrev nmBsub (P : Word) : Word := P + 0xFFFEE7F0

/-- The end of a subtraction round, from 0x5A: keep the borrow, store the
difference, and advance the pointers and the count. -/
def nmSubTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (23 : Fin 32) (23 : Fin 32) 4, .sw (24 : Fin 32) a0 0,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 4, .aluImm .add (24 : Fin 32) (24 : Fin 32) 4,
   .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem nmSubTail_end : blockEnd norm12Code 0x5A nmSubTail = some 0x68 := by decide
end

set_option maxRecDepth 20000 in
theorem nmSubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock nmSubTail (M, f)).1 = memStore32 M (f (24 : Fin 32) + 0) (f a0) ∧
    (runBlock nmSubTail (M, f)).2 a2 = f a1 ∧
    (runBlock nmSubTail (M, f)).2 (23 : Fin 32) = f (23 : Fin 32) + 4 ∧
    (runBlock nmSubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 4 ∧
    (runBlock nmSubTail (M, f)).2 (24 : Fin 32) = f (24 : Fin 32) + 4 ∧
    (runBlock nmSubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (23 : Fin 32) → q ≠ (8 : Fin 32) → q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) →
      (runBlock nmSubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, nmSubTail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 qnp qxp qd qc => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, qnp, qxp, qd, qc]

theorem nmSubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (24 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (24 : Fin 32) + 0) 4 base len) :
    BlockOk base len nmSubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, nmSubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One round of the subtraction**, from 0x4C: subtract limb `i` of `x`
and the borrow from limb `i` of the modulus at `np`, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem nm_sub_iter {M : Word → BitVec 8} {P F np xp D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x4C (reg n)) (hc : CodeIn M P norm12Code) (hb : CodeIn M (nmBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 12) (hF : F.toNat % 4 = 0) (hnp : np.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (nmBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P norm12Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P norm12Code.length)
    (rsp : reg n sp = F) (rnp : reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i))
    (rxp : reg n (8 : Fin 32) = xp + BitVec.ofNat 32 (4 * i)) (rd : reg n (24 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (rc : reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0x4C else 0x6A) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (24 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (23 : Fin 32) → q ≠ (8 : Fin 32) →
        q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc nm12_at_4c (off' := 0x50) (by decide)
    (by rw [rnp, add_lit_zero]; exact aligned_add hnp (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc nm12_at_50 (off' := 0x52) (by decide)
    (by rw [upd_ne (by decide) (by decide), rxp, add_lit_zero]; exact aligned_add hxp (by omega))
  rw [rnp, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (8 : Fin 32) + 0)) a0 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (8 : Fin 32) + 0)) a1 =
      memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [rxp, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFEE7F0 (by decide))
    nm12_at_52 nm12_at_56 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x52 + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P norm12Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have ed : reg n3 (24 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block nmSubTail u3 hc3 nmSubTail_end
    (nmSubTail_ok (by rw [ed]; exact aligned_add hD (by omega)) (by rw [ed]; exact sDC))
  obtain ⟨em4, t2, tnp, txp, td, tc, tk⟩ := nmSubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, ed, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock nmSubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have ec : reg n4 (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [g4, tc, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rc, cnt12_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (9 : Fin 32)) (reg n4 x0) = decide (i + 1 < 12) := by
    rw [ec, u4'.zero]; exact cnt12_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (24 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (23 : Fin 32) → q ≠ (8 : Fin 32) →
        q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, ec], fun q q0 q1 q2 q3 q4 qr qnp qxp qd qc => ?_⟩
    · rw [h5, g4, tnp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rnp, ptr4]
    · rw [h5, g4, txp, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rxp, ptr4]
    · rw [h5, g4, td, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rd, ptr4]
    · rw [h5, g4, tk q q2 qnp qxp qd qc, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x4C nm12_at_68 (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x6A nm12_at_68 (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The subtraction**, from round `i` to its end at 0x6A: the buffer at
`D` gets the modulus minus `x`, and `a2` the borrow out as a mask. -/
theorem nm_sub_loop {P F np xp D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 48 ≤ 2 ^ 32)
    (sFN : Sep (F + 0xFFFFFFFC) 4 np 48) (sFX : Sep (F + 0xFFFFFFFC) 4 xp 48) (sFD : Sep (F + 0xFFFFFFFC) 4 D 48)
    (sDN : Sep D 48 np 48) (sDX : Sep D 48 xp 48)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (nmBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P norm12Code.length)
    (sDB : Sep D 48 (nmBsub P) borrowingSubCode.length) (sDC : Sep D 48 P norm12Code.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x4C (reg n) → CodeIn M P norm12Code → CodeIn M (nmBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (24 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x6A (reg n') ∧ CodeIn M' P norm12Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np 12 + 2 ^ (32 * 12) * maskBit (reg n' a2) = accV M0 xp 12 + accV M' D 12 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (23 : Fin 32) → q ≠ (8 : Fin 32) →
          q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x4C (reg n) → CodeIn M P norm12Code → CodeIn M (nmBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (23 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (24 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (9 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x4C else 0x6A) (reg n') ∧
        CodeIn M' P norm12Code ∧ CodeIn M' (nmBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 xp (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (23 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (24 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (23 : Fin 32) → q ≠ (8 : Fin 32) →
          q ≠ (24 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, enp, exp, ed, ec, fr⟩ := nm_sub_iter (i := i) s hc hb hP hi hF hnp hxp hD
      sFB sFC (sDC.sub (by omega)) rsp rnp rxp rd rc ra2
    have eA : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    have eN : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFX.subR (by omega)) (sDX.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (nmBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P norm12Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, enp, exp, ed, ec, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i))) b).toNat *
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
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, enp, exp, ed, ec, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp rnp rxp rd rc ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 enp exp ed ec rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr qnp qxp qd qc => by
      rw [fr' q q0 q1 q2 q3 q4 qr qnp qxp qd qc, fr q q0 q1 q2 q3 q4 qr qnp qxp qd qc]⟩

/-- The function's region: `Uint<12>::select`'s 0x50 bytes below the frame,
which hold the word `is_nonzero` and `borrowing_sub` write, and the 0x60-byte
frame. -/
abbrev nmR (sp0 : Word) : Word := sp0 + 0xFFFFFF50

/-- The registers `norm` saves, at offsets from its `sp`. -/
abbrev nmPs : List (Fin 32 × Word) :=
  [(ra, 0x5C), ((8 : Fin 32), 0x58), ((9 : Fin 32), 0x54), ((18 : Fin 32), 0x50), ((19 : Fin 32), 0x4C),
   ((20 : Fin 32), 0x48), ((21 : Fin 32), 0x44), ((22 : Fin 32), 0x40), ((23 : Fin 32), 0x3C),
   ((24 : Fin 32), 0x38)]

/-- From 0x16 to the call at 0x24: keep the modulus, `f`'s sign, the value,
its sign byte, and the result pointer, and pass the magnitude to
`is_nonzero`. -/
def nmMov : List BInstr :=
  [.alu .add (23 : Fin 32) x0 a3, .alu .add (19 : Fin 32) x0 a2, .alu .add (22 : Fin 32) x0 a1,
   .lbu (20 : Fin 32) a1 0x30, .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 a1]

/-- From 0x2C to the call at 0x3C: keep `is_nonzero`'s answer and pass
`memset`'s arguments for the buffer at `sp + 8`. -/
def nmPre : List BInstr :=
  [.aluImm .and (21 : Fin 32) a0 0xFF, .aluImm .add a0 sp 0x8, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0,
   .aluImm .add (24 : Fin 32) sp 0x8]

/-- From 0x44 to 0x4A: the borrow, the count, and the magnitude's address. -/
def nmInit : List BInstr :=
  [.aluImm .add a2 x0 0x0, .aluImm .add (9 : Fin 32) x0 0xC, .alu .add (8 : Fin 32) x0 (22 : Fin 32)]

/-- From 0x6A to the call at 0x78: the choice, and `select`'s arguments. -/
def nmMk : List BInstr :=
  [.alu .xor a0 (20 : Fin 32) (19 : Fin 32), .alu .and a3 (21 : Fin 32) a0, .aluImm .add a2 sp 0x8,
   .alu .add a0 x0 (18 : Fin 32), .alu .add a1 x0 (22 : Fin 32)]

section
set_option maxRecDepth 20000
theorem nmSave_end : blockEnd norm12Code 2 (saveBlock nmPs) = some 0x16 := by decide
theorem nmMov_end : blockEnd norm12Code 0x16 nmMov = some 0x24 := by decide
theorem nmPre_end : blockEnd norm12Code 0x2C nmPre = some 0x3C := by decide
theorem nmInit_end : blockEnd norm12Code 0x44 nmInit = some 0x4A := by decide
theorem nmMk_end : blockEnd norm12Code 0x6A nmMk = some 0x78 := by decide
theorem nmRestore_end : blockEnd norm12Code 0x80 (restoreBlock nmPs) = some 0x94 := by decide
theorem nmPs_range : ∀ p ∈ nmPs, p.2.toNat % 4 = 0 ∧ 0x38 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x60 := by decide
theorem nmPs_sp : ∀ p ∈ nmPs, p.1 ≠ sp := by decide
end

/-- Where `norm` runs: its code and its callees', its region below `sp0`,
the result `out`, the value at `xp`, and the modulus at `np`, aligned and
apart from what each must not touch. -/
structure NmEnv (M : Word → BitVec 8) (P sp0 out xp np : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P norm12Code
  nz : CodeIn M (P + 0xFFFFFFE6) uint12IsNonzeroCode
  ref : CodeIn M (P + 0xFFFEF13C) uintRefIsNonzeroCode
  mset : CodeIn M (P + 0xCB6) memsetCode
  bsub : CodeIn M (nmBsub P) borrowingSubCode
  sel : CodeIn M (P + 0xFFFFF338) uintSelect12Code
  stub : CodeIn M (P + 0xD1E) memcpyStubCode
  body : CodeIn M (P + 0xD26) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xB0 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hxp : xp.toNat % 4 = 0
  hnp : np.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sSC : Sep (nmR sp0) 0xB0 P norm12Code.length
  sSZ : Sep (nmR sp0) 0xB0 (P + 0xFFFFFFE6) uint12IsNonzeroCode.length
  sSF : Sep (nmR sp0) 0xB0 (P + 0xFFFEF13C) uintRefIsNonzeroCode.length
  sSM : Sep (nmR sp0) 0xB0 (P + 0xCB6) memsetCode.length
  sSB : Sep (nmR sp0) 0xB0 (nmBsub P) borrowingSubCode.length
  sSL : Sep (nmR sp0) 0xB0 (P + 0xFFFFF338) uintSelect12Code.length
  sSU : Sep (nmR sp0) 0xB0 (P + 0xD1E) memcpyStubCode.length
  sSY : Sep (nmR sp0) 0xB0 (P + 0xD26) memcpyBodyCode.length
  sOC : Sep out 48 P norm12Code.length
  sOL : Sep out 48 (P + 0xFFFFF338) uintSelect12Code.length
  sOY : Sep out 48 (P + 0xD26) memcpyBodyCode.length
  sOS : Sep out 48 (nmR sp0) 0xB0
  sXS : Sep xp 49 (nmR sp0) 0xB0
  sNS : Sep np 48 (nmR sp0) 0xB0

/-- The registers `norm` leaves as they were. -/
def nmKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 10, 11, 12, 13, 14, 15, 16, 17]

/-- What `SignedInt<12>::norm` returns for a value with sign `σ` and
magnitude `X`, `f`'s sign `fs`, and the modulus `p`: the magnitude, or
`p - X` modulo 2^384 when the signs differ and `X` isn't zero. -/
def normVal (σ fs X p : Nat) : Nat := if σ ≠ fs ∧ X ≠ 0 then (p + 2 ^ 384 - X) % 2 ^ 384 else X

set_option maxRecDepth 60000 in
set_option maxHeartbeats 16000000 in
set_option exponentiation.threshold 400 in
/-- **The compiled `SignedInt<12>::norm`**, called with the result pointer
`out`, the value at `xp` (12 limbs and a sign byte 0 or 1 at `xp + 0x30`),
`f`'s sign 0 or 1, and the modulus at `np`: `out` gets `normVal` of them. -/
theorem norm12_correct (m : Machine) {P sp0 out xp np retAddr : Word} (env : NmEnv m.mem P sp0 out xp np)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (ha2 : reg m a2 = 0 ∨ reg m a2 = 1) (ha3 : reg m a3 = np) (hσ : (m.mem (xp + 0x30)).toNat ≤ 1)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, nmKeep q = true → reg m' q = reg m q) ∧
      accV m'.mem out 12 =
        normVal (m.mem (xp + 0x30)).toNat (reg m a2).toNat (accV m.mem xp 12) (accV m.mem np 12) ∧
      ∀ x, Sep (nmR sp0) 0xB0 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R, hR⟩ : ∃ R, nmR sp0 = R := ⟨_, rfl⟩
  have sSC := env.sSC; have sSZ := env.sSZ; have sSF := env.sSF; have sSM := env.sSM; have sSB := env.sSB
  have sSL := env.sSL; have sSU := env.sSU; have sSY := env.sSY; have sOS := env.sOS; have sXS := env.sXS
  have sNS := env.sNS
  rw [hR] at sSC sSZ sSF sSM sSB sSL sSU sSY sOS sXS sNS ⊢
  have hRw : R.toNat + 0xB0 = sp0.toNat := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFF50 : Word).toNat = 4294967120 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hRa : R.toNat % 4 = 0 := by rw [← hR]; exact aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  obtain ⟨F, hF⟩ : ∃ F, R + BitVec.ofNat 32 0x50 = F := ⟨_, rfl⟩
  have eF : sp0 + 0xFFFFFFA0 = F := by rw [← hF, ← hR, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := hF ▸ aligned_add hRa (by decide)
  have hFw : F.toNat + 0x60 = sp0.toNat := by
    rw [← hF, BitVec.toNat_add, ofNat_tn (by decide)]; omega
  have eFR : F + 0xFFFFFFFC = R + BitVec.ofNat 32 0x4C := by rw [← hF, BitVec.add_assoc]; rfl
  have eFS : F + 0xFFFFFFB0 = R := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero R
  obtain ⟨D, hD⟩ : ∃ D, F + BitVec.ofNat 32 8 = D := ⟨_, rfl⟩
  have eDR : D = R + BitVec.ofNat 32 0x58 := by rw [← hD, ← hF, add_ofNat_assoc]
  have hDa : D.toNat % 4 = 0 := hD ▸ aligned_add hFa (by decide)
  have hDw : D.toNat + 48 + 0x28 = sp0.toNat := by
    rw [← hD, BitVec.toNat_add, ofNat_tn (by decide)]; omega
  have toF : ∀ {b : Word} {k : Nat} {c l : Nat}, c + l ≤ 0x60 → Sep R 0xB0 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun {b k c l} h hs => by
    rw [← hF, add_ofNat_assoc]; exact hs.sub (by omega)
  have toF0 : ∀ {b : Word} {k : Nat} {l : Nat}, l ≤ 0x60 → Sep R 0xB0 b k → Sep F l b k := fun {b k l} h hs => by
    have := toF (c := 0) (l := l) (by omega) hs; rwa [add_ofNat_zero] at this
  have toD : ∀ {b : Word} {k : Nat}, Sep R 0xB0 b k → Sep D 48 b k := fun {b k} hs => by
    rw [← hD]; exact toF (by decide) hs
  have toG : ∀ {b : Word} {k : Nat}, Sep R 0xB0 b k → Sep (F + 0xFFFFFFFC) 4 b k := fun {b k} hs => by
    rw [eFR]; exact hs.sub (by decide)
  have toS : ∀ {b : Word} {k : Nat}, Sep R 0xB0 b k → Sep (F + 0xFFFFFFB0) 0x50 b k := fun {b k} hs => by
    rw [eFS]; have := hs.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep R 0xB0 b code.length → (∀ x, Sep R 0xB0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the prologue
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code nm12_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, eF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock nmPs) u1 env.code nmSave_end (saveBlock_ok _ nmPs _ fun p hp => by
    rw [sp1]
    have := nmPs_range p hp
    exact ⟨fr_al' hFa this.1, frm_sep' (toF0 (l := 0x60) (by decide) sSC) (by omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0)) nmPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep R 0xB0 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside nmPs fun p hp => frm_sep' (toF0 (l := 0x60) (by decide) hx) (by
      have := nmPs_range p hp; omega)
  have hslv : ∀ r o, (r, o) ∈ nmPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [nmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0) r := u2.regs
  have hσsv : Msv (xp + 0x30) = m.mem (xp + 0x30) :=
    frSv _ (by rw [show xp + 0x30 = xp + BitVec.ofNat 32 48 from rfl]; exact (sXS.sub (c := 48) (l := 1) (by decide)).symm)
  have sXS48 : Sep xp 48 R 0xB0 := by have := sXS.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨m3, c3, u3⟩ := St.block nmMov u2.self (cIn env.code sSC frSv) nmMov_end
    (by simp [BlockOk, BInstr.ok, nmMov])
  simp only [runBlock, BInstr.run, nmMov] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  obtain ⟨fs, hfs⟩ : ∃ fs, reg m a2 = fs := ⟨_, rfl⟩
  have v3 : reg m3 sp = F ∧ reg m3 23 = np ∧ reg m3 19 = fs ∧ reg m3 22 = xp ∧
      reg m3 20 = (m.mem (xp + 0x30)).zeroExtend 32 ∧ reg m3 18 = out ∧ reg m3 a0 = xp := by
    simp +decide only [g3, upd_app, ↓reduceIte, r2]
    simp only [ev_add, hsp, eF, ha0, ha1, ha3, hfs, zw]
    exact ⟨trivial, trivial, trivial, trivial, congrArg (BitVec.zeroExtend 32) hσsv, trivial, trivial⟩
  obtain ⟨v3sp, v323, v319, v322, v320, v318, v3a0⟩ := v3
  have k3 : ∀ q : Fin 32, q ≠ sp → q ≠ 23 → q ≠ 19 → q ≠ 22 → q ≠ 20 → q ≠ 18 → q ≠ a0 → reg m3 q = reg m q :=
    fun q h1 h2 h3 h4 h5 h6 h7 => by
      rw [g3]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h2, h3, h4, h5, h6, h7, ite_false]; rw [r2]; simp only [upd_app, h0, h1, ite_false]
  -- `is_nonzero`
  have hcS := cIn env.code sSC frSv
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS nm12_at_24 nm12_at_28
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFFE6 (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have sp4 : reg m4 sp = F := by rw [r4 sp (by decide), v3sp]
  have eW : P + BitVec.ofNat 32 0xFFFFFFE6 + 0xFFFEF156 = P + 0xFFFEF13C := by rw [BitVec.add_assoc]; rfl
  have eG4 : reg m4 sp + 0xFFFFFFFC = R + BitVec.ofNat 32 0x4C := by rw [sp4, eFR]
  obtain ⟨m5, c5, pc5, a05, k5, f5⟩ := uint12IsNonzero_correct m4 (even_at P env.hP 0xFFFFFFE6 (by decide))
    (by rw [mem4]; exact cIn env.nz sSZ frSv) (by rw [mem4, eW]; exact cIn env.ref sSF frSv) pc4
    (by rw [r4 a0 (by decide), v3a0]) env.hxp (by rw [sp4]; exact hFa)
    (by rw [eG4, eW]; exact sSF.sub (by decide)) (by rw [regs4]; simp +decide [upd])
    (even_clear _ (even_at P env.hP (0x24 + 8) (by decide)))
  rw [mem4] at a05 f5
  rw [eG4] at f5
  have frX : ∀ i, i < 12 → memLoad32 Msv (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * i)) :=
    fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]; exact frSv _ (sXS48.sub (c := 4 * i + q) (l := 1) (by omega)).symm
  obtain ⟨nz, hnz⟩ : ∃ nz : Word,
      (if ∀ i : Nat, i < 12 → memLoad32 Msv (xp + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) = nz := ⟨_, rfl⟩
  rw [hnz] at a05
  have fr5 : ∀ x, Sep R 0xB0 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [f5 x (hx.sub (by decide)), frSv x hx]
  have hnz01 : nz = 0 ∨ nz = 1 := by rw [← hnz]; split <;> simp
  have k5' : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ t1 → q ≠ ra → reg m5 q = reg m3 q :=
    fun q h0 h1 h2 h3 ht hr => by rw [k5 q h0 h1 h2 h3 ht, r4 q hr]
  have u5 : St m5.mem P m5 0x2C (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  -- the buffer
  obtain ⟨m6, c6, u6⟩ := St.block nmPre u5 (cIn env.code sSC fr5) nmPre_end (by simp [BlockOk, BInstr.ok, nmPre])
  simp only [runBlock, BInstr.run, nmPre] at u6
  have g6 : ∀ r, reg m6 r = _ := u6.regs
  have sp5 : reg m5 sp = F := by
    rw [k5' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v3sp]
  have v6 : reg m6 sp = F ∧ reg m6 21 = nz ∧ reg m6 a0 = D ∧ reg m6 a2 = BitVec.ofNat 32 (4 * 12) ∧
      reg m6 a1 = 0 ∧ reg m6 24 = D := by
    simp +decide only [g6, upd_app, ↓reduceIte]
    simp only [ev_add, sp5, a05, ← hD]
    refine ⟨trivial, ?_, ?_, trivial, trivial, ?_⟩ <;> try rfl
    rcases hnz01 with h | h <;> rw [h] <;> rfl
  obtain ⟨v6sp, v621, v6a0, v6a2, v6a1, v624⟩ := v6
  have k6 : ∀ q : Fin 32, q ≠ 21 → q ≠ a0 → q ≠ a2 → q ≠ a1 → q ≠ 24 → reg m6 q = reg m5 q :=
    fun q h1 h2 h3 h4 h5 => by
      rw [g6]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact u5.zero.symm
      simp only [upd_app, h0, h1, h2, h3, h4, h5, ite_false]
  have hDw48 : D.toNat + 4 * 12 < 2 ^ 32 := by have := sp0.isLt; omega
  obtain ⟨m7, c7, u7, a07, k7⟩ := u6.self.memsetW (B := P + 0xCB6) (w := 12) (dst := D)
    (even_at P env.hP 0xCB6 (by decide)) (cIn env.code sSC fr5) (cIn env.mset sSM fr5) nm12_at_3c nm12_at_40
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x3C + 8) (by decide)) (by decide) hDw48
    (by decide) hDa (toD sSM) v6a0 v6a1 v6a2
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords m5.mem D 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u7
  have frZ : ∀ x, Sep R 0xB0 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillWords_outside (dst := D) 12 (toD hx), fr5 x hx]
  have hcZ := cIn env.code sSC frZ
  obtain ⟨m8, c8, u8⟩ := St.block nmInit u7 hcZ nmInit_end (by simp [BlockOk, BInstr.ok, nmInit])
  simp only [runBlock, BInstr.run, nmInit] at u8
  have g8 : ∀ r, reg m8 r = _ := u8.regs
  have z7 : reg m7 x0 = 0 := u7.zero
  have k76 : ∀ q : Fin 32, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m7 q = reg m6 q := k7
  have r722 : reg m7 22 = xp := by
    rw [k76 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k5' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v322]
  have v8 : reg m8 a2 = 0 ∧ reg m8 9 = BitVec.ofNat 32 (12 - 0) ∧ reg m8 8 = xp := by
    simp +decide only [g8, upd_app, ↓reduceIte]
    simp only [z7, ev_add, r722]
    exact ⟨BitVec.zero_add _, trivial, BitVec.zero_add _⟩
  obtain ⟨v8a2, v89, v88⟩ := v8
  have k8 : ∀ q : Fin 32, q ≠ a2 → q ≠ 9 → q ≠ 8 → reg m8 q = reg m7 q := fun q h1 h2 h3 => by
    rw [g8]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact z7.symm
    simp only [upd_app, h0, h1, h2, h3, ite_false]
  obtain ⟨m9, d9, u9⟩ := u8.self.notTaken hcZ 0x4C nm12_at_4a (by decide) (by rw [v89, u8.self.zero]; decide)
  have k9 : ∀ q, reg m9 q = reg m8 q := u9.regs
  -- the subtraction
  have sFD : Sep (F + 0xFFFFFFFC) 4 D 48 := by
    rw [eFR, eDR]; exact sep_offsets R (.inl (by omega)) (by omega) (by omega)
  have r9sp : reg m9 sp = F := by
    rw [k9, k8 _ (by decide) (by decide) (by decide), k76 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v6sp]
  have r923 : reg m9 23 = np := by
    rw [k9, k8 _ (by decide) (by decide) (by decide), k76 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k5' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v323]
  have r924 : reg m9 24 = D := by
    rw [k9, k8 _ (by decide) (by decide) (by decide), k76 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v624]
  obtain ⟨n10, M10, c10, u10, hc10, hf10, hb10, hv10, sp10, k10⟩ :=
    nm_sub_loop (np := np) (xp := xp) (D := D) (M0 := Mz) env.hP hFa env.hnp env.hxp hDa (by omega)
      (toG sNS.symm) (toG sXS48.symm) sFD (toD sNS.symm) (toD sXS48.symm) (toG sSB) (toG sSC)
      (toD sSB) (toD sSC)
      11 0 rfl u9.self hcZ (cIn env.bsub sSB frZ) (fun _ _ _ => rfl) (.inl rfl) (by simp [accV, maskBit])
      r9sp (by rw [r923, Nat.mul_zero, add_ofNat_zero]) (by rw [k9, v88, Nat.mul_zero, add_ofNat_zero])
      (by rw [r924, Nat.mul_zero, add_ofNat_zero]) (by rw [k9, v89]) (by rw [k9, v8a2])
  have nZ : accV Mz np 12 = accV m.mem np 12 := accV_congr 12 fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc]; exact frZ _ (sNS.sub (c := 4 * i + q) (l := 1) (by omega)).symm
  have xZ : accV Mz xp 12 = accV m.mem xp 12 := accV_congr 12 fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc]; exact frZ _ (sXS48.sub (c := 4 * i + q) (l := 1) (by omega)).symm
  rw [nZ, xZ] at hv10
  -- the choice
  have kA : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ 23 → q ≠ 8 → q ≠ 24 →
      q ≠ 9 → q ≠ t1 → q ≠ 21 → q ≠ a5 → q ≠ a6 → q ≠ 22 → reg n10 q = reg m3 q :=
    fun q h0 h1 h2 h3 h4 hr h23 h8 h24 h9 ht h21 h5 h6 h22 => by
      rw [k10 q h0 h1 h2 h3 h4 hr h23 h8 h24 h9, k9, k8 q h2 h9 h8, k76 q h2 h3 h4 h5 h6 hr,
        k6 q h21 h0 h2 h1 h24, k5' q h0 h1 h2 h3 ht hr]
  have r1020 : reg n10 20 = (m.mem (xp + 0x30)).zeroExtend 32 := by
    rw [kA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v320]
  have r1019 : reg n10 19 = fs := by
    rw [kA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v319]
  have r1018 : reg n10 18 = out := by
    rw [kA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v318]
  have r1021 : reg n10 21 = nz := by
    rw [k10 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k9, k8 _ (by decide) (by decide) (by decide),
      k76 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v621]
  have r1022 : reg n10 22 = xp := by
    rw [k10 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k9, k8 _ (by decide) (by decide) (by decide), r722]
  obtain ⟨n11, c11, u11⟩ := St.block nmMk u10 hc10 nmMk_end (by simp [BlockOk, BInstr.ok, nmMk])
  simp only [runBlock, BInstr.run, nmMk] at u11
  have g11 : ∀ r, reg n11 r = _ := u11.regs
  have z10 : reg n10 x0 = 0 := u10.zero
  obtain ⟨c, hc⟩ : ∃ c : Word, aluEval .and nz (aluEval .xor ((m.mem (xp + 0x30)).zeroExtend 32) fs) = c :=
    ⟨_, rfl⟩
  have hσ01 : m.mem (xp + 0x30) = 0 ∨ m.mem (xp + 0x30) = 1 := by
    have h := (m.mem (xp + 0x30)).isLt
    rcases (by omega : (m.mem (xp + 0x30)).toNat = 0 ∨ (m.mem (xp + 0x30)).toNat = 1) with h' | h'
    · exact .inl (BitVec.eq_of_toNat_eq h')
    · exact .inr (BitVec.eq_of_toNat_eq h')
  have hfs01 : fs = 0 ∨ fs = 1 := by rw [← hfs]; exact ha2
  have hcc : c = 0 ∨ c = 1 := by
    rw [← hc]; rcases hnz01 with h | h <;> rcases hσ01 with h' | h' <;> rcases hfs01 with h'' | h'' <;>
      rw [h, h', h''] <;> decide
  have hc1 : c = 1 ↔ nz = 1 ∧ (m.mem (xp + 0x30)).toNat ≠ fs.toNat := by
    rw [← hc]; rcases hnz01 with h | h <;> rcases hσ01 with h' | h' <;> rcases hfs01 with h'' | h'' <;>
      rw [h, h', h''] <;> decide
  have v11 : reg n11 a3 = c ∧ reg n11 a2 = D ∧ reg n11 a0 = out ∧ reg n11 a1 = xp ∧ reg n11 sp = F := by
    simp +decide only [g11, upd_app, ↓reduceIte]
    simp only [ev_add, zw, sp10, r1018, r1019, r1020, r1021, r1022, hc, ← hD]
    exact ⟨trivial, rfl, trivial, trivial, trivial⟩
  obtain ⟨v11a3, v11a2, v11a0, v11a1, v11sp⟩ := v11
  have k11 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n11 q = reg n10 q := fun q h1 h2 h3 h4 => by
    rw [g11]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact z10.symm
    simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  -- `select`
  obtain ⟨n12, c12, pc12, mem12, regs12⟩ := u11.self.callRa hc10 nm12_at_78 nm12_at_7c (cb := P + 0xFFFFF338)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF338 (by decide))
  have r12 := PEnv.reg1 regs12 u11.self.zero
  have sp12 : reg n12 sp = F := by rw [r12 _ (by decide), v11sp]
  have fr10 : ∀ x, Sep R 0xB0 x 1 → M10 x = m.mem x := fun x hx => by
    have h1 : Sep (F + 0xFFFFFFFC) 4 x 1 := toG hx
    have h2 : Sep D 48 x 1 := toD hx
    rw [hf10 x h1 h2, frZ x hx]
  have eSel : reg n12 sp + 0xFFFFFFB0 = R := by rw [sp12, eFS]
  have eM : P + 0xFFFFF338 + 0x197E = P + 0xCB6 := by rw [BitVec.add_assoc]; rfl
  have eU : P + 0xFFFFF338 + 0x19E6 = P + 0xD1E := by rw [BitVec.add_assoc]; rfl
  have eB : P + 0xFFFFF338 + 0x19EE = P + 0xD26 := by rw [BitVec.add_assoc]; rfl
  have hF50 : 0x50 ≤ F.toNat := by rw [← hF, BitVec.toNat_add, ofNat_tn (by decide)]; omega
  have SE : SelEnv n12.mem (P + 0xFFFFF338) (reg n12 sp) out xp D := by
    rw [mem12]
    refine ⟨even_at P env.hP 0xFFFFF338 (by decide), cIn env.sel sSL fr10, by rw [eM]; exact cIn env.mset sSM fr10,
      by rw [eU]; exact cIn env.stub sSU fr10, by rw [eB]; exact cIn env.body sSY fr10,
      by rw [sp12]; exact hFa, by rw [sp12]; exact hF50, env.hout, env.hxp, hDa, env.hwo, ?_, ?_, ?_, ?_, ?_,
      env.sOL, by rw [eB]; exact env.sOY, ?_, ?_⟩
    · rw [eSel]; have := sSL.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this
    · rw [eSel, eM]; have := sSM.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this
    · rw [eSel, eU]; have := sSU.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this
    · rw [eSel, eB]; have := sSY.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this
    · rw [eSel]; exact (sOS.subR (c := 0) (l := 0x50) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
    · rw [eSel]; exact (sXS48.subR (c := 0) (l := 0x50) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
    · rw [eSel, eDR]
      have := sep_offsets R (c := 0x58) (n := 48) (d := 0) (k := 0x50) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
  obtain ⟨n13, c13, pc13, sp13, w13, mem13, k13⟩ := uintSelect12_correct n12 SE pc12
    (by rw [r12 _ (by decide), v11a0]) (by rw [r12 _ (by decide), v11a1]) (by rw [r12 _ (by decide), v11a2])
    (by rw [r12 _ (by decide), v11a3]) hcc (by rw [regs12]; simp +decide [upd])
    (even_clear _ (even_at P env.hP (0x78 + 8) (by decide)))
  rw [eSel] at mem13
  rw [sp12] at sp13
  rw [mem12] at w13 mem13
  have frF : ∀ x, Sep R 0xB0 x 1 → Sep out 48 x 1 → n13.mem x = m.mem x := fun x hx ho => by
    rw [mem13 x (by have := hx.sub (c := 0) (l := 0x50) (by decide); rwa [add_ofNat_zero] at this) ho, fr10 x hx]
  have hcF : CodeIn n13.mem P norm12Code := fun i hi => by
    rw [frF _ (sSC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have u13 : St n13.mem P n13 0x80 (reg n13) := ⟨pc13, rfl, fun _ => rfl⟩
  have k13' : ∀ q : Fin 32, selKeep q = true → q ≠ ra → reg n13 q = reg n11 q := fun q hq hr => by
    rw [k13 q hq, r12 q hr]
  -- the epilogue
  obtain ⟨n14, c14, u14⟩ := St.block (restoreBlock nmPs) u13 hcF nmRestore_end
    (restoreBlock_ok n13.mem _ nmPs (reg n13) sp13 nmPs_sp fun p hp => fr_al' hFa (nmPs_range p hp).1)
  simp only [restoreBlock_run n13.mem _ nmPs (reg n13) sp13 nmPs_sp] at u14
  obtain ⟨n15, d15, u15⟩ := u14.aluImm hcF nm12_at_94 (off' := 0x96) (by decide)
  obtain ⟨n16, d16, pc16, mem16, regs16⟩ := u15.jalr hcF nm12_at_96
  have slot : ∀ r o, (r, o) ∈ nmPs → memLoad32 n13.mem (F + o) = reg m r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := nmPs_range (r, o) h
    dsimp only at ho1 ho2
    have e : ∀ t, F + o + BitVec.ofNat 32 t = R + BitVec.ofNat 32 (0x50 + o.toNat + t) := fun t => by
      rw [← hF]; conv => lhs; rw [← ofNat_toNat_self o]
      rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]
    have h1 : memLoad32 n13.mem (F + o) = memLoad32 Msv (F + o) := memLoad32_congr fun t ht => by
      have sS : Sep R 0x50 (F + o + BitVec.ofNat 32 t) 1 := by
        rw [e]
        have := sep_offsets R (c := 0) (n := 0x50) (d := 0x50 + o.toNat + t) (k := 1) (.inl (by omega)) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at this
      have sO : Sep out 48 (F + o + BitVec.ofNat 32 t) 1 := by rw [e]; exact sOS.subR (by omega)
      have sG : Sep (F + 0xFFFFFFFC) 4 (F + o + BitVec.ofNat 32 t) 1 := by
        rw [e, eFR]; exact sep_offsets R (.inl (by omega)) (by omega) (by omega)
      have sDd : Sep D 48 (F + o + BitVec.ofNat 32 t) 1 := by
        rw [e, eDR]; exact sep_offsets R (.inl (by omega)) (by omega) (by omega)
      have sG' : Sep (R + BitVec.ofNat 32 0x4C) 4 (F + o + BitVec.ofNat 32 t) 1 := by rwa [eFR] at sG
      rw [mem13 _ sS sO, hf10 _ sG sDd, ← hMz, fillWords_outside (dst := D) 12 sDd, f5 _ sG']
    rw [h1]
    exact hslv r o h
  have rest : ∀ r o, (r, o) ∈ nmPs → restoreRegs n13.mem F (reg n13) nmPs r = reg m r := fun r o h => by
    have hs := slot
    simp only [nmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hs _ _ (by decide)
  have rsp14 : restoreRegs n13.mem F (reg n13) nmPs sp = F := by rw [restoreRegs_sp _ _ _ _ nmPs_sp]; exact sp13
  have eSp : F + 0x60 = sp0 := by rw [← eF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hra14 : restoreRegs n13.mem F (reg n13) nmPs ra = retAddr := by rw [rest ra 0x5C (by decide), hra]
  refine ⟨n16, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (.cons d9
    (c10.trans (c11.trans (c12.trans (c13.trans (c14.trans (.cons d15 (.single d16))))))))))))))),
    ?_, ?_, ?_, ?_, fun x hx ho => by rw [mem16, frF x hx ho]⟩
  · rw [pc16]; simp +decide only [upd_app, ↓reduceIte]; rw [hra14, add_lit_zero, hret]
  · rw [regs16]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp14, ev_add, eSp]
  · intro q hq
    rw [regs16]
    by_cases hsp' : q = sp
    · subst hsp'; simp +decide only [upd_app, ↓reduceIte]; rw [rsp14, ev_add, eSp, hsp]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, hsp', ite_false]
    by_cases hps : q.val ∈ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hps
      rcases hps with h | h | h | h | h | h | h | h | h | h <;> rw [show q = ⟨_, by decide⟩ from Fin.ext h]
      · exact rest ra 0x5C (by decide)
      · exact rest 8 0x58 (by decide)
      · exact rest 9 0x54 (by decide)
      · exact rest 18 0x50 (by decide)
      · exact rest 19 0x4C (by decide)
      · exact rest 20 0x48 (by decide)
      · exact rest 21 0x44 (by decide)
      · exact rest 22 0x40 (by decide)
      · exact rest 23 0x3C (by decide)
      · exact rest 24 0x38 (by decide)
    have nq : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24] → q ≠ w := fun w hw e => hps (e ▸ hw)
    have nk : ∀ w : Fin 32, w.val ∈ [5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → q ≠ w := fun w hw e => by
      subst e; simp only [nmKeep] at hq; exact absurd hw (by simpa using hq)
    have hsk : selKeep q = true := by
      simp only [selKeep]; simp only [nmKeep] at hq; exact hq
    simp only [restoreRegs, upd_app, h0, nq ra (by decide), nq 8 (by decide), nq 9 (by decide), nq 18 (by decide),
      nq 19 (by decide), nq 20 (by decide), nq 21 (by decide), nq 22 (by decide), nq 23 (by decide),
      nq 24 (by decide), ite_false]
    rw [k13' q hsk (nq ra (by decide)),
      k11 q (nk a0 (by decide)) (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)),
      kA q (nk a0 (by decide)) (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)) (nk a4 (by decide))
        (nq ra (by decide)) (nq 23 (by decide)) (nq 8 (by decide)) (nq 24 (by decide)) (nq 9 (by decide))
        (nk t1 (by decide)) (nq 21 (by decide)) (nk a5 (by decide)) (nk a6 (by decide)) (nq 22 (by decide)),
      k3 q hsp' (nq 23 (by decide)) (nq 19 (by decide)) (nq 22 (by decide)) (nq 20 (by decide)) (nq 18 (by decide))
        (nk a0 (by decide))]
  · have hval : accV n13.mem out 12 = if c = 1 then accV M10 D 12 else accV m.mem xp 12 := by
      by_cases h1 : c = 1
      · rw [ite_eq_left h1]
        exact accV_congr2 12 fun j hj => by rw [w13 j hj, ite_eq_left h1]
      · rw [ite_eq_right h1]
        exact accV_congr2 12 fun j hj => by
          rw [w13 j hj, ite_eq_right h1]
          exact memLoad32_congr fun q hq => by
            rw [add_ofNat_assoc]; exact fr10 _ (sXS48.sub (c := 4 * j + q) (l := 1) (by omega)).symm
    rw [mem16, hval]
    have hnzX : nz = 1 ↔ accV m.mem xp 12 ≠ 0 := by
      rw [← hnz]
      constructor
      · intro h hX
        rw [ite_eq_left fun i hi => by rw [frX i hi]; exact accV_eq_zero 12 hX i hi] at h
        exact absurd h (by decide)
      · intro hX
        by_cases hall : ∀ i : Nat, i < 12 → memLoad32 Msv (xp + BitVec.ofNat 32 (4 * i)) = 0
        · exact absurd (accV_zero 12 fun i hi => by rw [← frX i hi]; exact hall i hi) hX
        · rw [ite_eq_right hall]
    simp only [normVal, hfs]
    by_cases hC : c = 1
    · obtain ⟨h1, h2⟩ := hc1.mp hC
      rw [ite_eq_left hC, ite_eq_left ⟨h2, hnzX.mp h1⟩]
      exact ng_res (accV_lt _ _ 12) (accV_lt _ _ 12) (accV_lt _ _ 12) (mb_le1 _) hv10
    · rw [ite_eq_right hC]
      by_cases hX : (m.mem (xp + 0x30)).toNat ≠ fs.toNat ∧ accV m.mem xp 12 ≠ 0
      · exact absurd (hc1.mpr ⟨hnzX.mpr hX.2, hX.1⟩) hC
      · rw [ite_eq_right hX]

end C3.RV32
