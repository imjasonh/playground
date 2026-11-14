import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.P384Add

/-!
# `ConstMontyForm<p384>::neg`, as compiled

`crypto_bigint`'s `ConstMontyForm::neg` for the P-384 field computes `p - x`
limb by limb with `borrowing_sub` into a 48-byte buffer, then zeroes the
buffer when `x` is zero, through a byte of the frame, and copies it out.
`Uint<12>::is_nonzero`, which it calls first, passes the limb count to
`UintRef::is_nonzero`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem ng_at_0 : fetchRel p384NegCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem ng_at_2 : fetchRel p384NegCode 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem ng_at_4 : fetchRel p384NegCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem ng_at_6 : fetchRel p384NegCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x44, 2) := by decide
theorem ng_at_8 : fetchRel p384NegCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x40, 2) := by decide
theorem ng_at_a : fetchRel p384NegCode 0xA = some (.store .sw sp (19 : Fin 32) 0x3C, 2) := by decide
theorem ng_at_c : fetchRel p384NegCode 0xC = some (.store .sw sp (20 : Fin 32) 0x38, 2) := by decide
theorem ng_at_e : fetchRel p384NegCode 0xE = some (.store .sw sp (21 : Fin 32) 0x34, 2) := by decide
theorem ng_at_10 : fetchRel p384NegCode 0x10 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem ng_at_12 : fetchRel p384NegCode 0x12 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem ng_at_14 : fetchRel p384NegCode 0x14 = some (.alu .add a0 x0 a1, 2) := by decide
theorem ng_at_16 : fetchRel p384NegCode 0x16 = some (.auipc ra 0x11000, 4) := by decide
theorem ng_at_1a : fetchRel p384NegCode 0x1A = some (.jalr ra ra 0x286, 4) := by decide
theorem ng_at_1e : fetchRel p384NegCode 0x1E = some (.aluImm .and (19 : Fin 32) a0 0xFF, 4) := by decide
theorem ng_at_22 : fetchRel p384NegCode 0x22 = some (.alu .add a0 x0 sp, 2) := by decide
theorem ng_at_24 : fetchRel p384NegCode 0x24 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem ng_at_28 : fetchRel p384NegCode 0x28 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem ng_at_2a : fetchRel p384NegCode 0x2A = some (.alu .add (21 : Fin 32) x0 sp, 2) := by decide
theorem ng_at_2c : fetchRel p384NegCode 0x2C = some (.auipc ra 0x12000, 4) := by decide
theorem ng_at_30 : fetchRel p384NegCode 0x30 = some (.jalr ra ra 0xFFFFFF40, 4) := by decide
theorem ng_at_34 : fetchRel p384NegCode 0x34 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem ng_at_36 : fetchRel p384NegCode 0x36 = some (.lui (9 : Fin 32) 0x3FCC5000, 4) := by decide
theorem ng_at_3a : fetchRel p384NegCode 0x3A = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFC8C, 4) := by decide
theorem ng_at_3e : fetchRel p384NegCode 0x3E = some (.aluImm .add (8 : Fin 32) x0 0xC, 2) := by decide
theorem ng_at_40 : fetchRel p384NegCode 0x40 = some (.branch .beq (8 : Fin 32) x0 0x20, 2) := by decide
theorem ng_at_42 : fetchRel p384NegCode 0x42 = some (.load .lw a0 (9 : Fin 32) 0x0, 2) := by decide
theorem ng_at_44 : fetchRel p384NegCode 0x44 = some (.load .lw a1 (20 : Fin 32) 0x0, 4) := by decide
theorem ng_at_48 : fetchRel p384NegCode 0x48 = some (.auipc ra 0x0, 4) := by decide
theorem ng_at_4c : fetchRel p384NegCode 0x4C = some (.jalr ra ra 0xFFFFFA5E, 4) := by decide
theorem ng_at_50 : fetchRel p384NegCode 0x50 = some (.alu .add a2 x0 a1, 2) := by decide
theorem ng_at_52 : fetchRel p384NegCode 0x52 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem ng_at_54 : fetchRel p384NegCode 0x54 = some (.store .sw (21 : Fin 32) a0 0x0, 4) := by decide
theorem ng_at_58 : fetchRel p384NegCode 0x58 = some (.aluImm .add (20 : Fin 32) (20 : Fin 32) 0x4, 2) := by decide
theorem ng_at_5a : fetchRel p384NegCode 0x5A = some (.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x4, 2) := by decide
theorem ng_at_5c : fetchRel p384NegCode 0x5C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem ng_at_5e : fetchRel p384NegCode 0x5E = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFE4, 2) := by decide
theorem ng_at_60 : fetchRel p384NegCode 0x60 = some (.aluImm .xor a0 (19 : Fin 32) 0x1, 4) := by decide
theorem ng_at_64 : fetchRel p384NegCode 0x64 = some (.alu .add a1 x0 sp, 2) := by decide
theorem ng_at_66 : fetchRel p384NegCode 0x66 = some (.aluImm .add a2 x0 0xC, 2) := by decide
theorem ng_at_68 : fetchRel p384NegCode 0x68 = some (.aluImm .add a3 sp 0x33, 4) := by decide
theorem ng_at_6c : fetchRel p384NegCode 0x6C = some (.branch .beq a2 x0 0x18, 2) := by decide
theorem ng_at_6e : fetchRel p384NegCode 0x6E = some (.store .sb sp a0 0x33, 4) := by decide
theorem ng_at_72 : fetchRel p384NegCode 0x72 = some (.load .lw a4 a1 0x0, 2) := by decide
theorem ng_at_74 : fetchRel p384NegCode 0x74 = some (.load .lbu a5 sp 0x33, 4) := by decide
theorem ng_at_78 : fetchRel p384NegCode 0x78 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem ng_at_7a : fetchRel p384NegCode 0x7A = some (.alu .and a4 a4 a5, 2) := by decide
theorem ng_at_7c : fetchRel p384NegCode 0x7C = some (.store .sw a1 a4 0x0, 2) := by decide
theorem ng_at_7e : fetchRel p384NegCode 0x7E = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem ng_at_80 : fetchRel p384NegCode 0x80 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem ng_at_82 : fetchRel p384NegCode 0x82 = some (.branch .bne a2 x0 0xFFFFFFEC, 2) := by decide
theorem ng_at_84 : fetchRel p384NegCode 0x84 = some (.alu .add a1 x0 sp, 2) := by decide
theorem ng_at_86 : fetchRel p384NegCode 0x86 = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem ng_at_8a : fetchRel p384NegCode 0x8A = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem ng_at_8c : fetchRel p384NegCode 0x8C = some (.auipc ra 0x12000, 4) := by decide
theorem ng_at_90 : fetchRel p384NegCode 0x90 = some (.jalr ra ra 0xFFFFFF48, 4) := by decide
theorem ng_at_94 : fetchRel p384NegCode 0x94 = some (.load .lw ra sp 0x4C, 2) := by decide
theorem ng_at_96 : fetchRel p384NegCode 0x96 = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem ng_at_98 : fetchRel p384NegCode 0x98 = some (.load .lw (9 : Fin 32) sp 0x44, 2) := by decide
theorem ng_at_9a : fetchRel p384NegCode 0x9A = some (.load .lw (18 : Fin 32) sp 0x40, 2) := by decide
theorem ng_at_9c : fetchRel p384NegCode 0x9C = some (.load .lw (19 : Fin 32) sp 0x3C, 2) := by decide
theorem ng_at_9e : fetchRel p384NegCode 0x9E = some (.load .lw (20 : Fin 32) sp 0x38, 2) := by decide
theorem ng_at_a0 : fetchRel p384NegCode 0xA0 = some (.load .lw (21 : Fin 32) sp 0x34, 2) := by decide
theorem ng_at_a2 : fetchRel p384NegCode 0xA2 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem ng_at_a4 : fetchRel p384NegCode 0xA4 = some (.jalr x0 ra 0x0, 2) := by decide
theorem unz_at_0 : fetchRel uint12IsNonzeroCode 0x0 = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem unz_at_2 : fetchRel uint12IsNonzeroCode 0x2 = some (.auipc (6 : Fin 32) 0xFFFEF000, 4) := by decide
theorem unz_at_6 : fetchRel uint12IsNonzeroCode 0x6 = some (.jalr x0 (6 : Fin 32) 0x154, 4) := by decide
end

/-- **The compiled `Uint<12>::is_nonzero`** returns 0 when the 12 limbs at
`ptr` are all zero and 1 otherwise. It tail-calls `UintRef::is_nonzero`,
which writes the word below `sp`. -/
theorem uint12IsNonzero_correct (m : Machine) {base retAddr ptr : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base uint12IsNonzeroCode) (hu : CodeIn m.mem (base + 0xFFFEF156) uintRefIsNonzeroCode)
    (hpc : m.pc = base) (ha0 : reg m a0 = ptr) (hptr : ptr.toNat % 4 = 0) (hsp : (reg m sp).toNat % 4 = 0)
    (hsep : Sep (reg m sp + 0xFFFFFFFC) 4 (base + 0xFFFEF156) uintRefIsNonzeroCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if ∀ i : Nat, i < 12 → memLoad32 m.mem (ptr + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ t1 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc unz_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.auipc hc unz_at_2 (off' := 6) (by decide)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc unz_at_6
  have k : ∀ r, r ≠ a1 → r ≠ t1 → reg n3 r = reg m r := fun r h1 h2 => by
    rw [regs3, updz (upd_zero _ _ _) h2, updz hz h1]
  have pcU : n3.pc = base + 0xFFFEF156 := by
    rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
    rw [show base + BitVec.ofNat 32 2 + 0xFFFEF000 + 0x154 = base + 0xFFFEF156 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at base hP 0xFFFEF156 (by decide))
  have sp3 : reg n3 sp = reg m sp := k sp (by decide) (by decide)
  obtain ⟨m4, c4, pc4, a04, k4, f4⟩ := uintRefIsNonzero_correct n3 (len := 12) (by rw [mem3]; exact hu) pcU
    (by rw [k a0 (by decide) (by decide), ha0])
    (by rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]; rfl) (by decide) hptr
    (by rw [sp3]; exact hsp) (by rw [sp3]; exact hsep) (by rw [k ra (by decide) (by decide), hra]) hret
  rw [mem3] at a04 f4
  refine ⟨m4, .cons d1 (.cons d2 (.cons d3 c4)), pc4, a04, fun r h0 h1 h2 h3 ht => ?_, fun x hx => ?_⟩
  · rw [k4 r h0 h1 h2 h3, k r h1 ht]
  · rw [f4 x (by rw [sp3]; exact hx)]

/-- `borrowing_sub`'s offset from `neg`. -/
abbrev ngBsub (P : Word) : Word := P + 0xFFFFFAA6

/-- The end of a subtraction round, from 0x50: keep the borrow, store the
difference, and advance the pointers and the count. -/
def ngSubTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4, .sw (21 : Fin 32) a0 0,
   .aluImm .add (20 : Fin 32) (20 : Fin 32) 4, .aluImm .add (21 : Fin 32) (21 : Fin 32) 4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem ngSubTail_end : blockEnd p384NegCode 0x50 ngSubTail = some 0x5E := by decide
end

set_option maxRecDepth 20000 in
theorem ngSubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock ngSubTail (M, f)).1 = memStore32 M (f (21 : Fin 32) + 0) (f a0) ∧
    (runBlock ngSubTail (M, f)).2 a2 = f a1 ∧
    (runBlock ngSubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock ngSubTail (M, f)).2 (20 : Fin 32) = f (20 : Fin 32) + 4 ∧
    (runBlock ngSubTail (M, f)).2 (21 : Fin 32) = f (21 : Fin 32) + 4 ∧
    (runBlock ngSubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) → q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) →
      (runBlock ngSubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, ngSubTail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 q9 q20 q21 q8 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q9, q20, q21, q8]

theorem ngSubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (21 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (21 : Fin 32) + 0) 4 base len) :
    BlockOk base len ngSubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, ngSubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- **One round of the subtraction**, from 0x42: subtract limb `i` of `x`
and the borrow from limb `i` of the modulus at `np`, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem ng_sub_iter {M : Word → BitVec 8} {P F np xp D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x42 (reg n)) (hc : CodeIn M P p384NegCode) (hb : CodeIn M (ngBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 12) (hF : F.toNat % 4 = 0) (hnp : np.toNat % 4 = 0)
    (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (ngBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P p384NegCode.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P p384NegCode.length)
    (rsp : reg n sp = F) (r9 : reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i))
    (r20 : reg n (20 : Fin 32) = xp + BitVec.ofNat 32 (4 * i)) (r21 : reg n (21 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (r8 : reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0x42 else 0x60) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (20 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (21 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) →
        q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc ng_at_42 (off' := 0x44) (by decide)
    (by rw [r9, add_lit_zero]; exact aligned_add hnp (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc ng_at_44 (off' := 0x48) (by decide)
    (by rw [upd_ne (by decide) (by decide), r20, add_lit_zero]; exact aligned_add hxp (by omega))
  rw [r9, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (20 : Fin 32) + 0)) a0 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (20 : Fin 32) + 0)) a1 =
      memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [r20, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFFFAA6 (by decide))
    ng_at_48 ng_at_4c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x48 + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P p384NegCode := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have e21 : reg n3 (21 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block ngSubTail u3 hc3 ngSubTail_end
    (ngSubTail_ok (by rw [e21]; exact aligned_add hD (by omega)) (by rw [e21]; exact sDC))
  obtain ⟨em4, t2, t9, t20, t21, t8, tk⟩ := ngSubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, e21, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock ngSubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have e8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [g4, t8, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, cnt12_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (8 : Fin 32)) (reg n4 x0) = decide (i + 1 < 12) := by
    rw [e8, u4'.zero]; exact cnt12_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M (xp + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (20 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (21 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) →
        q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, e8], fun q q0 q1 q2 q3 q4 qr q9 q20 q21 q8 => ?_⟩
    · rw [h5, g4, t9, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, ptr4]
    · rw [h5, g4, t20, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r20, ptr4]
    · rw [h5, g4, t21, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, ptr4]
    · rw [h5, g4, tk q q2 q9 q20 q21 q8, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x42 ng_at_5e (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x60 ng_at_5e (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The subtraction**, from round `i` to its end at 0x60: the buffer at
`D` gets the modulus minus `x`, and `a2` the borrow out as a mask. -/
theorem ng_sub_loop {P F np xp D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hxp : xp.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 48 ≤ 2 ^ 32)
    (sFN : Sep (F + 0xFFFFFFFC) 4 np 48) (sFX : Sep (F + 0xFFFFFFFC) 4 xp 48) (sFD : Sep (F + 0xFFFFFFFC) 4 D 48)
    (sDN : Sep D 48 np 48) (sDX : Sep D 48 xp 48)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (ngBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P p384NegCode.length)
    (sDB : Sep D 48 (ngBsub P) borrowingSubCode.length) (sDC : Sep D 48 P p384NegCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x42 (reg n) → CodeIn M P p384NegCode → CodeIn M (ngBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (20 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (21 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x60 (reg n') ∧ CodeIn M' P p384NegCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np 12 + 2 ^ (32 * 12) * maskBit (reg n' a2) = accV M0 xp 12 + accV M' D 12 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) →
          q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x42 (reg n) → CodeIn M P p384NegCode → CodeIn M (ngBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 np i + 2 ^ (32 * i) * maskBit b = accV M0 xp i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = np + BitVec.ofNat 32 (4 * i) →
      reg n (20 : Fin 32) = xp + BitVec.ofNat 32 (4 * i) → reg n (21 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x42 else 0x60) (reg n') ∧
        CodeIn M' P p384NegCode ∧ CodeIn M' (ngBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 np (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 xp (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (9 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (20 : Fin 32) = xp + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (21 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (20 : Fin 32) →
          q ≠ (21 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r20 r21 r8 ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, e9, e20, e21, e8, fr⟩ := ng_sub_iter (i := i) s hc hb hP hi hF hnp hxp hD
      sFB sFC (sDC.sub (by omega)) rsp r9 r20 r21 r8 ra2
    have eA : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    have eN : memLoad32 M (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFX.subR (by omega)) (sDX.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (xp + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (ngBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P p384NegCode := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, e9, e20, e21, e8, fr⟩
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
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r20 r21 r8 ra2
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hb hfr hbm hv rsp r9 r20 r21 r8 ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r20 r21 r8 ra2
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e9, e20, e21, e8, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp r9 r20 r21 r8 ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 e9 e20 e21 e8 rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr q9 q20 q21 q8 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q9 q20 q21 q8, fr q q0 q1 q2 q3 q4 qr q9 q20 q21 q8]⟩

/-- One limb of the mask loop, from 0x6E: store the choice byte to the
frame, read it back, and AND limb `i` of the buffer with the byte minus 1. -/
def ngMask : List BInstr :=
  [.sb sp a0 0x33, .lw a4 a1 0, .lbu a5 sp 0x33, .aluImm .add a5 a5 0xFFFFFFFF, .alu .and a4 a4 a5, .sw a1 a4 0,
   .aluImm .add a1 a1 4, .aluImm .add a2 a2 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem ngMask_end : blockEnd p384NegCode 0x6E ngMask = some 0x82 := by decide
end

set_option maxRecDepth 20000 in
theorem ngMask_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock ngMask (M, f)).1 = memStore32 (memStore8 M (f sp + 0x33) ((f a0).extractLsb' 0 8)) (f a1 + 0)
      (aluEval .and (memLoad32 (memStore8 M (f sp + 0x33) ((f a0).extractLsb' 0 8)) (f a1 + 0))
        (aluEval .add ((memStore8 M (f sp + 0x33) ((f a0).extractLsb' 0 8) (f sp + 0x33)).zeroExtend 32)
          0xFFFFFFFF)) ∧
    (runBlock ngMask (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock ngMask (M, f)).2 a2 = f a2 + 0xFFFFFFFF ∧
    ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → (runBlock ngMask (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, ngMask]
  refine ⟨?_, ?_, ?_, fun q q1 q2 q4 q5 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1, q2, q4, q5]

theorem ngMask_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (hs1 : Sep (f sp + 0x33) 1 base len) (ha : (f a1 + 0).toNat % 4 = 0) (hs2 : Sep (f a1 + 0) 4 base len) :
    BlockOk base len ngMask (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, ngMask, upd, ↓reduceIte, and_true, true_and]
  exact ⟨hs1, ha, ha, hs2⟩

theorem ng_and_ones (w : Word) : w &&& 0xFFFFFFFF = w := by
  have hb : ∀ i : Fin 32, (0xFFFFFFFF : Word).getLsbD i.val = true := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, hb ⟨i, hi⟩, Bool.and_true]

theorem ng_maskW (w c : Word) (hc : c = 0 ∨ c = 1) :
    aluEval .and w (aluEval .add c 0xFFFFFFFF) = if c = 1 then 0 else w := by
  rcases hc with rfl | rfl
  · show w &&& (0 + 0xFFFFFFFF) = w
    rw [show (0 : Word) + 0xFFFFFFFF = 0xFFFFFFFF by decide, ng_and_ones]
  · show w &&& (1 + 0xFFFFFFFF) = 0
    rw [show (1 : Word) + 0xFFFFFFFF = 0 by decide]; exact BitVec.and_zero

theorem ng_slot (F : Word) {i : Nat} (hi : i < 12) :
    Sep (F + 0x33) 1 (F + BitVec.ofNat 32 (4 * i)) 4 :=
  sep_offsets F (c := 0x33) (n := 1) (d := 4 * i) (k := 4) (.inr (by omega)) (by omega) (by omega)

/-- **One limb of the mask loop**, from 0x6E: limb `i` of the buffer at `F`
stays when the choice `c` is 0 and becomes zero when it is 1. -/
theorem ng_mask_iter {M : Word → BitVec 8} {P F c : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x6E (reg n)) (hc : CodeIn M P p384NegCode) (hi : i < 12) (hcc : c = 0 ∨ c = 1)
    (hF : F.toNat % 4 = 0) (sC1 : Sep (F + 0x33) 1 P p384NegCode.length) (sC2 : Sep (F + BitVec.ofNat 32 (4 * i)) 4 P p384NegCode.length)
    (rsp : reg n sp = F) (ra1 : reg n a1 = F + BitVec.ofNat 32 (4 * i)) (ra2 : reg n a2 = BitVec.ofNat 32 (12 - i))
    (ra0 : reg n a0 = c) :
    ∃ n', Steps n n' ∧
      St (memStore32 (memStore8 M (F + 0x33) (c.extractLsb' 0 8)) (F + BitVec.ofNat 32 (4 * i))
          (if c = 1 then 0 else memLoad32 M (F + BitVec.ofNat 32 (4 * i))))
        P n' (if i + 1 < 12 then 0x6E else 0x84) (reg n') ∧
      reg n' a1 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → reg n' q = reg n q := by
  have hz := s.zero
  have ok := ngMask_ok (M := M) (f := reg n) (base := P) (len := p384NegCode.length) (by rw [rsp]; exact sC1)
    (by rw [ra1, add_lit_zero]; exact aligned_add hF (by omega)) (by rw [ra1, add_lit_zero]; exact sC2)
  obtain ⟨n1, c1, u1⟩ := St.block ngMask s hc ngMask_end ok
  obtain ⟨em1, e1, e2, fr⟩ := ngMask_run (M := M) (f := reg n) hz
  have u1' := u1.self
  rw [em1, rsp, ra0, ra1, add_lit_zero, memLoad32_store8_sep (ng_slot F hi), choice_byte M _ c hcc,
    ng_maskW _ c hcc] at u1'
  have hc1 := CodeIn.store32 (v := if c = 1 then 0 else memLoad32 M (F + BitVec.ofNat 32 (4 * i)))
    (CodeIn.store8 (v := c.extractLsb' 0 8) hc sC1) sC2
  have g1 : ∀ q, reg n1 q = (runBlock ngMask (M, reg n)).2 q := u1.regs
  have ea2 : reg n1 a2 = BitVec.ofNat 32 (12 - (i + 1)) := by rw [g1, e2, ra2, cnt12_dec i hi]
  have hb : branchTaken .bne (reg n1 a2) (reg n1 x0) = decide (i + 1 < 12) := by
    rw [ea2, u1'.zero]; exact cnt12_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a1 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → reg n2 q = reg n q := fun n2 h2 =>
    ⟨by rw [h2, g1, e1, ra1, ptr4], by rw [h2, ea2], fun q q1 q2 q4 q5 => by rw [h2, g1, fr q q1 q2 q4 q5]⟩
  by_cases hl : i + 1 < 12
  · obtain ⟨n2, d2, u2⟩ := u1'.taken hc1 0x6E ng_at_82 (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc1 0x84 ng_at_82 (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **The mask loop**, from limb `i` to its end at 0x84: the buffer's limbs
keep their values in `MB` when `c` is 0 and become zero when it is 1, and
nothing else changes but the choice byte. -/
theorem ng_mask_loop {P F c : Word} {MB : Word → BitVec 8} (hcc : c = 0 ∨ c = 1) (hF : F.toNat % 4 = 0)
    (sC : Sep F 0x34 P p384NegCode.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M P n 0x6E (reg n) → CodeIn M P p384NegCode →
      (∀ x, Sep F (4 * i) x 1 → Sep (F + 0x33) 1 x 1 → M x = MB x) →
      (∀ j, j < i → memLoad32 M (F + BitVec.ofNat 32 (4 * j)) = if c = 1 then 0 else memLoad32 MB (F + BitVec.ofNat 32 (4 * j))) →
      reg n sp = F → reg n a1 = F + BitVec.ofNat 32 (4 * i) → reg n a2 = BitVec.ofNat 32 (12 - i) → reg n a0 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x84 (reg n') ∧ CodeIn M' P p384NegCode ∧
        (∀ x, Sep F 48 x 1 → Sep (F + 0x33) 1 x 1 → M' x = MB x) ∧
        (∀ j, j < 12 → memLoad32 M' (F + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then 0 else memLoad32 MB (F + BitVec.ofNat 32 (4 * j))) ∧
        ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → reg n' q = reg n q := by
  have sC1 : Sep (F + 0x33) 1 P p384NegCode.length := by
    have := sC.sub (c := 0x33) (l := 1) (by decide); exact this
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine},
      St M P n 0x6E (reg n) → CodeIn M P p384NegCode →
      (∀ x, Sep F (4 * i) x 1 → Sep (F + 0x33) 1 x 1 → M x = MB x) →
      (∀ j, j < i → memLoad32 M (F + BitVec.ofNat 32 (4 * j)) = if c = 1 then 0 else memLoad32 MB (F + BitVec.ofNat 32 (4 * j))) →
      reg n sp = F → reg n a1 = F + BitVec.ofNat 32 (4 * i) → reg n a2 = BitVec.ofNat 32 (12 - i) → reg n a0 = c →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x6E else 0x84) (reg n') ∧ CodeIn M' P p384NegCode ∧
        (∀ x, Sep F (4 * (i + 1)) x 1 → Sep (F + 0x33) 1 x 1 → M' x = MB x) ∧
        (∀ j, j < i + 1 → memLoad32 M' (F + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then 0 else memLoad32 MB (F + BitVec.ofNat 32 (4 * j))) ∧
        reg n' sp = F ∧ reg n' a1 = F + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = BitVec.ofNat 32 (12 - (i + 1)) ∧
        reg n' a0 = c ∧ ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → reg n' q = reg n q := by
    intro i hi M n s hc hfr hwd rsp ra1 ra2 ra0
    have sC2 : Sep (F + BitVec.ofNat 32 (4 * i)) 4 P p384NegCode.length := sC.sub (by omega)
    obtain ⟨n1, c1, u1, e1, e2, fr⟩ := ng_mask_iter s hc hi hcc hF sC1 sC2 rsp ra1 ra2 ra0
    have hold : memLoad32 M (F + BitVec.ofNat 32 (4 * i)) = memLoad32 MB (F + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc]
        exact hfr _ (sep_offsets F (c := 0) (n := 4 * i) (d := 4 * i + q) (k := 1) (.inl (by omega)) (by omega)
            (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
          (sep_offsets F (c := 0x33) (n := 1) (d := 4 * i + q) (k := 1) (.inr (by omega)) (by omega) (by omega))
    refine ⟨n1, _, c1, u1, CodeIn.store32 (CodeIn.store8 hc sC1) sC2, fun x hx h33 => ?_, fun j hj => ?_,
      by rw [fr sp (by decide) (by decide) (by decide) (by decide), rsp], e1, e2,
      by rw [fr a0 (by decide) (by decide) (by decide) (by decide), ra0], fr⟩
    · have hx4 : Sep (F + BitVec.ofNat 32 (4 * i)) 4 x 1 := by
        have := hx.sub (c := 4 * i) (l := 4) (by omega); exact this
      have h8 : x ≠ F + 0x33 := fun e => by
        have := h33.point (i := 0) (j := 0) (by decide) (by decide)
        rw [add_ofNat_zero, add_ofNat_zero] at this; exact this e.symm
      rw [memStore32_get_sep hx4, memStore8_ne h8]
      exact hfr x (by
        intro a ha b hb e
        exact hx a (by omega) b hb e) h33
    · by_cases hji : j = i
      · subst hji
        rw [memLoad32_store32_same, hold]
      · rw [memLoad32_store32_sep (sep_offsets F (c := 4 * i) (n := 4) (d := 4 * j) (k := 4) (by omega)
            (by omega) (by omega)), memLoad32_store8_sep (ng_slot F (by omega)), hwd j (by omega)]
  intro m
  induction m with
  | zero =>
    intro i hi M n s hc hfr hwd rsp ra1 ra2 ra0
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, hf1, hw1, _, _, _, _, fr⟩ := step 11 (by decide) s hc hfr hwd rsp ra1 ra2 ra0
    exact ⟨n1, M1, c1, u1, hc1, hf1, hw1, fr⟩
  | succ m ih =>
    intro i hi M n s hc hfr hwd rsp ra1 ra2 ra0
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hf1, hw1, sp1, e1, e2, e0, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hfr hwd rsp ra1 ra2 ra0
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hw', fr'⟩ := ih (i + 1) (sel_succ hi) u1 hc1 hf1 hw1 sp1 e1 e2 e0
    exact ⟨n', M', c1.trans c', u', hc', hf', hw', fun q q1 q2 q4 q5 => by
      rw [fr' q q1 q2 q4 q5, fr q q1 q2 q4 q5]⟩

/-- The function's region: the word below its frame that its callees write,
and its 0x50-byte frame. -/
abbrev ngR (sp0 : Word) : Word := sp0 + 0xFFFFFFAC

/-- The registers `neg` saves, at offsets from its `sp`. -/
abbrev ngPs : List (Fin 32 × Word) :=
  [(ra, 0x4C), ((8 : Fin 32), 0x48), ((9 : Fin 32), 0x44), ((18 : Fin 32), 0x40), ((19 : Fin 32), 0x3C),
   ((20 : Fin 32), 0x38), ((21 : Fin 32), 0x34)]

/-- From 0x10 to the call at 0x16: keep `x` and the result pointer, and pass
`x` to `is_nonzero`. -/
def ngMov : List BInstr := [.alu .add (20 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 a1]

/-- From 0x1E to the call at 0x2C: keep `is_nonzero`'s answer and pass
`memset`'s arguments for the buffer at `sp`. -/
def ngPre : List BInstr :=
  [.aluImm .and (19 : Fin 32) a0 0xFF, .alu .add a0 x0 sp, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0,
   .alu .add (21 : Fin 32) x0 sp]

/-- From 0x34 to 0x40: the borrow, the modulus's address, and the count. -/
def ngInit : List BInstr :=
  [.aluImm .add a2 x0 0x0, .lui (9 : Fin 32) 0x3FCC5000, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFC8C,
   .aluImm .add (8 : Fin 32) x0 0xC]

/-- From 0x60 to 0x6C: the choice byte (1 when `x` is zero), the buffer, and
the count. -/
def ngMk : List BInstr :=
  [.aluImm .xor a0 (19 : Fin 32) 0x1, .alu .add a1 x0 sp, .aluImm .add a2 x0 0xC, .aluImm .add a3 sp 0x33]

/-- From 0x84 to the call at 0x8C: `memcpy`'s arguments. -/
def ngPost : List BInstr := [.alu .add a1 x0 sp, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem ngSave_end : blockEnd p384NegCode 2 (saveBlock ngPs) = some 0x10 := by decide
theorem ngMov_end : blockEnd p384NegCode 0x10 ngMov = some 0x16 := by decide
theorem ngPre_end : blockEnd p384NegCode 0x1E ngPre = some 0x2C := by decide
theorem ngInit_end : blockEnd p384NegCode 0x34 ngInit = some 0x40 := by decide
theorem ngMk_end : blockEnd p384NegCode 0x60 ngMk = some 0x6C := by decide
theorem ngPost_end : blockEnd p384NegCode 0x84 ngPost = some 0x8C := by decide
theorem ngRestore_end : blockEnd p384NegCode 0x94 (restoreBlock ngPs) = some 0xA2 := by decide
theorem ngPs_range : ∀ p ∈ ngPs, p.2.toNat % 4 = 0 ∧ 0x34 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x50 := by decide
theorem ngPs_sp : ∀ p ∈ ngPs, p.1 ≠ sp := by decide
end

/-- Where `neg` runs: its code and its callees', the modulus, its region
below `sp0`, the result `out`, and `x`, aligned and apart from what each
must not touch. -/
structure NgEnv (M : Word → BitVec 8) (P sp0 out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384NegCode
  nz : CodeIn M (P + 0x1129C) uint12IsNonzeroCode
  ref : CodeIn M (P + 0x3F2) uintRefIsNonzeroCode
  mset : CodeIn M (P + 0x11F6C) memsetCode
  bsub : CodeIn M (ngBsub P) borrowingSubCode
  stub : CodeIn M (P + 0x11FD4) memcpyStubCode
  body : CodeIn M (P + 0x11FDC) memcpyBodyCode
  pmod : CodeIn M p3M p384ModulusData
  hsp : sp0.toNat % 4 = 0
  hS : 0x54 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hxp : xp.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sSC : Sep (ngR sp0) 0x54 P p384NegCode.length
  sSZ : Sep (ngR sp0) 0x54 (P + 0x1129C) uint12IsNonzeroCode.length
  sSF : Sep (ngR sp0) 0x54 (P + 0x3F2) uintRefIsNonzeroCode.length
  sSM : Sep (ngR sp0) 0x54 (P + 0x11F6C) memsetCode.length
  sSB : Sep (ngR sp0) 0x54 (ngBsub P) borrowingSubCode.length
  sSU : Sep (ngR sp0) 0x54 (P + 0x11FD4) memcpyStubCode.length
  sSY : Sep (ngR sp0) 0x54 (P + 0x11FDC) memcpyBodyCode.length
  sSP : Sep (ngR sp0) 0x54 p3M 48
  sOC : Sep out 48 P p384NegCode.length
  sOY : Sep out 48 (P + 0x11FDC) memcpyBodyCode.length
  sOS : Sep out 48 (ngR sp0) 0x54
  sXS : Sep xp 48 (ngR sp0) 0x54

/-- The registers `neg` leaves as they were. -/
def ngKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 10, 11, 12, 13, 14, 15, 16, 17]

theorem accV_eq_zero {M : Word → BitVec 8} {b : Word} :
    ∀ n, accV M b n = 0 → ∀ i, i < n → memLoad32 M (b + BitVec.ofNat 32 (4 * i)) = 0
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    rw [accV_succ1] at h
    have hp : 0 < 2 ^ (32 * n) := Nat.two_pow_pos _
    have h1 : accV M b n = 0 := by omega
    have h2 : (memLoad32 M (b + BitVec.ofNat 32 (4 * n))).toNat = 0 := by
      rcases Nat.eq_zero_or_pos (memLoad32 M (b + BitVec.ofNat 32 (4 * n))).toNat with h' | h'
      · exact h'
      · have := Nat.mul_pos h' hp; omega
    rcases (by omega : i < n ∨ i = n) with hi' | rfl
    · exact accV_eq_zero n h1 i hi'
    · exact BitVec.eq_of_toNat_eq h2

theorem ng_res {X Dv p B : Nat} (hX : X < 2 ^ 384) (hD : Dv < 2 ^ 384) (hp : p < 2 ^ 384) (hB : B ≤ 1)
    (h : p + 2 ^ 384 * B = X + Dv) : Dv = (p + 2 ^ 384 - X) % 2 ^ 384 := by
  rcases (by omega : B = 0 ∨ B = 1) with rfl | rfl
  · rw [Nat.mod_eq_sub_mod (by omega), show p + 2 ^ 384 - X - 2 ^ 384 = p - X by omega,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
set_option exponentiation.threshold 400 in
/-- **The compiled `ConstMontyForm<p384>::neg`**: `out` gets `p - x` modulo
2^384, and zero when `x` is zero. -/
theorem p384Neg_correct (m : Machine) {P sp0 out xp retAddr : Word} (env : NgEnv m.mem P sp0 out xp)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, ngKeep q = true → reg m' q = reg m q) ∧
      accV m'.mem out 12 =
        (if accV m.mem xp 12 = 0 then 0 else (p384 + 2 ^ 384 - accV m.mem xp 12) % 2 ^ 384) ∧
      ∀ x, Sep (ngR sp0) 0x54 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R, hR⟩ : ∃ R, ngR sp0 = R := ⟨_, rfl⟩
  have sSC := env.sSC; have sSZ := env.sSZ; have sSF := env.sSF; have sSM := env.sSM; have sSB := env.sSB
  have sSU := env.sSU; have sSY := env.sSY; have sSP := env.sSP; have sOS := env.sOS; have sXS := env.sXS
  rw [hR] at sSC sSZ sSF sSM sSB sSU sSY sSP sOS sXS ⊢
  have hRw : R.toNat + 0x54 = sp0.toNat := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFFAC : Word).toNat = 4294967212 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hRa : R.toNat % 4 = 0 := by rw [← hR]; exact aligned_add env.hsp (k := 0xFFFFFFAC) (by decide)
  obtain ⟨F, hF⟩ : ∃ F, R + BitVec.ofNat 32 4 = F := ⟨_, rfl⟩
  have eF : sp0 + 0xFFFFFFB0 = F := by rw [← hF, ← hR, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := hF ▸ aligned_add hRa (by decide)
  have hFw : F.toNat + 0x50 = sp0.toNat := by
    rw [← hF, BitVec.toNat_add, ofNat_tn (by decide)]; omega
  have eFR : F + 0xFFFFFFFC = R + BitVec.ofNat 32 0 := by rw [← hF, BitVec.add_assoc]; rfl
  have toF : ∀ {b : Word} {k : Nat} {c l : Nat}, c + l ≤ 0x50 → Sep R 0x54 b k →
      Sep (F + BitVec.ofNat 32 c) l b k := fun {b k c l} h hs => by
    rw [← hF, add_ofNat_assoc]; exact hs.sub (by omega)
  have toF0 : ∀ {b : Word} {k : Nat} {l : Nat}, l ≤ 0x50 → Sep R 0x54 b k → Sep F l b k := fun {b k l} h hs => by
    have := toF (c := 0) (l := l) (by omega) hs; rwa [add_ofNat_zero] at this
  have toG : ∀ {b : Word} {k : Nat}, Sep R 0x54 b k → Sep (F + 0xFFFFFFFC) 4 b k := fun {b k} hs => by
    rw [eFR]; exact hs.sub (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep R 0x54 b code.length → (∀ x, Sep R 0x54 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the prologue
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code ng_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, eF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock ngPs) u1 env.code ngSave_end (saveBlock_ok _ ngPs _ fun p hp => by
    rw [sp1]
    have := ngPs_range p hp
    exact ⟨fr_al' hFa this.1, frm_sep' (toF0 (l := 0x50) (by decide) sSC) (by omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0)) ngPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep R 0x54 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside ngPs fun p hp => frm_sep' (toF0 (l := 0x50) (by decide) hx) (by
      have := ngPs_range p hp; omega)
  have hslv : ∀ r o, (r, o) ∈ ngPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [ngPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) r := u2.regs
  obtain ⟨m3, c3, u3⟩ := St.block ngMov u2.self (cIn env.code sSC frSv) ngMov_end
    (by simp [BlockOk, BInstr.ok, ngMov])
  simp only [runBlock, BInstr.run, ngMov] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have v3 : reg m3 sp = F ∧ reg m3 20 = xp ∧ reg m3 18 = out ∧ reg m3 a0 = xp := by
    simp +decide only [g3, upd_app, ↓reduceIte, r2]
    simp only [ev_add, hsp, eF, ha0, ha1, zw]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨v3sp, v320, v318, v3a0⟩ := v3
  have k3 : ∀ q : Fin 32, q ≠ sp → q ≠ 20 → q ≠ 18 → q ≠ a0 → reg m3 q = reg m q := fun q h1 h2 h3 h4 => by
    rw [g3]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, h2, h3, h4, ite_false]; rw [r2]; simp only [upd_app, h0, h1, ite_false]
  -- `is_nonzero`
  have hcS := cIn env.code sSC frSv
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS ng_at_16 ng_at_1a
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x1129C (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have sp4 : reg m4 sp = F := by rw [r4 sp (by decide), v3sp]
  have eW : P + BitVec.ofNat 32 0x1129C + 0xFFFEF156 = P + 0x3F2 := by rw [BitVec.add_assoc]; rfl
  have eG4 : reg m4 sp + 0xFFFFFFFC = R + BitVec.ofNat 32 0 := by rw [sp4, eFR]
  obtain ⟨m5, c5, pc5, a05, k5, f5⟩ := uint12IsNonzero_correct m4 (even_at P env.hP 0x1129C (by decide))
    (by rw [mem4]; exact cIn env.nz sSZ frSv) (by rw [mem4, eW]; exact cIn env.ref sSF frSv) pc4
    (by rw [r4 a0 (by decide), v3a0]) env.hxp (by rw [sp4]; exact hFa)
    (by rw [eG4, eW]; exact sSF.sub (by decide)) (by rw [regs4]; simp +decide [upd])
    (even_clear _ (even_at P env.hP (0x16 + 8) (by decide)))
  rw [mem4] at a05 f5
  rw [eG4] at f5
  have frX : ∀ i, i < 12 → memLoad32 Msv (xp + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * i)) :=
    fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]; exact frSv _ (sXS.sub (c := 4 * i + q) (l := 1) (by omega)).symm
  obtain ⟨nz, hnz⟩ : ∃ nz : Word,
      (if ∀ i : Nat, i < 12 → memLoad32 Msv (xp + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) = nz := ⟨_, rfl⟩
  rw [hnz] at a05
  have fr5 : ∀ x, Sep R 0x54 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [f5 x (hx.sub (by decide)), frSv x hx]
  have hnz01 : nz = 0 ∨ nz = 1 := by rw [← hnz]; split <;> simp
  have k5' : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ t1 → q ≠ ra → reg m5 q = reg m3 q :=
    fun q h0 h1 h2 h3 ht hr => by rw [k5 q h0 h1 h2 h3 ht, r4 q hr]
  have u5 : St m5.mem P m5 0x1E (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  -- the buffer
  obtain ⟨m6, c6, u6⟩ := St.block ngPre u5 (cIn env.code sSC fr5) ngPre_end (by simp [BlockOk, BInstr.ok, ngPre])
  simp only [runBlock, BInstr.run, ngPre] at u6
  have g6 : ∀ r, reg m6 r = _ := u6.regs
  have sp5 : reg m5 sp = F := by
    rw [k5' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v3sp]
  have v6 : reg m6 sp = F ∧ reg m6 19 = nz ∧ reg m6 a0 = F ∧ reg m6 a2 = BitVec.ofNat 32 (4 * 12) ∧ reg m6 a1 = 0 ∧
      reg m6 21 = F := by
    simp +decide only [g6, upd_app, ↓reduceIte]
    simp only [ev_add, sp5, a05, zw]
    refine ⟨trivial, ?_, trivial, trivial, trivial, trivial⟩
    rcases hnz01 with h | h <;> rw [h] <;> rfl
  obtain ⟨v6sp, v619, v6a0, v6a2, v6a1, v621⟩ := v6
  have k6 : ∀ q : Fin 32, q ≠ 19 → q ≠ a0 → q ≠ a2 → q ≠ a1 → q ≠ 21 → reg m6 q = reg m5 q :=
    fun q h1 h2 h3 h4 h5 => by
      rw [g6]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact u5.zero.symm
      simp only [upd_app, h0, h1, h2, h3, h4, h5, ite_false]
  have hFw48 : F.toNat + 4 * 12 < 2 ^ 32 := by omega
  obtain ⟨m7, c7, u7, a07, k7⟩ := u6.self.memsetW (B := P + 0x11F6C) (w := 12) (dst := F)
    (even_at P env.hP 0x11F6C (by decide)) (cIn env.code sSC fr5) (cIn env.mset sSM fr5) ng_at_2c ng_at_30
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x2C + 8) (by decide)) (by decide) hFw48
    (by decide) hFa (toF0 (by decide) sSM) v6a0 v6a1 v6a2
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords m5.mem F 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u7
  have frZ : ∀ x, Sep R 0x54 x 1 → Mz x = m.mem x := fun x hx => by
    rw [← hMz, fillWords_outside (dst := F) 12 (toF0 (by decide) hx), fr5 x hx]
  have hcZ := cIn env.code sSC frZ
  obtain ⟨m8, c8, u8⟩ := St.block ngInit u7 hcZ ngInit_end (by simp [BlockOk, BInstr.ok, ngInit])
  simp only [runBlock, BInstr.run, ngInit] at u8
  have g8 : ∀ r, reg m8 r = _ := u8.regs
  have z7 : reg m7 x0 = 0 := u7.zero
  have v8 : reg m8 a2 = 0 ∧ reg m8 9 = p3M ∧ reg m8 8 = BitVec.ofNat 32 (12 - 0) := by
    simp +decide only [g8, upd_app, ↓reduceIte]
    simp only [z7, ev_add]
    exact ⟨rfl, trivial⟩
  obtain ⟨v8a2, v89, v88⟩ := v8
  have k8 : ∀ q : Fin 32, q ≠ a2 → q ≠ 9 → q ≠ 8 → reg m8 q = reg m7 q := fun q h1 h2 h3 => by
    rw [g8]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact z7.symm
    simp only [upd_app, h0, h1, h2, h3, ite_false]
  obtain ⟨m9, d9, u9⟩ := u8.self.notTaken hcZ 0x42 ng_at_40 (by decide) (by rw [v88, u8.self.zero]; decide)
  have k9 : ∀ q, reg m9 q = reg m8 q := u9.regs
  -- the subtraction
  have sFD : Sep (F + 0xFFFFFFFC) 4 F 48 := by
    rw [eFR, ← hF]; exact sep_offsets R (.inl (by omega)) (by omega) (by omega)
  have k76 : ∀ q : Fin 32, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m7 q = reg m6 q := k7
  have r9sp : reg m9 sp = F := by
    rw [k9, k8 _ (by decide) (by decide) (by decide), k76 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v6sp]
  have r920 : reg m9 20 = xp := by
    rw [k9, k8 _ (by decide) (by decide) (by decide), k76 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k5' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v320]
  have r921 : reg m9 21 = F := by
    rw [k9, k8 _ (by decide) (by decide) (by decide), k76 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v621]
  obtain ⟨n10, M10, c10, u10, hc10, hf10, hb10, hv10, sp10, k10⟩ :=
    ng_sub_loop (np := p3M) (xp := xp) (D := F) (M0 := Mz) env.hP hFa (by decide) env.hxp hFa (by omega)
      (toG sSP) (toG sXS.symm) sFD (toF0 (by decide) sSP) (toF0 (by decide) sXS.symm) (toG sSB) (toG sSC)
      (toF0 (by decide) sSB) (toF0 (by decide) sSC)
      11 0 rfl u9.self hcZ (cIn env.bsub sSB frZ) (fun _ _ _ => rfl) (.inl rfl) (by simp [accV, maskBit])
      r9sp (by rw [k9, v89, Nat.mul_zero, add_ofNat_zero]) (by rw [r920, Nat.mul_zero, add_ofNat_zero])
      (by rw [r921, Nat.mul_zero, add_ofNat_zero]) (by rw [k9, v88]) (by rw [k9, v8a2])
  have pZ : accV Mz p3M 12 = p384 := p3M_val (cIn env.pmod sSP frZ)
  have xZ : accV Mz xp 12 = accV m.mem xp 12 := accV_congr 12 fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc]; exact frZ _ (sXS.sub (c := 4 * i + q) (l := 1) (by omega)).symm
  rw [pZ, xZ] at hv10
  -- the choice byte
  have r1019 : reg n10 19 = nz := by
    rw [k10 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k9, k8 _ (by decide) (by decide) (by decide),
      k76 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v619]
  obtain ⟨n11, c11, u11⟩ := St.block ngMk u10 hc10 ngMk_end (by simp [BlockOk, BInstr.ok, ngMk])
  simp only [runBlock, BInstr.run, ngMk] at u11
  have g11 : ∀ r, reg n11 r = _ := u11.regs
  have z10 : reg n10 x0 = 0 := u10.zero
  obtain ⟨c, hc⟩ : ∃ c : Word, aluEval .xor nz 1 = c := ⟨_, rfl⟩
  have hcc : c = 0 ∨ c = 1 := by rw [← hc]; rcases hnz01 with h | h <;> rw [h] <;> decide
  have hc1 : c = 1 ↔ nz = 0 := by rw [← hc]; rcases hnz01 with h | h <;> rw [h] <;> decide
  have v11 : reg n11 a0 = c ∧ reg n11 a1 = F ∧ reg n11 a2 = BitVec.ofNat 32 (12 - 0) ∧ reg n11 sp = F := by
    simp +decide only [g11, upd_app, ↓reduceIte]
    simp only [ev_add, zw, sp10, r1019, hc]
    exact ⟨trivial, trivial, trivial, trivial⟩
  obtain ⟨v11a0, v11a1, v11a2, v11sp⟩ := v11
  have k11 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n11 q = reg n10 q := fun q h1 h2 h3 h4 => by
    rw [g11]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact z10.symm
    simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  obtain ⟨n12, d12, u12⟩ := u11.self.notTaken hc10 0x6E ng_at_6c (by decide) (by rw [v11a2, u11.self.zero]; decide)
  have k12 : ∀ q, reg n12 q = reg n11 q := u12.regs
  -- the mask
  obtain ⟨n13, M13, c13, u13, hc13, hf13, hw13, k13⟩ :=
    ng_mask_loop (MB := M10) hcc hFa (toF0 (by decide) sSC) 11 0 rfl u12.self hc10 (fun _ _ _ => rfl)
      (fun j hj => absurd hj (Nat.not_lt_zero j)) (by rw [k12, v11sp]) (by rw [k12, v11a1, Nat.mul_zero, add_ofNat_zero])
      (by rw [k12, v11a2]) (by rw [k12, v11a0])
  have hFR : ∀ x, Sep R 0x38 x 1 → M13 x = m5.mem x := fun x hx => by
    have h1 : Sep F 48 x 1 := by rw [← hF]; exact hx.sub (by decide)
    have h2 : Sep (F + 0x33) 1 x 1 := by
      rw [show F + 0x33 = R + BitVec.ofNat 32 0x37 by rw [← hF, BitVec.add_assoc]; rfl]; exact hx.sub (by decide)
    have h3 : Sep (F + 0xFFFFFFFC) 4 x 1 := by rw [eFR]; exact hx.sub (by decide)
    rw [hf13 x h1 h2, hf10 x h3 h1, ← hMz, fillWords_outside (dst := F) 12 h1]
  have fr13 : ∀ x, Sep R 0x54 x 1 → M13 x = m.mem x := fun x hx => by
    rw [hFR x (hx.sub (c := 0) (l := 0x38) (by decide) |> fun h => by rwa [add_ofNat_zero] at h), fr5 x hx]
  -- copy the buffer out
  have r13 : ∀ q : Fin 32, q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ a5 → reg n13 q = reg n11 q := fun q h1 h2 h4 h5 => by
    rw [k13 q h1 h2 h4 h5, k12]
  have r1318 : reg n13 18 = out := by
    rw [r13 _ (by decide) (by decide) (by decide) (by decide), k11 _ (by decide) (by decide) (by decide) (by decide),
      k10 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), k9, k8 _ (by decide) (by decide) (by decide),
      k76 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k6 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k5' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v318]
  have sp13 : reg n13 sp = F := by
    rw [r13 _ (by decide) (by decide) (by decide) (by decide), k11 _ (by decide) (by decide) (by decide) (by decide),
      sp10]
  obtain ⟨n14, c14, u14⟩ := St.block ngPost u13 hc13 ngPost_end (by simp [BlockOk, BInstr.ok, ngPost])
  simp only [runBlock, BInstr.run, ngPost] at u14
  have g14 : ∀ r, reg n14 r = _ := u14.regs
  have z13 : reg n13 x0 = 0 := u13.zero
  have v14 : reg n14 a1 = F ∧ reg n14 a2 = BitVec.ofNat 32 (4 * 12) ∧ reg n14 a0 = out := by
    simp +decide only [g14, upd_app, ↓reduceIte]
    simp only [z13, ev_add, zw, sp13, r1318]
    exact ⟨trivial, trivial, trivial⟩
  obtain ⟨v14a1, v14a2, v14a0⟩ := v14
  have k14 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n14 q = reg n13 q := fun q h1 h2 h3 => by
    rw [g14]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact z13.symm
    simp only [upd_app, h0, h1, h2, h3, ite_false]
  have e8 : P + 0x11FD4 + 8 = P + 0x11FDC := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n15, c15, u15, a015, k15⟩ := u14.self.memcpyW (B := P + 0x11FD4) (w := 12) (dst := out) (src := F)
    (even_at P env.hP 0x11FD4 (by decide)) hc13 (cIn env.stub sSU fr13) (by rw [e8]; exact cIn env.body sSY fr13)
    ng_at_8c ng_at_90 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x8C + 8) (by decide))
    (by decide) env.hwo (by decide) env.hout hFa (by rw [← hF]; exact sOS.subR (by decide))
    (by rw [e8]; exact env.sOY) v14a0 v14a1 v14a2
  obtain ⟨MF, hMF⟩ : ∃ MF, copyWords M13 out F 12 = MF := ⟨_, rfl⟩
  rw [hMF] at u15
  have hMFs : ∀ x, Sep R 0x38 x 1 → Sep out 48 x 1 → MF x = Msv x := fun x hx ho => by
    rw [← hMF, copyWords_outside 12 ho, hFR x hx, f5 x (hx.sub (by decide))]
  have frF : ∀ x, Sep R 0x54 x 1 → Sep out 48 x 1 → MF x = m.mem x := fun x hx ho => by
    rw [hMFs x (hx.sub (c := 0) (l := 0x38) (by decide) |> fun h => by rwa [add_ofNat_zero] at h) ho, frSv x hx]
  have hcF : CodeIn MF P p384NegCode := fun i hi => by
    rw [frF _ (sSC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have k15' : ∀ q : Fin 32, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ ra → reg n15 q = reg n14 q := k15
  have sp15 : reg n15 sp = F := by
    rw [k15' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k14 _ (by decide) (by decide) (by decide), sp13]
  -- the epilogue
  obtain ⟨n16, c16, u16⟩ := St.block (restoreBlock ngPs) u15 hcF ngRestore_end
    (restoreBlock_ok MF _ ngPs (reg n15) sp15 ngPs_sp fun p hp => fr_al' hFa (ngPs_range p hp).1)
  simp only [restoreBlock_run MF _ ngPs (reg n15) sp15 ngPs_sp] at u16
  obtain ⟨n17, d17, u17⟩ := u16.aluImm hcF ng_at_a2 (off' := 0xA4) (by decide)
  obtain ⟨n18, d18, pc18, mem18, regs18⟩ := u17.jalr hcF ng_at_a4
  have slot : ∀ r o, (r, o) ∈ ngPs → memLoad32 MF (F + o) = reg m r := fun r o h => by
    obtain ⟨_, ho1, ho2⟩ := ngPs_range (r, o) h
    dsimp only at ho1 ho2
    have e : ∀ t, F + o + BitVec.ofNat 32 t = R + BitVec.ofNat 32 (4 + o.toNat + t) := fun t => by
      rw [← hF]; conv => lhs; rw [← ofNat_toNat_self o]
      rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]
    have h1 : memLoad32 MF (F + o) = memLoad32 Msv (F + o) := memLoad32_congr fun t ht => by
      have s1 : Sep R 0x38 (F + o + BitVec.ofNat 32 t) 1 := by
        rw [e]
        have := sep_offsets R (c := 0) (n := 0x38) (d := 4 + o.toNat + t) (k := 1) (.inl (by omega)) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at this
      have s2 : Sep out 48 (F + o + BitVec.ofNat 32 t) 1 := by rw [e]; exact sOS.subR (by omega)
      exact hMFs _ s1 s2
    rw [h1]
    exact hslv r o h
  have rest : ∀ r o, (r, o) ∈ ngPs → restoreRegs MF F (reg n15) ngPs r = reg m r := fun r o h => by
    have hs := slot
    simp only [ngPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hs _ _ (by decide)
  have rsp16 : restoreRegs MF F (reg n15) ngPs sp = F := by rw [restoreRegs_sp _ _ _ _ ngPs_sp]; exact sp15
  have eSp : F + 0x50 = sp0 := by rw [← eF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hra16 : restoreRegs MF F (reg n15) ngPs ra = retAddr := by rw [rest ra 0x4C (by decide), hra]
  refine ⟨n18, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (.cons d9
    (c10.trans (c11.trans (.cons d12 (c13.trans (c14.trans (c15.trans (c16.trans (.cons d17 (.single d18))))))))))))))))),
    ?_, ?_, ?_, ?_, fun x hx ho => by rw [mem18, frF x hx ho]⟩
  · rw [pc18]; simp +decide only [upd_app, ↓reduceIte]; rw [hra16, add_lit_zero, hret]
  · rw [regs18]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp16, ev_add, eSp]
  · intro q hq
    rw [regs18]
    by_cases hsp' : q = sp
    · subst hsp'; simp +decide only [upd_app, ↓reduceIte]; rw [rsp16, ev_add, eSp, hsp]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, hsp', ite_false]
    by_cases hps : q.val ∈ [1, 8, 9, 18, 19, 20, 21]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hps
      rcases hps with h | h | h | h | h | h | h <;> rw [show q = ⟨_, by decide⟩ from Fin.ext h]
      · exact rest ra 0x4C (by decide)
      · exact rest 8 0x48 (by decide)
      · exact rest 9 0x44 (by decide)
      · exact rest 18 0x40 (by decide)
      · exact rest 19 0x3C (by decide)
      · exact rest 20 0x38 (by decide)
      · exact rest 21 0x34 (by decide)
    have nq : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19, 20, 21] → q ≠ w := fun w hw e => hps (e ▸ hw)
    have nk : ∀ w : Fin 32, w.val ∈ [5, 6, 10, 11, 12, 13, 14, 15, 16, 17] → q ≠ w := fun w hw e => by
      subst e; simp only [ngKeep] at hq; exact absurd hw (by simpa using hq)
    simp only [restoreRegs, upd_app, h0, nq ra (by decide), nq 8 (by decide), nq 9 (by decide), nq 18 (by decide),
      nq 19 (by decide), nq 20 (by decide), nq 21 (by decide), ite_false]
    rw [k15' q (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)) (nk a4 (by decide)) (nk a5 (by decide))
        (nk a6 (by decide)) (nk a7 (by decide)) (nk t0 (by decide)) (nk t1 (by decide)) (nq ra (by decide)),
      k14 q (nk a0 (by decide)) (nk a1 (by decide)) (nk a2 (by decide)),
      r13 q (nk a1 (by decide)) (nk a2 (by decide)) (nk a4 (by decide)) (nk a5 (by decide)),
      k11 q (nk a0 (by decide)) (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)),
      k10 q (nk a0 (by decide)) (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)) (nk a4 (by decide))
        (nq ra (by decide)) (nq 9 (by decide)) (nq 20 (by decide)) (nq 21 (by decide)) (nq 8 (by decide)),
      k9, k8 q (nk a2 (by decide)) (nq 9 (by decide)) (nq 8 (by decide)),
      k76 q (nk a2 (by decide)) (nk a3 (by decide)) (nk a4 (by decide)) (nk a5 (by decide)) (nk a6 (by decide))
        (nq ra (by decide)),
      k6 q (nq 19 (by decide)) (nk a0 (by decide)) (nk a2 (by decide)) (nk a1 (by decide)) (nq 21 (by decide)),
      k5' q (nk a0 (by decide)) (nk a1 (by decide)) (nk a2 (by decide)) (nk a3 (by decide)) (nk t1 (by decide))
        (nq ra (by decide)),
      k3 q hsp' (nq 20 (by decide)) (nq 18 (by decide)) (nk a0 (by decide))]
  · have hw := env.hwo
    have hval : accV MF out 12 = if c = 1 then 0 else accV M10 F 12 := by
      have hl : ∀ j, j < 12 → memLoad32 MF (out + BitVec.ofNat 32 (4 * j)) =
          if c = 1 then 0 else memLoad32 M10 (F + BitVec.ofNat 32 (4 * j)) := fun j hj => by
        rw [← hMF, copyWords_load 12 j hj (by omega), hw13 j hj]
      by_cases h1 : c = 1
      · rw [ite_eq_left h1]; exact accV_zero 12 fun j hj => by rw [hl j hj, ite_eq_left h1]
      · rw [ite_eq_right h1]; exact accV_congr2 12 fun j hj => by rw [hl j hj, ite_eq_right h1]
    rw [mem18, hval]
    have hz' : c = 1 ↔ accV m.mem xp 12 = 0 := by
      rw [hc1, ← hnz]
      constructor
      · intro h
        by_cases hall : ∀ i : Nat, i < 12 → memLoad32 Msv (xp + BitVec.ofNat 32 (4 * i)) = 0
        · exact accV_zero 12 fun i hi => by rw [← frX i hi]; exact hall i hi
        · rw [ite_eq_right hall] at h; exact absurd h (by decide)
      · intro h
        rw [ite_eq_left fun i hi => by rw [frX i hi]; exact accV_eq_zero 12 h i hi]
    by_cases hX : accV m.mem xp 12 = 0
    · rw [ite_eq_left (hz'.mpr hX), ite_eq_left hX]
    · rw [ite_eq_right (fun h => hX (hz'.mp h)), ite_eq_right hX]
      exact ng_res (accV_lt _ _ 12) (accV_lt _ _ 12) (by decide) (mb_le1 _) hv10

end C3.RV32
