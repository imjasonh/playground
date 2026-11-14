import C3BootProofs.Proofs.U16
import C3BootProofs.Proofs.Crc32

/-!
# `c3_verify::reader::Reader::reserved`, as compiled

`Reader::reserved(n)` reads `n` bytes with `Reader::bytes` and fails with
`Error::NonzeroReserved` (4) unless all are zero, returning 0xFF in the low
byte of `a0` for `Ok`. The compiled function checks the bytes in a loop.
`reserved_loop` proves the loop by induction on the bytes left, and
`readerReserved_correct` proves the function through `readerBytes_correct`.
-/

namespace C3.RV32

open C3.Image

/-- Whether the `k` bytes at `p` are all zero. -/
def allZero (M : Word → BitVec 8) (p : Word) : Nat → Bool
  | 0 => true
  | k + 1 => M p == 0 && allZero M (p + 1) k

/-- What `Reader::reserved` returns in `a0`. -/
def reservedResult (M : Word → BitVec 8) (self n : Word) : Word :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n with
  | none => 0
  | some (p, _) => if allZero M p n.toNat then 0xFF else 4

/-- Memory after `Reader::reserved` returns, outside the stack it uses. -/
def reservedMem (M : Word → BitVec 8) (self n : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n with
  | none => M
  | some (_, e) => memStore32 M (self + 8) e

theorem rs_at_00 : fetchRel readerReservedCode 0x00 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem rs_at_02 : fetchRel readerReservedCode 0x02 = some (.store .sw sp ra 0x0C, 2) := by decide
theorem rs_at_04 : fetchRel readerReservedCode 0x04 = some (.alu .add a2 x0 a1, 2) := by decide
theorem rs_at_06 : fetchRel readerReservedCode 0x06 = some (.alu .add a1 x0 a0, 2) := by decide
theorem rs_at_08 : fetchRel readerReservedCode 0x08 = some (.aluImm .add a0 sp 4, 2) := by decide
theorem rs_at_0a : fetchRel readerReservedCode 0x0A = some (.auipc ra 0, 4) := by decide
theorem rs_at_0e : fetchRel readerReservedCode 0x0E = some (.jalr ra ra 0x92, 4) := by decide
theorem rs_at_12 : fetchRel readerReservedCode 0x12 = some (.load .lw a0 sp 4, 2) := by decide
theorem rs_at_14 : fetchRel readerReservedCode 0x14 = some (.branch .beq a0 x0 0x14, 2) := by decide
theorem rs_at_16 : fetchRel readerReservedCode 0x16 = some (.load .lw a1 sp 8, 2) := by decide
theorem rs_at_18 : fetchRel readerReservedCode 0x18 = some (.branch .beq a1 x0 0x16, 2) := by decide
theorem rs_at_1a : fetchRel readerReservedCode 0x1A = some (.load .lbu a2 a0 0, 4) := by decide
theorem rs_at_1e : fetchRel readerReservedCode 0x1E = some (.aluImm .add a0 a0 1, 2) := by decide
theorem rs_at_20 : fetchRel readerReservedCode 0x20 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem rs_at_22 : fetchRel readerReservedCode 0x22 = some (.branch .beq a2 x0 0xFFFFFFF6, 2) := by decide
theorem rs_at_24 : fetchRel readerReservedCode 0x24 = some (.aluImm .add a0 x0 4, 2) := by decide
theorem rs_at_26 : fetchRel readerReservedCode 0x26 = some (.jal x0 0x0C, 2) := by decide
theorem rs_at_28 : fetchRel readerReservedCode 0x28 = some (.load .lbu a0 sp 8, 4) := by decide
theorem rs_at_2c : fetchRel readerReservedCode 0x2C = some (.jal x0 6, 2) := by decide
theorem rs_at_2e : fetchRel readerReservedCode 0x2E = some (.aluImm .add a0 x0 0xFF, 4) := by decide
theorem rs_at_32 : fetchRel readerReservedCode 0x32 = some (.load .lw ra sp 0x0C, 2) := by decide
theorem rs_at_34 : fetchRel readerReservedCode 0x34 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem rs_at_36 : fetchRel readerReservedCode 0x36 = some (.jalr x0 ra 0, 2) := by decide

theorem zext_beq_zero (b : BitVec 8) : ((b.zeroExtend 32 : Word) == 0) = (b == 0) := by
  revert b; decide

/-- **The loop in `Reader::reserved`.** At offset 0x18 with `a0` at `q` and
`j` in `a1`, it reaches offset 0x32 with `a0` 0xFF when the `j` bytes at `q`
are zero and 4 otherwise, changing only `a0` through `a2`. -/
theorem reserved_loop {Mx : Word → BitVec 8} {base : Word} (hc : CodeIn Mx base readerReservedCode)
    (hbase : base.toNat % 2 = 0) :
    ∀ (j : Nat) (q : Word) (m : Machine) (f : Fin 32 → Word), St Mx base m 0x18 f →
      f a0 = q → f a1 = BitVec.ofNat 32 j → j < 2 ^ 32 →
      ∃ m', Steps m m' ∧ St Mx base m' 0x32 (reg m') ∧
        reg m' a0 = (if allZero Mx q j then 0xFF else 4) ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m' r = f r
  | 0, q, m, f, s, _, h1, _ => by
    have hz := s.zero
    obtain ⟨m1, e1, t1⟩ := s.taken hc 0x2E rs_at_18 (by decide) (by rw [h1, hz]; decide)
    obtain ⟨m2, e2, t2⟩ := t1.aluImm hc rs_at_2e (off' := 0x32) (by decide)
    refine ⟨m2, .cons e1 (.single e2), t2.self, ?_, fun r h0 _ _ => ?_⟩
    · rw [t2.regs]; simp +decide only [upd, ite_true, ite_false, allZero, aluEval]; rw [hz]; rfl
    · rw [t2.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0]
  | j + 1, q, m, f, s, h0, h1, hj => by
    have hz := s.zero
    obtain ⟨m1, e1, t1⟩ := s.notTaken hc 0x1A rs_at_18 (by decide) (by
      simp only [branchTaken, h1, hz]
      have : BitVec.ofNat 32 (j + 1) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat] at this
        have h0' : (0 : Word).toNat = 0 := rfl
        omega
      exact beq_eq_false_iff_ne.mpr this)
    obtain ⟨m2, e2, t2⟩ := t1.lbu hc rs_at_1a (off' := 0x1E) (by decide)
    rw [h0, add_lit_zero] at t2
    obtain ⟨m3, e3, t3⟩ := t2.aluImm hc rs_at_1e (off' := 0x20) (by decide)
    obtain ⟨m4, e4, t4⟩ := t3.aluImm hc rs_at_20 (off' := 0x22) (by decide)
    have g4 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 →
        upd (upd (upd f a2 ((Mx q).zeroExtend 32)) a0
          (aluEval .add (upd f a2 ((Mx q).zeroExtend 32) a0) 1)) a1
          (aluEval .add (upd (upd f a2 ((Mx q).zeroExtend 32)) a0
            (aluEval .add (upd f a2 ((Mx q).zeroExtend 32) a0) 1) a1) 0xFFFFFFFF) r = f r :=
      fun r h0' h1' h2' => by
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; simp [upd, hz]
        · simp [upd, hr, h0', h1', h2']
    by_cases hq : Mx q = 0
    · obtain ⟨m5, e5, t5⟩ := t4.taken hc 0x18 rs_at_22 (by decide)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hq]; decide)
      obtain ⟨m6, c6, t6, a06, fr6⟩ := reserved_loop hc hbase j (q + 1) m5 _ t5
        (by simp +decide only [upd, ite_true, ite_false, aluEval]; rw [h0]) (by
          simp +decide only [upd, ite_true, ite_false]
          rw [h1]; exact ofNat_succ_dec j) (by omega)
      refine ⟨m6, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 c6)))), t6, ?_, fun r h0' h1' h2' => ?_⟩
      · rw [a06]; simp only [allZero, hq, show ((0 : BitVec 8) == 0) = true from beq_iff_eq.mpr rfl,
          Bool.true_and]
      · rw [fr6 r h0' h1' h2', g4 r h0' h1' h2']
    · obtain ⟨m5, e5, t5⟩ := t4.notTaken hc 0x24 rs_at_22 (by decide)
        (by simp +decide only [upd, ite_true, ite_false]
            simp only [branchTaken, zext_beq_zero]; exact beq_eq_false_iff_ne.mpr hq)
      obtain ⟨m6, e6, t6⟩ := t5.aluImm hc rs_at_24 (off' := 0x26) (by decide)
      obtain ⟨m7, e7, t7⟩ := t6.jump hc rs_at_26 (off' := 0x32) (by decide)
        (by rw [t6.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x32 (by decide)))
      refine ⟨m7, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.single e7)))))), t7.self,
        ?_, fun r h0' h1' h2' => ?_⟩
      · rw [t7.regs]; simp +decide only [upd, ite_true, ite_false, aluEval, allZero]
        simp only [beq_eq_false_iff_ne.mpr hq, Bool.false_and]; rfl
      · rw [t7.regs]
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; simp [upd, hz]
        · simp [upd, hr, h0', h1', h2']

theorem allZero_congr {M M' : Word → BitVec 8} :
    ∀ (k : Nat) (p : Word), (∀ i, i < k → M' (p + BitVec.ofNat 32 i) = M (p + BitVec.ofNat 32 i)) →
      allZero M' p k = allZero M p k
  | 0, _, _ => rfl
  | k + 1, p, h => by
    simp only [allZero]
    have h0 := h 0 (by omega)
    rw [add_ofNat_zero] at h0
    have hk : allZero M' (p + 1) k = allZero M (p + 1) k := allZero_congr k (p + 1) (fun i hi => by
      have := h (1 + i) (by omega)
      rwa [← add_ofNat_assoc] at this)
    rw [h0, hk]

theorem rs_epilogue {m : Machine} {M : Word → BitVec 8} {f : Fin 32 → Word} {base G r0 : Word}
    (hc : CodeIn M base readerReservedCode) (t : St M base m 0x32 f) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) (h1 : memLoad32 M (G + 0x0C) = r0) (hret : r0 &&& ~~~1 = r0) :
    ∃ m', Steps m m' ∧ m'.pc = r0 ∧ m'.mem = M ∧ reg m' sp = G + 0x10 ∧ reg m' ra = r0 ∧
      ∀ r, r ≠ sp → r ≠ ra → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m1, e1, t1⟩ := t.lw hc rs_at_32 (off' := 0x34) (by decide)
    (by rw [hsp]; exact aligned_add hG (k := 0x0C) (by decide))
  rw [hsp, h1] at t1
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc rs_at_34 (off' := 0x36) (by decide)
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := t2.jalr hc rs_at_36
  refine ⟨m3, .cons e1 (.cons e2 (.single e3)), ?_, mem3, ?_, ?_, ?_⟩
  · rw [pc3]; simp +decide only [upd]; simpa using hret
  · rw [regs3]; simp +decide [upd, aluEval, hsp]
  · rw [regs3]; simp +decide [upd]
  · intro r h1' h2'
    rw [regs3]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [hz]
    · simp [upd, hr, h1', h2']

/-- **The compiled `Reader::reserved` is correct.** With its bytes at
`base` and `Reader::bytes`'s where the image puts them, a reader `self` over
a slice that is not null and doesn't wrap, a count `n` that is not zero,
everything aligned, and the 16 bytes of stack below `sp`, the reader, its
position, and its buffer kept apart as the hypotheses list, there is an
execution that reaches the return address with `sp` restored, `a0` as
`reservedResult` says, every register but `a0` through `a5` unchanged, and
memory outside those 16 bytes as `reservedMem` says. -/
theorem readerReserved_correct (m : Machine) (base retAddr self n : Word)
    (hcode : CodeAt m base readerReservedCode)
    (hbcode : CodeAt m (base + 0x9C) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = self) (ha1 : reg m a1 = n) (hn : n ≠ 0) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSr : Sep (reg m sp + 0xFFFFFFF0) 16 base readerReservedCode.length)
    (hSb : Sep (reg m sp + 0xFFFFFFF0) 16 (base + 0x9C) readerBytesCode.length)
    (hEr : Sep (self + 8) 4 base readerReservedCode.length)
    (hEb : Sep (self + 8) 4 (base + 0x9C) readerBytesCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFF0) 16)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFF0) 16)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      reg m' a0 = reservedResult m.mem self n ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFF0) 16 x 1 → m'.mem x = reservedMem m.mem self n x := by
  have hc : CodeIn m.mem base readerReservedCode := hcode
  have s0' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  have hspG : reg m sp = reg m sp + 0xFFFFFFF0 + 0x10 := by
    rw [BitVec.add_assoc]; exact (BitVec.add_zero _).symm
  obtain ⟨G, hGdef⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hGdef] at hSr hSb hRS hBS hspG ⊢
  have hGa : G.toNat % 4 = 0 := hGdef ▸ aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  obtain ⟨ptr, hptr⟩ : ∃ ptr, memLoad32 m.mem self = ptr := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, memLoad32 m.mem (self + 4) = len := ⟨_, rfl⟩
  rw [hptr, hlen] at hbuf hBS hBE
  have sepG : ∀ c l, c + l ≤ 16 → ∀ (b : Word) (k : Nat), Sep G 16 b k →
      Sep (G + BitVec.ofNat 32 c) l b k := fun c l h b k hs => hs.sub (c := c) (l := l) h
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc rs_at_00 (off' := 0x02) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hGdef] at t1
  have r1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  obtain ⟨m2, e2, t2⟩ := t1.sw hc rs_at_02 (off' := 0x04) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 0x0C) (by decide))
  rw [r1sp, show upd (reg m) sp G ra = reg m ra by simp +decide [upd]] at t2
  have hc2 := hc.store32 (v := reg m ra) (show Sep (G + 0x0C) 4 base _ from sepG 0x0C 4 (by omega) _ _ hSr)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 m.mem (G + 0x0C) (reg m ra) = M1 := ⟨_, rfl⟩
  rw [hM1] at t2 hc2
  have M1out : ∀ x, Sep G 16 x 1 → M1 x = m.mem x := fun x h => by
    rw [← hM1, memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from sepG 0x0C 4 (by omega) _ _ h)]
  obtain ⟨m3, e3, t3⟩ := t2.alu hc2 rs_at_04 (off' := 0x06) (by decide)
  obtain ⟨m4, e4, t4⟩ := t3.alu hc2 rs_at_06 (off' := 0x08) (by decide)
  obtain ⟨m5, e5, t5⟩ := t4.aluImm hc2 rs_at_08 (off' := 0x0A) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.auipc hc2 rs_at_0a (off' := 0x0E) (by decide)
  obtain ⟨m7, e7, pc7, mem7, regs7⟩ := t6.call hc2 rs_at_0e
  have r7 : ∀ r, reg m7 r = if r = ra then base + BitVec.ofNat 32 0x12 else
      if r = a0 then G + 4 else if r = a1 then self else if r = a2 then n else
      if r = sp then G else reg m r := by
    intro r; rw [regs7, show base + BitVec.ofNat 32 0x0E + 4 = base + BitVec.ofNat 32 0x12 from
      add_ofNat_assoc base 0x0E 4]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp +decide [upd, hz]
    · by_cases h1 : r = ra
      · subst h1; simp +decide [upd]
      by_cases h2 : r = a0
      · subst h2; simp +decide [upd, aluEval]
      by_cases h3 : r = a1
      · subst h3; simp +decide [upd, aluEval, ha0]
      by_cases h4 : r = a2
      · subst h4; simp +decide [upd, aluEval, ha1]
      by_cases h5 : r = sp
      · subst h5; simp +decide [upd]
      simp [upd, hr, h1, h2, h3, h4, h5]
  have hevb : (base + 0x9C).toNat % 2 = 0 := even_at base hbase 0x9C (by decide)
  have hpc7 : m7.pc = base + 0x9C := by
    rw [pc7]; simp +decide only [upd, ite_true, ite_false]
    rw [show base + BitVec.ofNat 32 0x0A + 0 + 0x92 = base + 0x9C by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl, even_clear _ hevb]
  have hm7 : m7.mem = M1 := mem7
  have hSself : Sep G 16 self 12 := hRS.symm
  have ld1 : ∀ c, c + 4 ≤ 12 → memLoad32 M1 (self + BitVec.ofNat 32 c) =
      memLoad32 m.mem (self + BitVec.ofNat 32 c) := fun c hc' => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact M1out _ (hSself.subR (c := c + j) (l := 1) (by omega))
  have l1p : memLoad32 M1 self = ptr := by
    have := ld1 0 (by omega); rw [add_ofNat_zero] at this; rw [this, hptr]
  have l1l : memLoad32 M1 (self + 4) = len := by
    rw [show self + 4 = self + BitVec.ofNat 32 4 from rfl, ld1 4 (by omega)]; exact hlen
  have l1e : memLoad32 M1 (self + 8) = memLoad32 m.mem (self + 8) := ld1 8 (by omega)
  have hG4 : (G + 4).toNat % 4 = 0 := aligned_add hGa (k := 4) (by decide)
  obtain ⟨m8, c8, pc8, mem8, fr8⟩ := readerBytes_correct m7 (base + 0x9C)
    (base + BitVec.ofNat 32 0x12) (G + 4) self n
    (fun i hi => by rw [hm7, M1out _ (hSb.subR (c := i) (l := 1) (by omega))]; exact hbcode i hi)
    hpc7 (by rw [r7]; simp +decide) (by rw [r7]; simp +decide) (by rw [r7]; simp +decide)
    (by rw [r7]; simp +decide) (even_clear _ (even_at base hbase 0x12 (by decide))) hG4 hself
    (show Sep (G + BitVec.ofNat 32 4) 8 _ _ from sepG 4 8 (by omega) _ _ hSb) hEb
  rw [hm7] at mem8
  have hR : bytesResult (memLoad32 M1 self) (memLoad32 M1 (self + 4)) (memLoad32 M1 (self + 8)) n =
      bytesResult ptr len (memLoad32 m.mem (self + 8)) n := by rw [l1p, l1l, l1e]
  have r8 : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m8 r = reg m7 r := fr8
  have r8sp : reg m8 sp = G := by rw [r8 sp (by decide) (by decide) (by decide), r7]; simp +decide
  have outS : ∀ x, Sep G 16 x 1 → Sep (G + 4) 8 x 1 := fun x h =>
    show Sep (G + BitVec.ofNat 32 4) 8 x 1 from sepG 4 8 (by omega) _ _ h
  have m8x : ∀ x, Sep G 16 x 1 → m8.mem x = reservedMem m.mem self n x := fun x h => by
    rw [mem8, bytesMem_outside (outS x h), hR]
    unfold reservedMem; rw [hptr, hlen]
    rcases bytesResult ptr len (memLoad32 m.mem (self + 8)) n with _ | ⟨q, e'⟩
    · exact M1out x h
    · exact memStore32_congr (M1out x h)
  have codeS : ∀ i, i < readerReservedCode.length → Sep G 16 (base + BitVec.ofNat 32 i) 1 :=
    fun i hi => hSr.subR (c := i) (l := 1) (by omega)
  have hc8 : CodeIn m8.mem base readerReservedCode := fun i hi => by
    rw [m8x _ (codeS i hi)]; unfold reservedMem; rw [hptr, hlen]
    rcases bytesResult ptr len (memLoad32 m.mem (self + 8)) n with _ | ⟨q, e'⟩
    · exact hc i hi
    · dsimp only; rw [memStore32_get_sep (hEr.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have slot : memLoad32 m8.mem (G + 0x0C) = reg m ra := by
    rw [mem8, show G + 0x0C = G + BitVec.ofNat 32 0x0C from rfl, bytesMem_load (out := G + 4)
      (show Sep (G + 4) 8 (G + BitVec.ofNat 32 0x0C) 4 from
        sep_offsets G (c := 4) (n := 8) (d := 0x0C) (k := 4) (by omega) (by omega) (by omega))
      ((hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 0x0C) (l := 4) (by omega)), ← hM1]
    exact memLoad32_store32_same _ _ _
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  have keep8 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp →
      reg m8 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 => by
    rw [r8 r h3 h4 h5, r7]; simp [h0, h1, h2, h6, h7]
  have fin : ∀ (k : Machine) (g : Fin 32 → Word),
      (∀ r, r ≠ sp → r ≠ ra → reg k r = g r) → reg k sp = G + 0x10 → reg k ra = reg m ra →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → g r = reg m r) →
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg k r = reg m r :=
    fun k g hk hsp' hra' hg r h0 h1 h2 h3 h4 h5 => by
      by_cases e1 : r = sp
      · subst e1; rw [hsp', ← hspG]
      by_cases e2 : r = ra
      · subst e2; exact hra'
      rw [hk r e1 e2]; exact hg r h0 h1 h2 h3 h4 h5 e2 e1
  have t8 : St m8.mem base m8 0x12 (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  have hz8 := t8.zero
  obtain ⟨n1, d1, u1⟩ := t8.lw hc8 rs_at_12 (off' := 0x14) (by decide)
    (by rw [r8sp]; exact hG4)
  rw [r8sp] at u1
  rcases hR1 : bytesResult ptr len (memLoad32 m.mem (self + 8)) n with _ | ⟨p, e⟩
  · obtain ⟨b0, b4⟩ := bytesMem_none (out := G + 4) (hR.trans hR1)
    rw [← mem8] at b0 b4
    rw [b0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.taken hc8 0x28 rs_at_14 (by decide) (by simp +decide [upd])
    obtain ⟨n3, d3, u3⟩ := u2.lbu hc8 rs_at_28 (off' := 0x2C) (by decide)
    rw [show upd (reg m8) a0 0 sp = G by simp +decide [upd, r8sp],
      show G + 8 = G + 4 + 4 by rw [BitVec.add_assoc]; rfl, b4] at u3
    obtain ⟨n4, d4, u4⟩ := u3.jump hc8 rs_at_2c (off' := 0x32) (by decide)
      (by rw [u3.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x32 (by decide)))
    obtain ⟨n5, c5, pc5, mem5, sp5, ra5, fr5⟩ := rs_epilogue (r0 := reg m ra) hc8 u4
      (by simp +decide [upd, r8sp]) hGa slot hret'
    refine ⟨n5, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (c8.trans
      (.cons d1 (.cons d2 (.cons d3 (.cons d4 c5))))))))))), by rw [pc5, hra], by rw [sp5, ← hspG],
      ?_, ?_, ?_⟩
    · rw [fr5 a0 (by decide) (by decide)]
      unfold reservedResult; rw [hptr, hlen, hR1]; simp +decide [upd]
    · refine fin n5 _ fr5 sp5 ra5 fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0]
        exact keep8 r h0 h1 h2 h3 h4 h5 h6 h7
    · intro x hx; rw [mem5]; exact m8x x hx
  · obtain ⟨b0, b4⟩ := bytesMem_some (out := G + 4) (hR.trans hR1)
    rw [← mem8] at b0 b4
    rw [b0] at u1
    have hp0 : p ≠ 0 := bytesResult_ne_zero hbuf.1 hbuf.2 hn hR1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hc8 0x16 rs_at_14 (by decide)
      (by simp +decide only [upd, ite_true, ite_false]; simpa [branchTaken] using hp0)
    have q2sp : upd (reg m8) a0 p sp = G := by simp +decide [upd, r8sp]
    obtain ⟨n3, d3, u3⟩ := u2.lw hc8 rs_at_16 (off' := 0x18) (by decide)
      (by rw [q2sp]; exact aligned_add hGa (k := 8) (by decide))
    rw [q2sp, show G + 8 = G + 4 + 4 by rw [BitVec.add_assoc]; rfl, b4] at u3
    obtain ⟨n4, c4, u4, a04, fr4⟩ := reserved_loop hc8 hbase n.toNat p n3 _ u3
      (by simp +decide [upd]) (by simp +decide [upd]) n.isLt
    have hR' := hR1
    rw [bytesResult_eq] at hR'
    split at hR'
    case isFalse => cases hR'
    rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨hp1, -⟩ := hR'
    have hz' : allZero m8.mem p n.toNat = allZero m.mem p n.toNat := allZero_congr _ _ fun i hi => by
      have hpk : p + BitVec.ofNat 32 i =
          ptr + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + i) := by
        rw [← hp1, ← add_ofNat_assoc, ofNat_toNat_self]
      have bS : Sep G 16 (p + BitVec.ofNat 32 i) 1 := by
        rw [hpk]; exact (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + i) (l := 1) (by omega)).symm
      have bE : Sep (self + 8) 4 (p + BitVec.ofNat 32 i) 1 := by
        rw [hpk]; exact (hBE.sub (c := (memLoad32 m.mem (self + 8)).toNat + i) (l := 1) (by omega)).symm
      rw [m8x _ bS]; unfold reservedMem; rw [hptr, hlen, hR1]; exact memStore32_get_sep bE
    obtain ⟨n5, c5, pc5, mem5, sp5, ra5, fr5⟩ := rs_epilogue (r0 := reg m ra) hc8 u4
      (by rw [fr4 sp (by decide) (by decide) (by decide)]; simp +decide [upd, r8sp]) hGa slot hret'
    refine ⟨n5, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (c8.trans
      (.cons d1 (.cons d2 (.cons d3 (c4.trans c5))))))))))), by rw [pc5, hra], by rw [sp5, ← hspG],
      ?_, ?_, ?_⟩
    · rw [fr5 a0 (by decide) (by decide), a04, hz']
      unfold reservedResult; rw [hptr, hlen, hR1]
    · refine fin n5 _ fr5 sp5 ra5 fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_
      rw [fr4 r h0 h1 h2]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1]
        exact keep8 r h0 h1 h2 h3 h4 h5 h6 h7
    · intro x hx; rw [mem5]; exact m8x x hx

end C3.RV32
