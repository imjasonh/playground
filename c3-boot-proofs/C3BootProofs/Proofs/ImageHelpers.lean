import C3BootProofs.Proofs.Reserved
import C3BootProofs.Proofs.ReaderU32

/-!
# Functions `image::parse` calls, as compiled

`Reader::u8`, `Segment::physical`, and `memcpy`, proved as compiled.
`image::parse` calls each through these theorems.
-/

namespace C3.RV32

open C3.ImageV0

abbrev s0' : Fin 32 := 8

/-! ## `Reader::u8` -/

/-- What `Reader::u8` returns: the error flag in `a0` and the byte or the
error in `a1`. `Reader::bytes` reports only `Truncated` (0). -/
def u8Result (M : Word → BitVec 8) (self : Word) : Word × Word :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 1 with
  | none => (1, 0)
  | some (p, _) => (0, (M p).zeroExtend 32)

theorem u8_at_0 : fetchRel readerU8Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem u8_at_2 : fetchRel readerU8Code 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem u8_at_4 : fetchRel readerU8Code 0x4 = some (.store .sw sp s0 0x8, 2) := by decide
theorem u8_at_6 : fetchRel readerU8Code 0x6 = some (.alu .add a1 x0 a0, 2) := by decide
theorem u8_at_8 : fetchRel readerU8Code 0x8 = some (.alu .add a0 x0 sp, 2) := by decide
theorem u8_at_a : fetchRel readerU8Code 0xA = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem u8_at_c : fetchRel readerU8Code 0xC = some (.aluImm .add s0 x0 0x1, 2) := by decide
theorem u8_at_e : fetchRel readerU8Code 0xE = some (.auipc ra 0x0, 4) := by decide
theorem u8_at_12 : fetchRel readerU8Code 0x12 = some (.jalr ra ra 0xC8, 4) := by decide
theorem u8_at_16 : fetchRel readerU8Code 0x16 = some (.load .lw a0 sp 0x0, 2) := by decide
theorem u8_at_18 : fetchRel readerU8Code 0x18 = some (.branch .beq a0 x0 0x10, 2) := by decide
theorem u8_at_1a : fetchRel readerU8Code 0x1A = some (.load .lw a1 sp 0x4, 2) := by decide
theorem u8_at_1c : fetchRel readerU8Code 0x1C = some (.branch .bne a1 s0 0x12, 4) := by decide
theorem u8_at_20 : fetchRel readerU8Code 0x20 = some (.load .lbu a1 a0 0x0, 4) := by decide
theorem u8_at_24 : fetchRel readerU8Code 0x24 = some (.aluImm .add s0 x0 0x0, 2) := by decide
theorem u8_at_26 : fetchRel readerU8Code 0x26 = some (.jal x0 0xA, 2) := by decide
theorem u8_at_28 : fetchRel readerU8Code 0x28 = some (.load .lbu a1 sp 0x4, 4) := by decide
theorem u8_at_2c : fetchRel readerU8Code 0x2C = some (.jal x0 0x4, 2) := by decide
theorem u8_at_2e : fetchRel readerU8Code 0x2E = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem u8_at_30 : fetchRel readerU8Code 0x30 = some (.alu .add a0 x0 s0, 2) := by decide
theorem u8_at_32 : fetchRel readerU8Code 0x32 = some (.load .lw ra sp 0xC, 2) := by decide
theorem u8_at_34 : fetchRel readerU8Code 0x34 = some (.load .lw s0 sp 0x8, 2) := by decide
theorem u8_at_36 : fetchRel readerU8Code 0x36 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem u8_at_38 : fetchRel readerU8Code 0x38 = some (.jalr x0 ra 0x0, 2) := by decide

theorem u8_epilogue {m : Machine} {M : Word → BitVec 8} {f : Fin 32 → Word} {base G r0 r8 : Word}
    (hc : CodeIn M base readerU8Code) (t : St M base m 0x30 f) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) (h1 : memLoad32 M (G + 0x0C) = r0) (h2 : memLoad32 M (G + 8) = r8)
    (hret : r0 &&& ~~~1 = r0) :
    ∃ m', Steps m m' ∧ m'.pc = r0 ∧ m'.mem = M ∧ reg m' sp = G + 0x10 ∧ reg m' ra = r0 ∧
      reg m' s0 = r8 ∧ reg m' a0 = f s0 ∧ ∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → r ≠ a0 → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m0, e0, t0'⟩ := t.alu hc u8_at_30 (off' := 0x32) (by decide)
  have u0 : upd f a0 (aluEval .add (f x0) (f s0)) sp = G := by simp +decide [upd, hsp]
  obtain ⟨m1, e1, t1⟩ := t0'.lw hc u8_at_32 (off' := 0x34) (by decide)
    (by rw [u0]; exact aligned_add hG (k := 0x0C) (by decide))
  rw [u0, h1] at t1
  have u1 : upd (upd f a0 (aluEval .add (f x0) (f s0))) ra r0 sp = G := by simp +decide [upd, hsp]
  obtain ⟨m2, e2, t2⟩ := t1.lw hc u8_at_34 (off' := 0x36) (by decide)
    (by rw [u1]; exact aligned_add hG (k := 8) (by decide))
  rw [u1, h2] at t2
  obtain ⟨m3, e3, t3⟩ := t2.aluImm hc u8_at_36 (off' := 0x38) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := t3.jalr hc u8_at_38
  refine ⟨m4, .cons e0 (.cons e1 (.cons e2 (.cons e3 (.single e4)))), ?_, mem4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc4]; simp +decide only [upd]; simpa using hret
  · rw [regs4]; simp +decide [upd, aluEval, hsp]
  · rw [regs4]; simp +decide [upd]
  · rw [regs4]; simp +decide [upd]
  · rw [regs4]; simp +decide [upd, aluEval, hz]
  · intro r h1' h2' h3' h4'
    rw [regs4]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [hz]
    · simp [upd, hr, h1', h2', h3', h4']

/-- **The compiled `Reader::u8` is correct.** It returns `u8Result` in `a0`
and `a1`, restores `sp` and every register but `a0` through `a5`, and leaves
memory outside its 16 bytes of stack as `reservedMem` with `n = 1` says:
the position advanced by 1 when a byte was left. -/
theorem readerU8_correct (m : Machine) (base retAddr self : Word)
    (hcode : CodeAt m base readerU8Code)
    (hbcode : CodeAt m (base + 0xD6) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = self) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSr : Sep (reg m sp + 0xFFFFFFF0) 16 base readerU8Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFF0) 16 (base + 0xD6) readerBytesCode.length)
    (hEr : Sep (self + 8) 4 base readerU8Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xD6) readerBytesCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFF0) 16)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFF0) 16)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      reg m' a0 = (u8Result m.mem self).1 ∧ reg m' a1 = (u8Result m.mem self).2 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFF0) 16 x 1 → m'.mem x = reservedMem m.mem self 1 x := by
  have hc : CodeIn m.mem base readerU8Code := hcode
  have s0'' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0''.zero
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
  obtain ⟨m1, e1, t1⟩ := s0''.aluImm hc u8_at_0 (off' := 0x02) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hGdef] at t1
  have r1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  obtain ⟨m2, e2, t2⟩ := t1.sw hc u8_at_2 (off' := 0x04) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 0x0C) (by decide))
  rw [r1sp, show upd (reg m) sp G ra = reg m ra by simp +decide [upd]] at t2
  have hc2 := hc.store32 (v := reg m ra) (show Sep (G + 0x0C) 4 base _ from sepG 0x0C 4 (by omega) _ _ hSr)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 u8_at_4 (off' := 0x06) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [r1sp, show upd (reg m) sp G s0 = reg m s0 by simp +decide [upd]] at t3
  have hc3 := hc2.store32 (v := reg m s0) (show Sep (G + 8) 4 base _ from sepG 8 4 (by omega) _ _ hSr)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0) = M1 :=
    ⟨_, rfl⟩
  rw [hM1] at t3 hc3
  have M1out : ∀ x, Sep G 16 x 1 → M1 x = m.mem x := fun x h => by
    rw [← hM1, memStore32_get_sep (show Sep (G + 8) 4 x 1 from sepG 8 4 (by omega) _ _ h),
      memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from sepG 0x0C 4 (by omega) _ _ h)]
  obtain ⟨m4, e4, t4⟩ := t3.alu hc3 u8_at_6 (off' := 0x08) (by decide)
  obtain ⟨m5, e5, t5⟩ := t4.alu hc3 u8_at_8 (off' := 0x0A) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.aluImm hc3 u8_at_a (off' := 0x0C) (by decide)
  obtain ⟨m6', e6', t6'⟩ := t6.aluImm hc3 u8_at_c (off' := 0x0E) (by decide)
  obtain ⟨m7a, e7a, t7a⟩ := t6'.auipc hc3 u8_at_e (off' := 0x12) (by decide)
  obtain ⟨m7, e7, pc7, mem7, regs7⟩ := t7a.call hc3 u8_at_12
  have r7 : ∀ r, reg m7 r = if r = ra then base + BitVec.ofNat 32 0x16 else
      if r = a0 then G else if r = a1 then self else if r = a2 then 1 else
      if r = s0 then 1 else if r = sp then G else reg m r := by
    intro r; rw [regs7, show base + BitVec.ofNat 32 0x12 + 4 = base + BitVec.ofNat 32 0x16 from
      add_ofNat_assoc base 0x12 4]
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
      · subst h4; simp +decide [upd, aluEval]
      by_cases h5 : r = s0
      · subst h5; simp +decide [upd, aluEval]
      by_cases h6 : r = sp
      · subst h6; simp +decide [upd]
      simp [upd, hr, h1, h2, h3, h4, h5, h6]
  have hevb : (base + 0xD6).toNat % 2 = 0 := even_at base hbase 0xD6 (by decide)
  have hpc7 : m7.pc = base + 0xD6 := by
    rw [pc7]; simp +decide only [upd, ite_true, ite_false]
    rw [show base + BitVec.ofNat 32 0x0E + 0 + 0xC8 = base + 0xD6 by
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
  obtain ⟨m8, c8, pc8, mem8, fr8⟩ := readerBytes_correct m7 (base + 0xD6)
    (base + BitVec.ofNat 32 0x16) G self 1
    (fun i hi => by rw [hm7, M1out _ (hSb.subR (c := i) (l := 1) (by omega))]; exact hbcode i hi)
    hpc7 (by rw [r7]; simp +decide) (by rw [r7]; simp +decide) (by rw [r7]; simp +decide)
    (by rw [r7]; simp +decide) (even_clear _ (even_at base hbase 0x16 (by decide))) hGa hself
    (by have := sepG 0 8 (by omega) _ _ hSb; rwa [add_ofNat_zero] at this) hEb
  rw [hm7] at mem8
  have hR : bytesResult (memLoad32 M1 self) (memLoad32 M1 (self + 4)) (memLoad32 M1 (self + 8)) 1 =
      bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 := by rw [l1p, l1l, l1e]
  have r8 : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m8 r = reg m7 r := fr8
  have r8sp : reg m8 sp = G := by rw [r8 sp (by decide) (by decide) (by decide), r7]; simp +decide
  have r8s0 : reg m8 s0 = 1 := by rw [r8 s0 (by decide) (by decide) (by decide), r7]; simp +decide
  have outS : ∀ x, Sep G 16 x 1 → Sep G 8 x 1 := fun x h => by
    have := sepG 0 8 (by omega) _ _ h; rwa [add_ofNat_zero] at this
  have m8x : ∀ x, Sep G 16 x 1 → m8.mem x = reservedMem m.mem self 1 x := fun x h => by
    rw [mem8, bytesMem_outside (outS x h), hR]
    unfold reservedMem; rw [hptr, hlen]
    rcases bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 with _ | ⟨q, e'⟩
    · exact M1out x h
    · exact memStore32_congr (M1out x h)
  have codeS : ∀ i, i < readerU8Code.length → Sep G 16 (base + BitVec.ofNat 32 i) 1 :=
    fun i hi => hSr.subR (c := i) (l := 1) (by omega)
  have hc8 : CodeIn m8.mem base readerU8Code := fun i hi => by
    rw [m8x _ (codeS i hi)]; unfold reservedMem; rw [hptr, hlen]
    rcases bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 with _ | ⟨q, e'⟩
    · exact hc i hi
    · dsimp only; rw [memStore32_get_sep (hEr.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have slot : ∀ c, c = 8 ∨ c = 0x0C → memLoad32 m8.mem (G + BitVec.ofNat 32 c) =
      memLoad32 M1 (G + BitVec.ofNat 32 c) := by
    intro c hc'
    rw [mem8, bytesMem_load (out := G)
      (by have := sep_offsets G (c := 0) (n := 8) (d := c) (k := 4) (by omega) (by omega) (by omega)
          rwa [add_ofNat_zero] at this)
      ((hRS.sub (c := 8) (l := 4) (by omega)).subR (c := c) (l := 4) (by omega))]
  have slotRa : memLoad32 m8.mem (G + 0x0C) = reg m ra := by
    rw [show G + 0x0C = G + BitVec.ofNat 32 0x0C from rfl, slot 0x0C (by omega), ← hM1,
      memLoad32_store32_sep (show Sep (G + 8) 4 (G + BitVec.ofNat 32 0x0C) 4 from
        sep_offsets G (c := 8) (n := 4) (d := 0x0C) (k := 4) (by omega) (by omega) (by omega))]
    exact memLoad32_store32_same _ _ _
  have slotS0 : memLoad32 m8.mem (G + 8) = reg m s0 := by
    rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, slot 8 (by omega), ← hM1]
    exact memLoad32_store32_same _ _ _
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  have t8 : St m8.mem base m8 0x16 (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
  have hz8 := t8.zero
  obtain ⟨n1, d1, u1⟩ := t8.lw hc8 u8_at_16 (off' := 0x18) (by decide)
    (by rw [r8sp, add_lit_zero]; exact hGa)
  rw [r8sp, add_lit_zero] at u1
  have keep : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ s0 →
      reg m8 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [r8 r h3 h4 h5, r7]; simp [h0, h1, h2, h6, h7, h8]
  have pre : Steps m m8 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e6'
    (.cons e7a (.cons e7 c8))))))))
  have fin : ∀ (k : Machine) (g : Fin 32 → Word),
      (∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → r ≠ a0 → reg k r = g r) → reg k sp = G + 0x10 →
      reg k ra = reg m ra → reg k s0 = reg m s0 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ s0 → g r = reg m r) →
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg k r = reg m r :=
    fun k g hk hsp' hra' hs0' hg r h0 h1 h2 h3 h4 h5 => by
      by_cases e1 : r = sp
      · subst e1; rw [hsp', ← hspG]
      by_cases e2 : r = ra
      · subst e2; exact hra'
      by_cases e3 : r = s0
      · subst e3; exact hs0'
      rw [hk r e1 e2 e3 h0]; exact hg r h0 h1 h2 h3 h4 h5 e2 e1 e3
  rcases hR1 : bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 with _ | ⟨p, e⟩
  · obtain ⟨b0, b4⟩ := bytesMem_none (out := G) (hR.trans hR1)
    rw [← mem8] at b0 b4
    rw [b0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.taken hc8 0x28 u8_at_18 (by decide) (by simp +decide [upd])
    obtain ⟨n3, d3, u3⟩ := u2.lbu hc8 u8_at_28 (off' := 0x2C) (by decide)
    rw [show upd (reg m8) a0 0 sp = G by simp +decide [upd, r8sp], b4] at u3
    obtain ⟨n4, d4, u4⟩ := u3.jump hc8 u8_at_2c (off' := 0x30) (by decide)
      (by rw [u3.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x30 (by decide)))
    obtain ⟨n5, c5, pc5, mem5, sp5, ra5, s05, a05, fr5⟩ := u8_epilogue (r0 := reg m ra) hc8 u4
      (by simp +decide [upd, r8sp]) hGa slotRa slotS0 hret'
    refine ⟨n5, pre.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 c5)))), by rw [pc5, hra],
      by rw [sp5, ← hspG], ?_, ?_, ?_, ?_⟩
    · rw [a05]; unfold u8Result; rw [hptr, hlen, hR1]; simp +decide [upd, r8s0]
    · rw [fr5 a1 (by decide) (by decide) (by decide) (by decide)]
      unfold u8Result; rw [hptr, hlen, hR1]; simp +decide [upd]
    · refine fin n5 _ fr5 sp5 ra5 s05 fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 => ?_
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1]
        exact keep r h0 h1 h2 h3 h4 h5 h6 h7 h8
    · intro x hx; rw [mem5]; exact m8x x hx
  · obtain ⟨b0, b4⟩ := bytesMem_some (out := G) (hR.trans hR1)
    rw [← mem8] at b0 b4
    rw [b0] at u1
    have hp0 : p ≠ 0 := bytesResult_ne_zero hbuf.1 hbuf.2 (by decide) hR1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hc8 0x1A u8_at_18 (by decide)
      (by simp +decide only [upd, ite_true, ite_false]; simpa [branchTaken] using hp0)
    have q2sp : upd (reg m8) a0 p sp = G := by simp +decide [upd, r8sp]
    obtain ⟨n3, d3, u3⟩ := u2.lw hc8 u8_at_1a (off' := 0x1C) (by decide)
      (by rw [q2sp]; exact aligned_add hGa (k := 4) (by decide))
    rw [q2sp, b4] at u3
    obtain ⟨n4, d4, u4⟩ := u3.notTaken hc8 0x20 u8_at_1c (by decide)
      (by simp +decide [upd, r8s0])
    obtain ⟨n5, d5, u5⟩ := u4.lbu hc8 u8_at_20 (off' := 0x24) (by decide)
    rw [show upd (upd (reg m8) a0 p) a1 1 a0 = p by simp +decide [upd], add_lit_zero] at u5
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hc8 u8_at_24 (off' := 0x26) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.jump hc8 u8_at_26 (off' := 0x30) (by decide)
      (by rw [u6.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x30 (by decide)))
    obtain ⟨n8, c9, pc9, mem9, sp9, ra9, s09, a09, fr9⟩ := u8_epilogue (r0 := reg m ra) hc8 u7
      (by simp +decide [upd, r8sp]) hGa slotRa slotS0 hret'
    have hR' := hR1
    rw [bytesResult_eq] at hR'
    split at hR'
    case isFalse => cases hR'
    rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨hp1, -⟩ := hR'
    have hpk : p = ptr + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + 0) := by
      rw [← hp1, Nat.add_zero, ofNat_toNat_self]
    have hb1 : (memLoad32 m.mem (self + 8)).toNat + 0 < len.toNat := by
      have : (1 : Word).toNat = 1 := rfl; omega
    have bS : Sep G 16 p 1 := by
      rw [hpk]; exact (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + 0) (l := 1) (by omega)).symm
    have bE : Sep (self + 8) 4 p 1 := by
      rw [hpk]; exact (hBE.sub (c := (memLoad32 m.mem (self + 8)).toNat + 0) (l := 1) (by omega)).symm
    have hbyte : m8.mem p = m.mem p := by
      rw [m8x _ bS]; unfold reservedMem; rw [hptr, hlen, hR1]; exact memStore32_get_sep bE
    refine ⟨n8, pre.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c9))))))),
      by rw [pc9, hra], by rw [sp9, ← hspG], ?_, ?_, ?_, ?_⟩
    · rw [a09]; unfold u8Result; rw [hptr, hlen, hR1]; simp +decide [upd, aluEval]
    · rw [fr9 a1 (by decide) (by decide) (by decide) (by decide)]
      unfold u8Result; rw [hptr, hlen, hR1]; simp +decide [upd, hbyte]
    · refine fin n8 _ fr9 sp9 ra9 s09 fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 => ?_
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1, h8]
        exact keep r h0 h1 h2 h3 h4 h5 h6 h7 h8
    · intro x hx; rw [mem9]; exact m8x x hx

/-! ## `Segment::physical` -/

/-- What `Segment::physical` decides for a segment of kind byte `kind` at
`addr`: its address space (0 for the flash cache's linear space, 1 for
SRAM) and its start there, or `none` for `BadSegment`. The kind bytes are
Rust's discriminants: flash code, flash data, RAM code, RAM data. -/
def physResult (kind : BitVec 8) (addr : Word) : Option (BitVec 8 × Word) :=
  if kind = 0 then (if addr.ult 0x42000000 then none else some (0, addr + 0xBE000000))
  else if kind = 1 then (if addr.ult 0x3C000000 then none else some (0, addr + 0xC4000000))
  else if kind = 2 then (if addr.ult 0x700000 then none else some (1, addr + 0xFF900000))
  else some (1, addr)

/-- Memory after `Segment::physical` writes its `Result` through `out`. -/
def physMem (M : Word → BitVec 8) (out : Word) (kind : BitVec 8) (addr : Word) : Word → BitVec 8 :=
  match physResult kind addr with
  | none => memStore8 (memStore8 M (out + 1) 9) out 2
  | some (t, v) =>
    if kind = 0 ∨ kind = 1 ∨ kind = 2 then memStore8 (memStore32 M (out + 4) v) out t
    else memStore32 (memStore8 M out t) (out + 4) v

theorem ph_at_0 : fetchRel segmentPhysicalCode 0x0 = some (.aluImm .and a2 a2 0xFF, 4) := by decide
theorem ph_at_4 : fetchRel segmentPhysicalCode 0x4 = some (.branch .beq a2 x0 0x38, 2) := by decide
theorem ph_at_6 : fetchRel segmentPhysicalCode 0x6 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem ph_at_8 : fetchRel segmentPhysicalCode 0x8 = some (.branch .beq a2 a3 0x22, 4) := by decide
theorem ph_at_c : fetchRel segmentPhysicalCode 0xC = some (.aluImm .add a3 x0 0x2, 2) := by decide
theorem ph_at_e : fetchRel segmentPhysicalCode 0xE = some (.branch .bne a2 a3 0x44, 4) := by decide
theorem ph_at_12 : fetchRel segmentPhysicalCode 0x12 = some (.aluImm .srl a3 a1 0x14, 4) := by decide
theorem ph_at_16 : fetchRel segmentPhysicalCode 0x16 = some (.aluImm .sltu a2 a3 0x7, 4) := by decide
theorem ph_at_1a : fetchRel segmentPhysicalCode 0x1A = some (.aluImm .add a4 x0 0x7, 2) := by decide
theorem ph_at_1c : fetchRel segmentPhysicalCode 0x1C = some (.aluImm .add a2 a2 0x1, 2) := by decide
theorem ph_at_1e : fetchRel segmentPhysicalCode 0x1E = some (.branch .bgeu a3 a4 0x46, 4) := by decide
theorem ph_at_22 : fetchRel segmentPhysicalCode 0x22 = some (.aluImm .add a1 x0 0x9, 2) := by decide
theorem ph_at_24 : fetchRel segmentPhysicalCode 0x24 = some (.store .sb a0 a1 0x1, 4) := by decide
theorem ph_at_28 : fetchRel segmentPhysicalCode 0x28 = some (.jal x0 0x44, 2) := by decide
theorem ph_at_2a : fetchRel segmentPhysicalCode 0x2A = some (.aluImm .srl a2 a1 0x1A, 4) := by decide
theorem ph_at_2e : fetchRel segmentPhysicalCode 0x2E = some (.aluImm .add a3 x0 0xF, 2) := by decide
theorem ph_at_30 : fetchRel segmentPhysicalCode 0x30 = some (.branch .bltu a2 a3 0x18, 4) := by decide
theorem ph_at_34 : fetchRel segmentPhysicalCode 0x34 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem ph_at_36 : fetchRel segmentPhysicalCode 0x36 = some (.lui a3 0xC4000000, 4) := by decide
theorem ph_at_3a : fetchRel segmentPhysicalCode 0x3A = some (.jal x0 0x2E, 2) := by decide
theorem ph_at_3c : fetchRel segmentPhysicalCode 0x3C = some (.aluImm .srl a2 a1 0x19, 4) := by decide
theorem ph_at_40 : fetchRel segmentPhysicalCode 0x40 = some (.aluImm .add a3 x0 0x21, 4) := by decide
theorem ph_at_44 : fetchRel segmentPhysicalCode 0x44 = some (.branch .bgeu a2 a3 0x18, 4) := by decide
theorem ph_at_48 : fetchRel segmentPhysicalCode 0x48 = some (.aluImm .add a1 x0 0x9, 2) := by decide
theorem ph_at_4a : fetchRel segmentPhysicalCode 0x4A = some (.store .sb a0 a1 0x1, 4) := by decide
theorem ph_at_4e : fetchRel segmentPhysicalCode 0x4E = some (.aluImm .add a2 x0 0x2, 2) := by decide
theorem ph_at_50 : fetchRel segmentPhysicalCode 0x50 = some (.jal x0 0x1C, 2) := by decide
theorem ph_at_52 : fetchRel segmentPhysicalCode 0x52 = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem ph_at_54 : fetchRel segmentPhysicalCode 0x54 = some (.store .sb a0 a2 0x0, 4) := by decide
theorem ph_at_58 : fetchRel segmentPhysicalCode 0x58 = some (.store .sw a0 a1 0x4, 2) := by decide
theorem ph_at_5a : fetchRel segmentPhysicalCode 0x5A = some (.jalr x0 ra 0x0, 2) := by decide
theorem ph_at_5c : fetchRel segmentPhysicalCode 0x5C = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem ph_at_5e : fetchRel segmentPhysicalCode 0x5E = some (.lui a3 0xBE000000, 4) := by decide
theorem ph_at_62 : fetchRel segmentPhysicalCode 0x62 = some (.jal x0 0x6, 2) := by decide
theorem ph_at_64 : fetchRel segmentPhysicalCode 0x64 = some (.lui a3 0xFF900000, 4) := by decide
theorem ph_at_68 : fetchRel segmentPhysicalCode 0x68 = some (.alu .add a1 a1 a3, 2) := by decide
theorem ph_at_6a : fetchRel segmentPhysicalCode 0x6A = some (.store .sw a0 a1 0x4, 2) := by decide
theorem ph_at_6c : fetchRel segmentPhysicalCode 0x6C = some (.store .sb a0 a2 0x0, 4) := by decide
theorem ph_at_70 : fetchRel segmentPhysicalCode 0x70 = some (.jalr x0 ra 0x0, 2) := by decide

theorem physMem_k {M : Word → BitVec 8} {out addr : Word} {lo off : Word} {t : BitVec 8} (k : BitVec 8)
    (hk : k = 0 ∨ k = 1 ∨ k = 2)
    (hr : physResult k addr = if addr.ult lo then none else some (t, addr + off)) :
    physMem M out k addr = if addr.ult lo then memStore8 (memStore8 M (out + 1) 9) out 2
      else memStore8 (memStore32 M (out + 4) (addr + off)) out t := by
  unfold physMem; rw [hr]
  cases addr.ult lo
  · simp only [Bool.false_eq_true, ↓reduceIte, hk]
  · rfl

theorem physMem_other {M : Word → BitVec 8} {out addr : Word} (k : BitVec 8)
    (h0 : k ≠ 0) (h1 : k ≠ 1) (h2 : k ≠ 2) :
    physMem M out k addr = memStore32 (memStore8 M out 1) (out + 4) addr := by
  unfold physMem physResult
  simp only [h0, h1, h2, ↓reduceIte, or_self]

theorem shr_ult_iff (x : Word) (k c : Nat) (_hk : k < 32) (hc : c * 2 ^ k < 2 ^ 32) :
    (x >>> k).ult (BitVec.ofNat 32 c) = x.ult (BitVec.ofNat 32 (c * 2 ^ k)) := by
  simp only [BitVec.ult, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hc' : c < 2 ^ 32 := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right c this) hc
  rw [Nat.mod_eq_of_lt hc', Nat.mod_eq_of_lt hc]
  apply decide_eq_decide.mpr
  exact Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)

theorem zext_and_ff (b : BitVec 8) : aluEval .and (b.zeroExtend 32) 0xFF = b.zeroExtend 32 := by
  revert b; decide

/-- **The compiled `Segment::physical` is correct.** For a segment of kind
byte `kind` (zero-extended in `a2`) at `addr`, it writes the `Result` that
`physResult` gives through `out`, as `physMem` says, changes only `a1`
through `a4` among the registers, and returns. -/
theorem segmentPhysical_correct (m : Machine) (base retAddr out addr : Word) (k : BitVec 8)
    (hcode : CodeAt m base segmentPhysicalCode) (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = addr) (ha2 : reg m a2 = k.zeroExtend 32)
    (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0)
    (hsep : Sep out 8 base segmentPhysicalCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = physMem m.mem out k addr ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r := by
  have hc : CodeIn m.mem base segmentPhysicalCode := hcode
  have s0'' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0''.zero
  have sO : ∀ c l, c + l ≤ 8 → Sep (out + BitVec.ofNat 32 c) l base segmentPhysicalCode.length :=
    fun c l h => hsep.sub (c := c) (l := l) h
  have s0o : Sep out 1 base segmentPhysicalCode.length := by
    have := sO 0 1 (by omega); rwa [add_ofNat_zero] at this
  have s1o : Sep (out + 1) 1 base segmentPhysicalCode.length := sO 1 1 (by omega)
  have s4o : Sep (out + 4) 4 base segmentPhysicalCode.length := sO 4 4 (by omega)
  have hand : aluEval .and (k.zeroExtend 32) 0xFF = k.zeroExtend 32 := zext_and_ff k
  obtain ⟨m1, e1, t1⟩ := s0''.aluImm hc ph_at_0 (off' := 0x4) (by decide)
  rw [ha2, hand] at t1
  have zk : ∀ c : Nat, c < 256 → ((k.zeroExtend 32 : Word) == BitVec.ofNat 32 c) = (k == BitVec.ofNat 8 c) := by
    intro c hc'
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this ⊢
      have hk' := k.isLt; omega
    · intro h; subst h; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have stores : ∀ (M : Word → BitVec 8) (v : Word) (t : BitVec 8),
      CodeIn M base segmentPhysicalCode → CodeIn (memStore32 M (out + 4) v) base segmentPhysicalCode ∧
        CodeIn (memStore8 M out t) base segmentPhysicalCode ∧
        CodeIn (memStore8 M (out + 1) t) base segmentPhysicalCode :=
    fun M v t h => ⟨h.store32 s4o, h.store8 s0o, h.store8 s1o⟩
  have frame : ∀ (k' : Machine) (f : Fin 32 → Word), (∀ r, reg k' r = f r) →
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → f r = reg m r) →
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg k' r = reg m r :=
    fun k' f h1 h2 r q1 q2 q3 q4 => (h1 r).trans (h2 r q1 q2 q3 q4)
  have keepU : ∀ (f : Fin 32 → Word) (rd : Fin 32) (v : Word), rd = a1 ∨ rd = a2 ∨ rd = a3 ∨ rd = a4 →
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → f r = reg m r) →
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → upd f rd v r = reg m r := by
    intro f rd v hrd hf r q1 q2 q3 q4
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · have : r ≠ rd := by rcases hrd with rfl | rfl | rfl | rfl <;> assumption
      simp [upd, hr, this]; exact hf r q1 q2 q3 q4
  -- The tails: 0x68 adds the offset, stores the start and the tag, and returns; 0x6C stores the tag.
  have tail6c : ∀ (M : Word → BitVec 8) (n : Machine) (g : Fin 32 → Word), CodeIn M base segmentPhysicalCode →
      St M base n 0x6C g → g a0 = out → g ra = retAddr →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = memStore8 M out ((g a2).extractLsb' 0 8) ∧
        ∀ r, reg n' r = g r := by
    intro M n g hM s ha hr
    obtain ⟨n1, d1, u1⟩ := s.sb hM ph_at_6c (off' := 0x70) (by decide)
    rw [ha, add_lit_zero] at u1
    obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.jalr (hM.store8 s0o) ph_at_70
    refine ⟨n2, .cons d1 (.single d2), by rw [pc2, hr, add_lit_zero, hret], mem2, fun r => ?_⟩
    rw [regs2]
  have tail68 : ∀ (n : Machine) (g : Fin 32 → Word), St m.mem base n 0x68 g → g a0 = out → g ra = retAddr →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧
        n'.mem = memStore8 (memStore32 m.mem (out + 4) (g a1 + g a3)) out ((g a2).extractLsb' 0 8) ∧
        ∀ r, reg n' r = upd g a1 (g a1 + g a3) r := by
    intro n g s ha hr
    obtain ⟨n1, d1, u1⟩ := s.alu hc ph_at_68 (off' := 0x6A) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.sw hc ph_at_6a (off' := 0x6C) (by decide)
      (by simp +decide only [upd, ite_false]; rw [ha]; exact aligned_add hout (k := 4) (by decide))
    simp +decide only [upd, ite_false, ite_true, aluEval] at u2
    rw [ha] at u2
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := tail6c _ n2 _ (hc.store32 s4o) u2
      (by simp +decide [upd, ha]) (by simp +decide [upd, hr])
    refine ⟨n3, .cons d1 (.cons d2 d3), pc3, ?_, fun r => ?_⟩
    · rw [mem3]; simp +decide [upd]
    · rw [regs3]
  have ev : ∀ c : Nat, c < 0x72 → c % 2 = 0 → (base + BitVec.ofNat 32 c).getLsbD 0 = false :=
    fun c h1 h2 => even_bit0 (even_at base hbase c (by omega))
  have srl_eq : ∀ (x : Word) (i : Word), i.toNat < 32 → aluEval .srl x i = x >>> i.toNat := fun x i h => by
    simp only [aluEval, Nat.mod_eq_of_lt h]
  have k1 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m r = reg m r := fun _ _ _ _ _ => rfl
  have kF := keepU _ a2 (k.zeroExtend 32) (by decide) k1
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨m2, e2, t2⟩ := t1.taken hc 0x3C ph_at_4 (by decide) (by simp +decide [upd])
    obtain ⟨m3, e3, t3⟩ := t2.aluImm hc ph_at_3c (off' := 0x40) (by decide)
    obtain ⟨m4, e4, t4⟩ := t3.aluImm hc ph_at_40 (off' := 0x44) (by decide)
    have c4 : (addr >>> 25).ult 0x21 = addr.ult 0x42000000 := shr_ult_iff addr 25 0x21 (by omega) (by decide)
    cases hcnd : addr.ult 0x42000000
    · obtain ⟨m5, e5, t5⟩ := t4.taken hc 0x5C ph_at_44 (by decide) (by
        simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, hz, ha1]
        rw [show (BitVec.toNat (25 : Word)) % 32 = 25 from rfl, show (0 : Word) + 33 = 0x21 from rfl, c4, hcnd]
        rfl)
      obtain ⟨m6, e6, t6⟩ := t5.aluImm hc ph_at_5c (off' := 0x5E) (by decide)
      obtain ⟨m7, e7, t7⟩ := t6.lui hc ph_at_5e (off' := 0x62) (by decide)
      obtain ⟨m8, e8, t8⟩ := t7.jump hc ph_at_62 (off' := 0x68) (by decide)
        (by rw [t7.pc, BitVec.add_assoc]; exact ev 0x68 (by omega) (by omega))
      obtain ⟨m9, c9, pc9, mem9, regs9⟩ := tail68 m8 _ t8 (by simp +decide [upd, ha0])
        (by simp +decide [upd, hra])
      refine ⟨m9, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 c9))))))),
        pc9, ?_, ?_⟩
      · rw [mem9, physMem_k 0 (by decide) (lo := 0x42000000) (off := 0xBE000000) (t := 0) rfl, hcnd]
        simp +decide [upd, aluEval, ha1]
      · intro r q1 q2 q3 q4; rw [regs9]
        exact keepU _ a1 _ (by decide) (keepU _ a3 _ (by decide) (keepU _ a2 _ (by decide)
          (keepU _ a3 _ (by decide) (keepU _ a2 _ (by decide) kF)))) r q1 q2 q3 q4
    · obtain ⟨m5, e5, t5⟩ := t4.notTaken hc 0x48 ph_at_44 (by decide) (by
        simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, hz, ha1]
        rw [show (BitVec.toNat (25 : Word)) % 32 = 25 from rfl, show (0 : Word) + 33 = 0x21 from rfl, c4, hcnd]
        rfl)
      obtain ⟨m6, e6, t6⟩ := t5.aluImm hc ph_at_48 (off' := 0x4A) (by decide)
      obtain ⟨m7, e7, t7⟩ := t6.sb hc ph_at_4a (off' := 0x4E) (by decide)
      simp +decide only [upd, ite_false, ite_true, aluEval, hz] at t7
      rw [ha0] at t7
      have hc7 := hc.store8 (a := out + 1) (v := (0 + 9 : Word).extractLsb' 0 8) s1o
      obtain ⟨m8, e8, t8⟩ := t7.aluImm hc7 ph_at_4e (off' := 0x50) (by decide)
      obtain ⟨m9, e9, t9⟩ := t8.jump hc7 ph_at_50 (off' := 0x6C) (by decide)
        (by rw [t8.pc, BitVec.add_assoc]; exact ev 0x6C (by omega) (by omega))
      obtain ⟨m10, c10, pc10, mem10, regs10⟩ := tail6c _ m9 _ hc7 t9 (by simp +decide [upd, ha0])
        (by simp +decide [upd, hra])
      refine ⟨m10, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
        (.cons e9 c10)))))))), pc10, ?_, ?_⟩
      · rw [mem10, physMem_k 0 (by decide) (lo := 0x42000000) (off := 0xBE000000) (t := 0) rfl, hcnd]
        simp +decide [upd, aluEval]
      · intro r q1 q2 q3 q4; rw [regs10]
        exact keepU _ a2 _ (by decide) (keepU _ a1 _ (by decide) (keepU _ a3 _ (by decide)
          (keepU _ a2 _ (by decide) kF))) r q1 q2 q3 q4
  obtain ⟨m2, e2, t2⟩ := t1.notTaken hc 0x6 ph_at_4 (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken, hz]
    show (BitVec.zeroExtend 32 k == BitVec.ofNat 32 0) = false
    rw [zk 0 (by decide)]; simpa using hk0)
  obtain ⟨m3, e3, t3⟩ := t2.aluImm hc ph_at_6 (off' := 0x8) (by decide)
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨m4, e4, t4⟩ := t3.taken hc 0x2A ph_at_8 (by decide) (by simp +decide [upd, aluEval])
    obtain ⟨m5, e5, t5⟩ := t4.aluImm hc ph_at_2a (off' := 0x2E) (by decide)
    obtain ⟨m6, e6, t6⟩ := t5.aluImm hc ph_at_2e (off' := 0x30) (by decide)
    have c6 : (addr >>> 26).ult 15 = addr.ult 0x3C000000 := shr_ult_iff addr 26 15 (by omega) (by decide)
    cases hcnd : addr.ult 0x3C000000
    · obtain ⟨m7, e7, t7⟩ := t6.notTaken hc 0x34 ph_at_30 (by decide) (by
        simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, hz, ha1]
        rw [show (BitVec.toNat (26 : Word)) % 32 = 26 from rfl, show (0 : Word) + 15 = 15 from rfl, c6, hcnd])
      obtain ⟨m8, e8, t8⟩ := t7.aluImm hc ph_at_34 (off' := 0x36) (by decide)
      obtain ⟨m9, e9, t9⟩ := t8.lui hc ph_at_36 (off' := 0x3A) (by decide)
      obtain ⟨m10, e10, t10⟩ := t9.jump hc ph_at_3a (off' := 0x68) (by decide)
        (by rw [t9.pc, BitVec.add_assoc]; exact ev 0x68 (by omega) (by omega))
      obtain ⟨m11, c11, pc11, mem11, regs11⟩ := tail68 m10 _ t10 (by simp +decide [upd, ha0])
        (by simp +decide [upd, hra])
      refine ⟨m11, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
        (.cons e9 (.cons e10 c11))))))))), pc11, ?_, ?_⟩
      · rw [mem11, physMem_k 1 (by decide) (lo := 0x3C000000) (off := 0xC4000000) (t := 0) rfl, hcnd]
        simp +decide [upd, aluEval, ha1]
      · intro r q1 q2 q3 q4; rw [regs11]
        exact keepU _ a1 _ (by decide) (keepU _ a3 _ (by decide) (keepU _ a2 _ (by decide)
          (keepU _ a3 _ (by decide) (keepU _ a2 _ (by decide) (keepU _ a3 _ (by decide) kF))))) r q1 q2 q3 q4
    · obtain ⟨m7, e7, t7⟩ := t6.taken hc 0x48 ph_at_30 (by decide) (by
        simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, hz, ha1]
        rw [show (BitVec.toNat (26 : Word)) % 32 = 26 from rfl, show (0 : Word) + 15 = 15 from rfl, c6, hcnd])
      obtain ⟨m8, e8, t8⟩ := t7.aluImm hc ph_at_48 (off' := 0x4A) (by decide)
      obtain ⟨m9, e9, t9⟩ := t8.sb hc ph_at_4a (off' := 0x4E) (by decide)
      simp +decide only [upd, ite_false, ite_true, aluEval, hz] at t9
      rw [ha0] at t9
      have hc9 := hc.store8 (a := out + 1) (v := (0 + 9 : Word).extractLsb' 0 8) s1o
      obtain ⟨m10, e10, t10⟩ := t9.aluImm hc9 ph_at_4e (off' := 0x50) (by decide)
      obtain ⟨m11, e11, t11⟩ := t10.jump hc9 ph_at_50 (off' := 0x6C) (by decide)
        (by rw [t10.pc, BitVec.add_assoc]; exact ev 0x6C (by omega) (by omega))
      obtain ⟨m12, c12, pc12, mem12, regs12⟩ := tail6c _ m11 _ hc9 t11 (by simp +decide [upd, ha0])
        (by simp +decide [upd, hra])
      refine ⟨m12, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
        (.cons e9 (.cons e10 (.cons e11 c12)))))))))), pc12, ?_, ?_⟩
      · rw [mem12, physMem_k 1 (by decide) (lo := 0x3C000000) (off := 0xC4000000) (t := 0) rfl, hcnd]
        simp +decide [upd, aluEval]
      · intro r q1 q2 q3 q4; rw [regs12]
        exact keepU _ a2 _ (by decide) (keepU _ a1 _ (by decide) (keepU _ a3 _ (by decide)
          (keepU _ a2 _ (by decide) (keepU _ a3 _ (by decide) kF)))) r q1 q2 q3 q4
  obtain ⟨m4, e4, t4⟩ := t3.notTaken hc 0xC ph_at_8 (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken, hz, aluEval]
    rw [show (0 : Word) + 1 = BitVec.ofNat 32 1 from rfl, zk 1 (by decide)]; simpa using hk1)
  obtain ⟨m5, e5, t5⟩ := t4.aluImm hc ph_at_c (off' := 0xE) (by decide)
  by_cases hk2 : k = 2
  · subst hk2
    obtain ⟨m6, e6, t6⟩ := t5.notTaken hc 0x12 ph_at_e (by decide) (by simp +decide [upd, aluEval])
    obtain ⟨m7, e7, t7⟩ := t6.aluImm hc ph_at_12 (off' := 0x16) (by decide)
    obtain ⟨m8, e8, t8⟩ := t7.aluImm hc ph_at_16 (off' := 0x1A) (by decide)
    obtain ⟨m9, e9, t9⟩ := t8.aluImm hc ph_at_1a (off' := 0x1C) (by decide)
    obtain ⟨m10, e10, t10⟩ := t9.aluImm hc ph_at_1c (off' := 0x1E) (by decide)
    have c10 : (addr >>> 20).ult 7 = addr.ult 0x700000 := shr_ult_iff addr 20 7 (by omega) (by decide)
    have e20 : (BitVec.toNat (20 : Word)) % 32 = 20 := rfl
    cases hcnd : addr.ult 0x700000
    · obtain ⟨m11, e11, t11⟩ := t10.taken hc 0x64 ph_at_1e (by decide) (by
        simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, hz, ha1]
        rw [e20, show (0 : Word) + 7 = 7 from rfl, c10, hcnd]; rfl)
      obtain ⟨m12, e12, t12⟩ := t11.lui hc ph_at_64 (off' := 0x68) (by decide)
      obtain ⟨m13, c13, pc13, mem13, regs13⟩ := tail68 m12 _ t12 (by simp +decide [upd, ha0])
        (by simp +decide [upd, hra])
      refine ⟨m13, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
        (.cons e9 (.cons e10 (.cons e11 (.cons e12 c13))))))))))), pc13, ?_, ?_⟩
      · rw [mem13, physMem_k 2 (by decide) (lo := 0x700000) (off := 0xFF900000) (t := 1) rfl, hcnd]
        simp +decide only [upd, ite_false, ite_true, aluEval, hz, ha1]
        rw [e20, c10, hcnd]; rfl
      · intro r q1 q2 q3 q4; rw [regs13]
        exact keepU _ a1 _ (by decide) (keepU _ a3 _ (by decide) (keepU _ a2 _ (by decide)
          (keepU _ a4 _ (by decide) (keepU _ a2 _ (by decide) (keepU _ a3 _ (by decide)
          (keepU _ a3 _ (by decide) (keepU _ a3 _ (by decide) kF))))))) r q1 q2 q3 q4
    · obtain ⟨m11, e11, t11⟩ := t10.notTaken hc 0x22 ph_at_1e (by decide) (by
        simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, hz, ha1]
        rw [e20, show (0 : Word) + 7 = 7 from rfl, c10, hcnd]; rfl)
      obtain ⟨m12, e12, t12⟩ := t11.aluImm hc ph_at_22 (off' := 0x24) (by decide)
      obtain ⟨m13, e13, t13⟩ := t12.sb hc ph_at_24 (off' := 0x28) (by decide)
      simp +decide only [upd, ite_false, ite_true, aluEval, hz] at t13
      rw [ha0] at t13
      have hc13 := hc.store8 (a := out + 1) (v := (0 + 9 : Word).extractLsb' 0 8) s1o
      obtain ⟨m14, e14, t14⟩ := t13.jump hc13 ph_at_28 (off' := 0x6C) (by decide)
        (by rw [t13.pc, BitVec.add_assoc]; exact ev 0x6C (by omega) (by omega))
      obtain ⟨m15, c15, pc15, mem15, regs15⟩ := tail6c _ m14 _ hc13 t14 (by simp +decide [upd, ha0])
        (by simp +decide [upd, hra])
      refine ⟨m15, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
        (.cons e9 (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 c15))))))))))))), pc15, ?_, ?_⟩
      · rw [mem15, physMem_k 2 (by decide) (lo := 0x700000) (off := 0xFF900000) (t := 1) rfl, hcnd]
        simp +decide only [upd, ha1, ↓reduceIte]
        rw [e20, c10, hcnd]; rfl
      · intro r q1 q2 q3 q4; rw [regs15]
        exact keepU _ a1 _ (by decide) (keepU _ a2 _ (by decide) (keepU _ a4 _ (by decide)
          (keepU _ a2 _ (by decide) (keepU _ a3 _ (by decide) (keepU _ a3 _ (by decide)
          (keepU _ a3 _ (by decide) kF)))))) r q1 q2 q3 q4
  obtain ⟨m6, e6, t6⟩ := t5.taken hc 0x52 ph_at_e (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken, hz, aluEval]
    show (!(BitVec.zeroExtend 32 k == BitVec.ofNat 32 2)) = true
    rw [zk 2 (by decide)]; simpa using hk2)
  obtain ⟨m7, e7, t7⟩ := t6.aluImm hc ph_at_52 (off' := 0x54) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.sb hc ph_at_54 (off' := 0x58) (by decide)
  simp +decide only [upd, ite_false, ite_true, aluEval, hz] at t8
  rw [ha0, add_lit_zero] at t8
  have hc8 := hc.store8 (a := out) (v := (0 + 1 : Word).extractLsb' 0 8) s0o
  obtain ⟨m9, e9, t9⟩ := t8.sw hc8 ph_at_58 (off' := 0x5A) (by decide)
    (by simp +decide only [upd, ite_false]; rw [ha0]; exact aligned_add hout (k := 4) (by decide))
  simp +decide only [upd, ite_false] at t9
  rw [ha0, ha1] at t9
  obtain ⟨m10, e10, pc10, mem10, regs10⟩ := t9.jalr (hc8.store32 s4o) ph_at_5a
  refine ⟨m10, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
    (.cons e9 (.single e10))))))))), ?_, ?_, ?_⟩
  · rw [pc10]; simp +decide only [upd, ite_false]; rw [hra, add_lit_zero, hret]
  · rw [mem10, physMem_other k hk0 hk1 hk2]; rfl
  · intro r q1 q2 q3 q4; rw [regs10]
    exact keepU _ a2 _ (by decide) (keepU _ a3 _ (by decide) (keepU _ a3 _ (by decide) kF)) r q1 q2 q3 q4

/-! ## `memcpy`, for word-aligned buffers -/

abbrev a7 : Fin 32 := 17
abbrev t1 : Fin 32 := 6

/-- `k` words copied from `src` to `dst`, each read from the memory before
the copy. -/
def copyWords (M : Word → BitVec 8) (dst src : Word) : Nat → Word → BitVec 8
  | 0 => M
  | k + 1 => memStore32 (copyWords M dst src k) (dst + BitVec.ofNat 32 (4 * k))
      (memLoad32 M (src + BitVec.ofNat 32 (4 * k)))

theorem copyWords_outside {M : Word → BitVec 8} {dst src x : Word} :
    ∀ k, Sep dst (4 * k) x 1 → copyWords M dst src k x = M x
  | 0, _ => rfl
  | k + 1, h => by
    simp only [copyWords]
    rw [memStore32_get_sep (h.sub (c := 4 * k) (l := 4) (by omega)),
      copyWords_outside k (h.sub (c := 0) (l := 4 * k) (by omega) |> fun h' => by
        rwa [add_ofNat_zero] at h')]

theorem ms_at_0 : fetchRel memcpyStubCode 0x0 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem ms_at_4 : fetchRel memcpyStubCode 0x4 = some (.jalr x0 (6 : Fin 32) 0x8, 4) := by decide
section

set_option maxRecDepth 20000

theorem mc_at_0 : fetchRel memcpyBodyCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem mc_at_2 : fetchRel memcpyBodyCode 0x2 = some (.aluImm .add a3 x0 0x10, 2) := by decide
theorem mc_at_4 : fetchRel memcpyBodyCode 0x4 = some (.branch .bltu a2 a3 0x72, 4) := by decide
theorem mc_at_8 : fetchRel memcpyBodyCode 0x8 = some (.alu .sub a3 x0 a0, 4) := by decide
theorem mc_at_c : fetchRel memcpyBodyCode 0xC = some (.aluImm .and a3 a3 0x3, 2) := by decide
theorem mc_at_e : fetchRel memcpyBodyCode 0xE = some (.alu .add a4 a0 a3, 4) := by decide
theorem mc_at_12 : fetchRel memcpyBodyCode 0x12 = some (.branch .bgeu a0 a4 0x1A, 4) := by decide
theorem mc_at_2c : fetchRel memcpyBodyCode 0x2C = some (.alu .add a1 a1 a3, 2) := by decide
theorem mc_at_2e : fetchRel memcpyBodyCode 0x2E = some (.alu .sub a2 a2 a3, 2) := by decide
theorem mc_at_30 : fetchRel memcpyBodyCode 0x30 = some (.aluImm .and a5 a2 0xFFFFFFFC, 4) := by decide
theorem mc_at_34 : fetchRel memcpyBodyCode 0x34 = some (.aluImm .and t0 a1 0x3, 4) := by decide
theorem mc_at_38 : fetchRel memcpyBodyCode 0x38 = some (.alu .add a3 a4 a5, 4) := by decide
theorem mc_at_3c : fetchRel memcpyBodyCode 0x3C = some (.branch .beq t0 x0 0x46, 4) := by decide
theorem mc_at_82 : fetchRel memcpyBodyCode 0x82 = some (.branch .bgeu a4 a3 0xE4, 4) := by decide
theorem mc_at_86 : fetchRel memcpyBodyCode 0x86 = some (.alu .add (16 : Fin 32) x0 a1, 2) := by decide
theorem mc_at_88 : fetchRel memcpyBodyCode 0x88 = some (.load .lw (17 : Fin 32) (16 : Fin 32) 0x0, 4) := by decide
theorem mc_at_8c : fetchRel memcpyBodyCode 0x8C = some (.store .sw a4 (17 : Fin 32) 0x0, 4) := by decide
theorem mc_at_90 : fetchRel memcpyBodyCode 0x90 = some (.aluImm .add a4 a4 0x4, 2) := by decide
theorem mc_at_92 : fetchRel memcpyBodyCode 0x92 = some (.aluImm .add (16 : Fin 32) (16 : Fin 32) 0x4, 2) := by decide
theorem mc_at_94 : fetchRel memcpyBodyCode 0x94 = some (.branch .bltu a4 a3 0xFFFFFFF4, 4) := by decide
theorem mc_at_98 : fetchRel memcpyBodyCode 0x98 = some (.jal x0 0xCE, 2) := by decide
theorem mc_at_166 : fetchRel memcpyBodyCode 0x166 = some (.alu .add a1 a1 a5, 2) := by decide
theorem mc_at_168 : fetchRel memcpyBodyCode 0x168 = some (.aluImm .and a2 a2 0x3, 2) := by decide
theorem mc_at_16a : fetchRel memcpyBodyCode 0x16A = some (.alu .add a4 a3 a2, 4) := by decide
theorem mc_at_16e : fetchRel memcpyBodyCode 0x16E = some (.branch .bgeu a3 a4 0x14, 4) := by decide
theorem mc_at_182 : fetchRel memcpyBodyCode 0x182 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem mc_at_184 : fetchRel memcpyBodyCode 0x184 = some (.jalr x0 ra 0x0, 2) := by decide

end

/-- The word loop at 0x88: with `j` words copied and `k` left, it copies the
rest and leaves the loop at 0x98. -/
theorem memcpy_loop {B dst src : Word} {M0 : Word → BitVec 8} {w : Nat}
    (hc : ∀ j, j ≤ w → CodeIn (copyWords M0 dst src j) B memcpyBodyCode)
    (hdst : dst.toNat % 4 = 0) (hsrc : src.toNat % 4 = 0)
    (hwrap : dst.toNat + 4 * w < 2 ^ 32)
    (hsep : Sep dst (4 * w) src (4 * w)) :
    ∀ k j (n : Machine), j + k = w → 0 < k →
      St (copyWords M0 dst src j) B n 0x88 (reg n) → reg n a4 = dst + BitVec.ofNat 32 (4 * j) →
      reg n a6 = src + BitVec.ofNat 32 (4 * j) → reg n a3 = dst + BitVec.ofNat 32 (4 * w) →
      ∃ n', Steps n n' ∧ St (copyWords M0 dst src w) B n' 0x98 (reg n') ∧
        (∀ r, r ≠ a4 → r ≠ a6 → r ≠ a7 → reg n' r = reg n r) := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n hjk _ s h4 h6 h3
    have hjw : j < w := by omega
    have hcj := hc j (by omega)
    obtain ⟨n1, d1, u1⟩ := s.lw hcj mc_at_88 (off' := 0x8C) (by decide)
      (by rw [h6, add_lit_zero]; exact aligned_add hsrc (k := 4 * j) (by omega))
    rw [h6, add_lit_zero] at u1
    have ld : memLoad32 (copyWords M0 dst src j) (src + BitVec.ofNat 32 (4 * j)) =
        memLoad32 M0 (src + BitVec.ofNat 32 (4 * j)) := memLoad32_congr fun i hi => by
      rw [add_ofNat_assoc]
      exact copyWords_outside j ((hsep.subR (c := 4 * j + i) (l := 1) (by omega)).sub (c := 0) (l := 4 * j)
        (by omega) |> fun h' => by rwa [add_ofNat_zero] at h')
    rw [ld] at u1
    obtain ⟨n2, d2, u2⟩ := u1.sw hcj mc_at_8c (off' := 0x90) (by decide)
      (by simp +decide only [upd, ite_false]; rw [h4, add_lit_zero]
          exact aligned_add hdst (k := 4 * j) (by omega))
    simp +decide only [upd, ite_false, ite_true] at u2
    rw [h4, add_lit_zero] at u2
    have hst : memStore32 (copyWords M0 dst src j) (dst + BitVec.ofNat 32 (4 * j))
        (memLoad32 M0 (src + BitVec.ofNat 32 (4 * j))) = copyWords M0 dst src (j + 1) := rfl
    rw [hst] at u2
    have hcj1 := hc (j + 1) (by omega)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hcj1 mc_at_90 (off' := 0x92) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hcj1 mc_at_92 (off' := 0x94) (by decide)
    have e4 : dst + BitVec.ofNat 32 (4 * j) + 4 = dst + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2
    have e6 : src + BitVec.ofNat 32 (4 * j) + 4 = src + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2
    have ult : (dst + BitVec.ofNat 32 (4 * (j + 1))).ult (dst + BitVec.ofNat 32 (4 * w)) = decide (j + 1 < w) := by
      simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
      apply decide_eq_decide.mpr
      rw [Nat.mod_eq_of_lt (a := 4 * (j + 1)) (by omega), Nat.mod_eq_of_lt (a := 4 * w) (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      constructor <;> intro h <;> omega
    have r4 : ∀ r, reg n4 r = upd (upd (upd (reg n) a7 (memLoad32 M0 (src + BitVec.ofNat 32 (4 * j)))) a4
        (dst + BitVec.ofNat 32 (4 * (j + 1)))) a6 (src + BitVec.ofNat 32 (4 * (j + 1))) r := fun r => by
      rw [u4.regs]; simp +decide only [upd, ite_false, aluEval, h4, h6, e4, e6]
    have u4' : St (copyWords M0 dst src (j + 1)) B n4 0x94 (reg n4) := u4.self
    by_cases hlt : j + 1 < w
    · obtain ⟨n5, d5, u5⟩ := u4'.taken hcj1 0x88 mc_at_94 (by decide) (by
        rw [r4, r4]; simp +decide only [upd, ite_false, ite_true, branchTaken]
        rw [h3, ult]; simpa using hlt)
      obtain ⟨n6, c6, u6, f6⟩ := ih (j + 1) n5 (by omega) (by omega) u5.self
        (by rw [u5.regs, r4]; simp +decide [upd]) (by rw [u5.regs, r4]; simp +decide [upd])
        (by rw [u5.regs, r4]; simp +decide [upd, h3])
      refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c6)))), u6, fun r q4 q6 q7 => ?_⟩
      rw [f6 r q4 q6 q7, u5.regs, r4]; simp [upd, q4, q6, q7]
      by_cases h0 : r = 0
      · subst h0; rfl
      · simp [h0]
    · have hj : j + 1 = w := by omega
      obtain ⟨n5, d5, u5⟩ := u4'.notTaken hcj1 0x98 mc_at_94 (by decide) (by
        rw [r4, r4]; simp +decide only [upd, ite_false, ite_true, branchTaken]
        rw [h3, ult]; simpa using hlt)
      rw [hj] at u5
      refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), u5.self, fun r q4 q6 q7 => ?_⟩
      rw [u5.regs, r4]; simp [upd, q4, q6, q7]
      by_cases h0 : r = 0
      · subst h0; rfl
      · simp [h0]

theorem and3 (n : Nat) : n &&& 3 = n % 4 := by
  have h1 : n &&& 3 ≤ 3 := Nat.and_le_right
  rw [← Nat.mod_eq_of_lt (show n &&& 3 < 4 by omega), show (4 : Nat) = 2 ^ 2 from rfl, Nat.and_mod_two_pow]
  have : n % 2 ^ 2 < 4 := Nat.mod_lt _ (by decide)
  generalize n % 2 ^ 2 = r at this ⊢
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

theorem and3_word {x : Word} (h : x.toNat % 4 = 0) : x &&& 3 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (3 : Word).toNat = 3 from rfl, and3, h]; rfl

/-- **The compiled `memcpy` is correct for word-aligned buffers.** Called at
its stub with `dst` and `src` 4-byte aligned, apart, and a length of `4 * w`
bytes for `w` at least 4, it copies the `w` words (`copyWords`), returns
`dst` in `a0`, restores `sp`, and changes only `a1` through `a7`, `t0`, and
`t1` among the other registers. `ha5` holds for every multiple of 4; each
caller checks it for its length with `decide`. -/
theorem memcpy_aligned (m : Machine) (stub retAddr dst src : Word) (w : Nat)
    (hcode : CodeAt m stub memcpyStubCode) (hbody : CodeAt m (stub + 8) memcpyBodyCode)
    (hstub : stub.toNat % 2 = 0) (hpc : m.pc = stub)
    (ha0 : reg m a0 = dst) (ha1 : reg m a1 = src) (ha2 : reg m a2 = BitVec.ofNat 32 (4 * w))
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hw : 4 ≤ w) (hwrap : dst.toNat + 4 * w < 2 ^ 32)
    (ha5 : BitVec.ofNat 32 (4 * w) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * w))
    (hdst : dst.toNat % 4 = 0) (hsrc : src.toNat % 4 = 0)
    (hsep : Sep dst (4 * w) src (4 * w))
    (hDB : Sep dst (4 * w) (stub + 8) memcpyBodyCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = copyWords m.mem dst src w ∧ reg m' a0 = dst ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        reg m' r = reg m r := by
  have hcs : CodeIn m.mem stub memcpyStubCode := hcode
  have s0'' : St m.mem stub m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0''.zero
  obtain ⟨m1, e1, t1'⟩ := s0''.auipc hcs ms_at_0 (off' := 4) (by decide)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1'.call hcs ms_at_4
  have hB : (stub + 8).toNat % 2 = 0 := even_at stub hstub 8 (by decide)
  have hcB : ∀ j, j ≤ w → CodeIn (copyWords m.mem dst src j) (stub + 8) memcpyBodyCode :=
    fun j hj i hi => by
      rw [copyWords_outside j ((hDB.subR (c := i) (l := 1) (by omega)).sub (c := 0) (l := 4 * j) (by omega)
        |> fun h' => by rwa [add_ofNat_zero] at h')]
      exact hbody i hi
  have hc0 := hcB 0 (by omega)
  have r2 : ∀ r, r ≠ t1 → reg m2 r = reg m r := fun r h6 => by
    rw [regs2]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · have h6' : r ≠ (6 : Fin 32) := h6
      have h0' : r ≠ x0 := fun e => h0 (by subst e; rfl)
      simp [upd, h0, h6', h0']
  have hpc2 : m2.pc = stub + 8 := by
    rw [pc2]; simp +decide only [upd, ite_false, ite_true]
    rw [add_lit_zero, show stub + BitVec.ofNat 32 0 = stub from add_ofNat_zero stub, even_clear _ hB]
  have u0 : St (copyWords m.mem dst src 0) (stub + 8) m2 0 (reg m2) :=
    ⟨by rw [hpc2]; simp, mem2, fun _ => rfl⟩
  have sub0 : ∀ x : Word, x - 0 = x := fun x => BitVec.eq_of_toNat_eq (by simp)
  have add0 : ∀ x : Word, 0 + x = x := fun x => BitVec.eq_of_toNat_eq (by simp)
  have z0 : (0 - dst) &&& 3 = 0 := and3_word (by
    rw [BitVec.toNat_sub, show (0 : Word).toNat = 0 from rfl]; omega)
  have zs : src &&& 3 = 0 := and3_word hsrc
  obtain ⟨n1, d1, v1⟩ := u0.aluImm hc0 mc_at_0 (off' := 0x2) (by decide)
  obtain ⟨n2, d2, v2⟩ := v1.aluImm hc0 mc_at_2 (off' := 0x4) (by decide)
  have h16 : (BitVec.ofNat 32 (4 * w)).ult (0 + 0x10) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4 * w < 2 ^ 32 by omega)]
    apply decide_eq_false; show ¬ 4 * w < 16; omega
  obtain ⟨n3, d3, v3⟩ := v2.notTaken hc0 0x8 mc_at_4 (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval, r2 a2 (by decide), ha2, r2 x0 (by decide), hz]
    exact h16)
  obtain ⟨n4, d4, v4⟩ := v3.alu hc0 mc_at_8 (off' := 0xC) (by decide)
  obtain ⟨n5, d5, v5⟩ := v4.aluImm hc0 mc_at_c (off' := 0xE) (by decide)
  obtain ⟨n6, d6, v6⟩ := v5.alu hc0 mc_at_e (off' := 0x12) (by decide)
  have g6 : ∀ r, r = a0 ∨ r = a1 ∨ r = a2 → reg m2 r = reg m r := fun r hr => r2 r (by
    rcases hr with rfl | rfl | rfl <;> decide)
  have va3 : aluEval .and (aluEval .sub 0 (reg m2 a0)) 3 = 0 := by
    simp only [aluEval]; rw [g6 a0 (by simp), ha0]; exact z0
  obtain ⟨n7, d7, v7⟩ := v6.taken hc0 0x2C mc_at_12 (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken]
    rw [va3]; simp only [aluEval, add_lit_zero]; simp [BitVec.ult])
  obtain ⟨n8, d8, v8⟩ := v7.alu hc0 mc_at_2c (off' := 0x2E) (by decide)
  obtain ⟨n9, d9, v9⟩ := v8.alu hc0 mc_at_2e (off' := 0x30) (by decide)
  obtain ⟨n10, d10, v10⟩ := v9.aluImm hc0 mc_at_30 (off' := 0x34) (by decide)
  obtain ⟨n11, d11, v11⟩ := v10.aluImm hc0 mc_at_34 (off' := 0x38) (by decide)
  obtain ⟨n12, d12, v12⟩ := v11.alu hc0 mc_at_38 (off' := 0x3C) (by decide)
  -- The registers at 0x3C.
  have q12 : reg n12 sp = reg m sp + 0xFFFFFFF0 ∧ reg n12 a4 = dst ∧ reg n12 a1 = src ∧
      reg n12 a2 = BitVec.ofNat 32 (4 * w) ∧ reg n12 a5 = BitVec.ofNat 32 (4 * w) ∧ reg n12 t0 = 0 ∧
      reg n12 a3 = dst + BitVec.ofNat 32 (4 * w) ∧ reg n12 a0 = dst ∧
      ∀ r, r ≠ sp → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ t1 → reg n12 r = reg m r := by
    have e : ∀ r, reg n12 r = _ := v12.regs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r qs q1 q2 q3 q4 q5 q6 q7 => ?_⟩
    · rw [e]; simp +decide only [upd, ite_false, ite_true, aluEval]; rw [r2 sp (by decide)]
    · rw [e]; simp +decide only [upd, ite_false, ite_true]; rw [va3]; simp only [aluEval, add_lit_zero]
      rw [g6 a0 (by simp), ha0]
    · rw [e]; simp +decide only [upd, ite_false, ite_true]; rw [va3]; simp only [aluEval, add_lit_zero]
      rw [g6 a1 (by simp), ha1]
    · rw [e]; simp +decide only [upd, ite_false, ite_true]; rw [va3]; simp only [aluEval, sub0]
      rw [g6 a2 (by simp), ha2]
    · rw [e]; simp +decide only [upd, ite_false, ite_true]; rw [va3]
      simp only [aluEval, sub0]; rw [g6 a2 (by simp), ha2]; exact ha5
    · rw [e]; simp +decide only [upd, ite_false, ite_true]; rw [va3]
      simp only [aluEval, add_lit_zero]; rw [g6 a1 (by simp), ha1]; exact zs
    · rw [e]; simp +decide only [upd, ite_false, ite_true]; rw [va3]
      simp only [aluEval, add_lit_zero, sub0]; rw [g6 a0 (by simp), g6 a2 (by simp), ha0, ha2, ha5]
    · rw [e]; simp +decide only [upd, ite_false, ite_true]; rw [g6 a0 (by simp), ha0]
    · rw [e]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd, hz]
      · simp [upd, h0, qs, q1, q2, q3, q4, q5, q6]; exact r2 r q7
  obtain ⟨q12sp, q12a4, q12a1, q12a2, q12a5, q12t0, q12a3, q12a0, k12⟩ := q12
  have v12' : St (copyWords m.mem dst src 0) (stub + 8) n12 0x3C (reg n12) := v12.self
  obtain ⟨n13, d13, v13⟩ := v12'.taken hc0 0x82 mc_at_3c (by decide) (by
    simp only [branchTaken]; rw [q12t0, v12'.zero]; rfl)
  have hlt : dst.ult (dst + BitVec.ofNat 32 (4 * w)) = true := by
    simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 4 * w) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true (by omega)
  obtain ⟨n14, d14, v14⟩ := v13.notTaken hc0 0x86 mc_at_82 (by decide) (by
    simp only [branchTaken]; rw [q12a4, q12a3, hlt]; rfl)
  obtain ⟨n15, d15, v15⟩ := v14.alu hc0 mc_at_86 (off' := 0x88) (by decide)
  obtain ⟨n16, c16, v16, f16⟩ := memcpy_loop hcB hdst hsrc hwrap hsep w 0 n15 (by omega) (by omega)
    v15.self
    (by rw [v15.regs]; simp +decide only [upd, ite_false]; rw [q12a4]; exact (add_ofNat_zero dst).symm)
    (by rw [v15.regs]; simp +decide only [upd, ite_false, ite_true, aluEval]
        rw [v12'.zero, q12a1, add0]; exact (add_ofNat_zero src).symm)
    (by rw [v15.regs]; simp +decide only [upd, ite_false]; rw [q12a3])
  have r16 : ∀ r, r ≠ a4 → r ≠ a6 → r ≠ a7 → reg n16 r = reg n12 r := fun r h1 h2 h3 => by
    rw [f16 r h1 h2 h3, v15.regs]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact v12'.zero.symm
    · simp [upd, h0, h2]
  have hcw := hcB w (Nat.le_refl w)
  obtain ⟨n17, d17, v17⟩ := v16.jump hcw mc_at_98 (off' := 0x166) (by decide)
    (by rw [v16.pc, BitVec.add_assoc]; exact even_bit0 (even_at _ hB 0x166 (by decide)))
  obtain ⟨n18, d18, v18⟩ := v17.alu hcw mc_at_166 (off' := 0x168) (by decide)
  obtain ⟨n19, d19, v19⟩ := v18.aluImm hcw mc_at_168 (off' := 0x16A) (by decide)
  obtain ⟨n20, d20, v20⟩ := v19.alu hcw mc_at_16a (off' := 0x16E) (by decide)
  have w3 : BitVec.ofNat 32 (4 * w) &&& 3 = 0 := and3_word (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * w) (by omega)]; omega)
  obtain ⟨n21, d21, v21⟩ := v20.taken hcw 0x182 mc_at_16e (by decide) (by
    simp +decide only [upd, ite_false, ite_true, branchTaken, aluEval]
    rw [r16 a2 (by decide) (by decide) (by decide), q12a2, w3, add_lit_zero]; simp [BitVec.ult])
  obtain ⟨n22, d22, v22⟩ := v21.aluImm hcw mc_at_182 (off' := 0x184) (by decide)
  obtain ⟨n23, d23, pc23, mem23, regs23⟩ := v22.jalr hcw mc_at_184
  have spr : reg m sp + 0xFFFFFFF0 + 0x10 = reg m sp := by
    rw [BitVec.add_assoc]; exact BitVec.add_zero _
  refine ⟨n23, .cons e1 (.cons e2 (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
    (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (c16.trans
    (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.single d23)))))))))))))))))))))))),
    ?_, mem23, ?_, ?_⟩
  · rw [pc23]; simp +decide only [upd, ite_false]
    rw [r16 ra (by decide) (by decide) (by decide), k12 ra (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hra, add_lit_zero, hret]
  · rw [regs23]; simp +decide only [upd, ite_false]
    rw [r16 a0 (by decide) (by decide) (by decide), q12a0]
  · intro r q1 q2 q3 q4 q5 q6 q7 q8 q9
    rw [regs23]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · by_cases hs : r = sp
      · subst hs; simp +decide [upd, aluEval]
        rw [r16 sp (by decide) (by decide) (by decide), q12sp]; exact spr
      · simp [upd, h0, hs, q1, q2, q4]
        rw [r16 r q4 q6 q7, k12 r hs q1 q2 q3 q4 q5 q8 q9]
end C3.RV32
