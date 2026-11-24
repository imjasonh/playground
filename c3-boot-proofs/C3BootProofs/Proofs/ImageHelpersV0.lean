import C3BootProofs.Proofs.ImageHelpers
import C3BootProofs.Image.BootloaderV0

/-!
# `Reader::u8` in the earlier image

The calls in `Reader::u8` reach their callees at different distances in the
earlier image (`Image/BootloaderV0.lean`) than in the current one, so the
bytes differ. These are the theorems for the earlier image, which the
proofs about that image use. They describe the same results and memory as
the theorems in `ImageHelpers.lean`.
-/

namespace C3.RV32.V0

open C3.RV32 C3.ImageV0

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
    (hbcode : CodeAt m (base + 0xD6) Image.readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = self) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSr : Sep (reg m sp + 0xFFFFFFF0) 16 base readerU8Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFF0) 16 (base + 0xD6) Image.readerBytesCode.length)
    (hEr : Sep (self + 8) 4 base readerU8Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xD6) Image.readerBytesCode.length)
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

end C3.RV32.V0
