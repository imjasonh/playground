import C3BootProofs.Proofs.Magic

/-!
# `Reader::u16` and `Reader::version_1`, as compiled

`Reader::u16` reads 2 bytes with `Reader::bytes` and returns
`Result<u16, Error>` packed in `a0`: bit 0 set for `Err` with the error in
bits 8 to 15, or the value in bits 16 to 31 for `Ok`. `Reader::version_1`
calls it and fails with `Error::BadVersion` (3) unless the value is 1,
returning 0xFF in the low byte of `a0` for `Ok`. `readerU16_correct` and
`readerVersion1_correct` prove them on the RV32 model, `version_1` through
`readerU16_correct`.
-/

namespace C3.RV32

open C3.ImageV0

/-- A slice that `Reader::bytes` returns for at least one byte, from a
buffer that is not null and doesn't wrap, is not null. -/
theorem bytesResult_ne_zero {ptr len pos n p e : Word} (hptr : ptr ≠ 0)
    (hwrap : ptr.toNat + len.toNat ≤ 2 ^ 32) (hn : n ≠ 0)
    (h : bytesResult ptr len pos n = some (p, e)) : p ≠ 0 := by
  rw [bytesResult_eq] at h
  split at h
  · rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hp, -⟩ := h
    rw [← hp]
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_add] at h1
    have hne : ptr.toNat ≠ 0 := fun h => hptr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hn' : n.toNat ≠ 0 := fun h => hn (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have h3 : (0 : Word).toNat = 0 := rfl
    omega
  · cases h

/-- What `Reader::u16` returns in `a0`. -/
def u16Result (M : Word → BitVec 8) (self : Word) : Word :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 2 with
  | none => 1
  | some (p, _) => (M (p + 1)).zeroExtend 32 <<< 24 ||| (M p).zeroExtend 32 <<< 16

/-- Memory after `Reader::u16` or `Reader::version_1` returns, outside the
stack it uses. -/
def u16Mem (M : Word → BitVec 8) (self : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 2 with
  | none => M
  | some (_, e) => memStore32 M (self + 8) e

theorem u16_at_00 : fetchRel readerU16Code 0x00 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem u16_at_02 : fetchRel readerU16Code 0x02 = some (.store .sw sp ra 0x0C, 2) := by decide
theorem u16_at_04 : fetchRel readerU16Code 0x04 = some (.store .sw sp s0 8, 2) := by decide
theorem u16_at_06 : fetchRel readerU16Code 0x06 = some (.alu .add a1 x0 a0, 2) := by decide
theorem u16_at_08 : fetchRel readerU16Code 0x08 = some (.alu .add a0 x0 sp, 2) := by decide
theorem u16_at_0a : fetchRel readerU16Code 0x0A = some (.aluImm .add a2 x0 2, 2) := by decide
theorem u16_at_0c : fetchRel readerU16Code 0x0C = some (.aluImm .add s0 x0 2, 2) := by decide
theorem u16_at_0e : fetchRel readerU16Code 0x0E = some (.auipc ra 0, 4) := by decide
theorem u16_at_12 : fetchRel readerU16Code 0x12 = some (.jalr ra ra 0xFFFFFFCC, 4) := by decide
theorem u16_at_16 : fetchRel readerU16Code 0x16 = some (.load .lw a0 sp 0, 2) := by decide
theorem u16_at_18 : fetchRel readerU16Code 0x18 = some (.branch .beq a0 x0 0x18, 2) := by decide
theorem u16_at_1a : fetchRel readerU16Code 0x1A = some (.load .lw a1 sp 4, 2) := by decide
theorem u16_at_1c : fetchRel readerU16Code 0x1C = some (.branch .bne a1 s0 0x1E, 4) := by decide
theorem u16_at_20 : fetchRel readerU16Code 0x20 = some (.load .lbu a1 a0 0, 4) := by decide
theorem u16_at_24 : fetchRel readerU16Code 0x24 = some (.load .lbu a0 a0 1, 4) := by decide
theorem u16_at_28 : fetchRel readerU16Code 0x28 = some (.aluImm .sll a1 a1 0x10, 2) := by decide
theorem u16_at_2a : fetchRel readerU16Code 0x2A = some (.aluImm .sll a0 a0 0x18, 2) := by decide
theorem u16_at_2c : fetchRel readerU16Code 0x2C = some (.alu .or a0 a0 a1, 2) := by decide
theorem u16_at_2e : fetchRel readerU16Code 0x2E = some (.jal x0 0x0E, 2) := by decide
theorem u16_at_30 : fetchRel readerU16Code 0x30 = some (.load .lbu a0 sp 4, 4) := by decide
theorem u16_at_34 : fetchRel readerU16Code 0x34 = some (.aluImm .sll a0 a0 8, 2) := by decide
theorem u16_at_36 : fetchRel readerU16Code 0x36 = some (.aluImm .add a0 a0 1, 2) := by decide
theorem u16_at_38 : fetchRel readerU16Code 0x38 = some (.jal x0 4, 2) := by decide
theorem u16_at_3c : fetchRel readerU16Code 0x3C = some (.load .lw ra sp 0x0C, 2) := by decide
theorem u16_at_3e : fetchRel readerU16Code 0x3E = some (.load .lw s0 sp 8, 2) := by decide
theorem u16_at_40 : fetchRel readerU16Code 0x40 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem u16_at_42 : fetchRel readerU16Code 0x42 = some (.jalr x0 ra 0, 2) := by decide

theorem sll_zext (v : BitVec 8) (k : Nat) (hk : k < 32) :
    aluEval .sll (v.zeroExtend 32) (BitVec.ofNat 32 k) = v.zeroExtend 32 <<< k := by
  show v.zeroExtend 32 <<< ((BitVec.ofNat 32 k).toNat % 32) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32), Nat.mod_eq_of_lt hk]

theorem u16_epilogue {m : Machine} {M : Word → BitVec 8} {f : Fin 32 → Word} {base G r0 r8 : Word}
    (hc : CodeIn M base readerU16Code) (t : St M base m 0x3C f) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) (h1 : memLoad32 M (G + 0x0C) = r0) (h2 : memLoad32 M (G + 8) = r8)
    (hret : r0 &&& ~~~1 = r0) :
    ∃ m', Steps m m' ∧ m'.pc = r0 ∧ m'.mem = M ∧ reg m' sp = G + 0x10 ∧ reg m' ra = r0 ∧
      reg m' s0 = r8 ∧ ∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m1, e1, t1⟩ := t.lw hc u16_at_3c (off' := 0x3E) (by decide)
    (by rw [hsp]; exact aligned_add hG (k := 0x0C) (by decide))
  rw [hsp, h1] at t1
  have u1 : upd f ra r0 sp = G := by simp +decide [upd, hsp]
  obtain ⟨m2, e2, t2⟩ := t1.lw hc u16_at_3e (off' := 0x40) (by decide)
    (by rw [u1]; exact aligned_add hG (k := 8) (by decide))
  rw [u1, h2] at t2
  obtain ⟨m3, e3, t3⟩ := t2.aluImm hc u16_at_40 (off' := 0x42) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := t3.jalr hc u16_at_42
  refine ⟨m4, .cons e1 (.cons e2 (.cons e3 (.single e4))), ?_, mem4, ?_, ?_, ?_, ?_⟩
  · rw [pc4]; simp +decide only [upd]; simpa using hret
  · rw [regs4]; simp +decide [upd, aluEval, hsp]
  · rw [regs4]; simp +decide [upd]
  · rw [regs4]; simp +decide [upd]
  · intro r h1' h2' h3'
    rw [regs4]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [hz]
    · simp [upd, hr, h1', h2', h3']

/-- **The compiled `Reader::u16` is correct.** With its bytes at `base` and
`Reader::bytes`'s where the image puts them, a reader `self` over a slice
that is not null and doesn't wrap, everything aligned, and the 16 bytes of
stack below `sp`, the reader, its position, and its buffer kept apart as
the hypotheses list, there is an execution that reaches the return address
with `sp` restored, `a0` as `u16Result` says, every register but `a0`
through `a5` unchanged, and memory outside those 16 bytes as `u16Mem`
says. -/
theorem readerU16_correct (m : Machine) (base retAddr self : Word)
    (hcode : CodeAt m base readerU16Code)
    (hbcode : CodeAt m (base + 0xFFFFFFDA) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = self) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSu : Sep (reg m sp + 0xFFFFFFF0) 16 base readerU16Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFF0) 16 (base + 0xFFFFFFDA) readerBytesCode.length)
    (hEu : Sep (self + 8) 4 base readerU16Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xFFFFFFDA) readerBytesCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFF0) 16)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFF0) 16)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧ reg m' a0 = u16Result m.mem self ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFF0) 16 x 1 → m'.mem x = u16Mem m.mem self x := by
  have hc : CodeIn m.mem base readerU16Code := hcode
  have s0' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  have hspG : reg m sp = reg m sp + 0xFFFFFFF0 + 0x10 := by
    rw [BitVec.add_assoc]; exact (BitVec.add_zero _).symm
  obtain ⟨G, hGdef⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hGdef] at hSu hSb hRS hBS hspG ⊢
  have hGa : G.toNat % 4 = 0 := hGdef ▸ aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  obtain ⟨ptr, hptr⟩ : ∃ ptr, memLoad32 m.mem self = ptr := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, memLoad32 m.mem (self + 4) = len := ⟨_, rfl⟩
  rw [hptr, hlen] at hbuf hBS hBE
  have sepG : ∀ c l, c + l ≤ 16 → ∀ (b : Word) (n : Nat), Sep G 16 b n →
      Sep (G + BitVec.ofNat 32 c) l b n := fun c l h b n hs => hs.sub (c := c) (l := l) h
  -- 0x00 to 0x04: the frame.
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc u16_at_00 (off' := 0x02) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hGdef] at t1
  have r1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  obtain ⟨m2, e2, t2⟩ := t1.sw hc u16_at_02 (off' := 0x04) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 0x0C) (by decide))
  rw [r1sp, show upd (reg m) sp G ra = reg m ra by simp +decide [upd]] at t2
  have hc2 := hc.store32 (v := reg m ra) (show Sep (G + 0x0C) 4 base _ from sepG 0x0C 4 (by omega) _ _ hSu)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 u16_at_04 (off' := 0x06) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [r1sp, show upd (reg m) sp G s0 = reg m s0 by simp +decide [upd]] at t3
  have hc3 := hc2.store32 (v := reg m s0) (show Sep (G + 8) 4 base _ from sepG 8 4 (by omega) _ _ hSu)
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0) = M2 :=
    ⟨_, rfl⟩
  rw [hM2] at t3 hc3
  have M2out : ∀ x, Sep G 16 x 1 → M2 x = m.mem x := fun x h => by
    rw [← hM2, memStore32_get_sep (show Sep (G + 8) 4 x 1 from sepG 8 4 (by omega) _ _ h),
      memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from sepG 0x0C 4 (by omega) _ _ h)]
  have M2slots : memLoad32 M2 (G + 0x0C) = reg m ra ∧ memLoad32 M2 (G + 8) = reg m s0 := by
    rw [← hM2]
    refine ⟨?_, memLoad32_store32_same _ _ _⟩
    rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x0C) 4 from
        sep_offsets G (c := 8) (n := 4) (d := 0x0C) (k := 4) (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  -- 0x06 to 0x12: the call to `Reader::bytes`.
  obtain ⟨m4, e4, t4⟩ := t3.alu hc3 u16_at_06 (off' := 0x08) (by decide)
  obtain ⟨m5, e5, t5⟩ := t4.alu hc3 u16_at_08 (off' := 0x0A) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.aluImm hc3 u16_at_0a (off' := 0x0C) (by decide)
  obtain ⟨m7, e7, t7⟩ := t6.aluImm hc3 u16_at_0c (off' := 0x0E) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.auipc hc3 u16_at_0e (off' := 0x12) (by decide)
  obtain ⟨m9, e9, pc9, mem9, regs9⟩ := t8.call hc3 u16_at_12
  have r9 : ∀ r, reg m9 r = if r = ra then base + BitVec.ofNat 32 0x16 else
      if r = a0 then G else if r = a1 then self else if r = a2 then 2 else if r = s0 then 2 else
      if r = sp then G else reg m r := by
    intro r; rw [regs9, show base + BitVec.ofNat 32 0x12 + 4 = base + BitVec.ofNat 32 0x16 from
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
  have hevb : (base + 0xFFFFFFDA).toNat % 2 = 0 := even_at base hbase 0xFFFFFFDA (by decide)
  have hpc9 : m9.pc = base + 0xFFFFFFDA := by
    rw [pc9]; simp +decide only [upd, ite_true, ite_false]
    rw [show base + BitVec.ofNat 32 0x0E + 0 + 0xFFFFFFCC = base + 0xFFFFFFDA by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl, even_clear _ hevb]
  have hm9 : m9.mem = M2 := mem9
  have hSself : Sep G 16 self 12 := hRS.symm
  have ld2 : ∀ c, c + 4 ≤ 12 → memLoad32 M2 (self + BitVec.ofNat 32 c) =
      memLoad32 m.mem (self + BitVec.ofNat 32 c) := fun c hc' => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact M2out _ (hSself.subR (c := c + j) (l := 1) (by omega))
  have l2p : memLoad32 M2 self = ptr := by
    have := ld2 0 (by omega); rw [add_ofNat_zero] at this; rw [this, hptr]
  have l2l : memLoad32 M2 (self + 4) = len := by
    rw [show self + 4 = self + BitVec.ofNat 32 4 from rfl, ld2 4 (by omega)]; exact hlen
  have l2e : memLoad32 M2 (self + 8) = memLoad32 m.mem (self + 8) := ld2 8 (by omega)
  have cB : CodeAt m9 (base + 0xFFFFFFDA) readerBytesCode := fun i hi => by
    rw [hm9, M2out _ (hSb.subR (c := i) (l := 1) (by omega))]; exact hbcode i hi
  obtain ⟨m10, c10, pc10, mem10, fr10⟩ := readerBytes_correct m9 (base + 0xFFFFFFDA)
    (base + BitVec.ofNat 32 0x16) G self 2 cB hpc9 (by rw [r9]; simp +decide)
    (by rw [r9]; simp +decide) (by rw [r9]; simp +decide) (by rw [r9]; simp +decide)
    (even_clear _ (even_at base hbase 0x16 (by decide))) hGa hself
    (by have := sepG 0 8 (by omega) _ _ hSb; rwa [add_ofNat_zero] at this) hEb
  rw [hm9] at mem10
  have hR : bytesResult (memLoad32 M2 self) (memLoad32 M2 (self + 4)) (memLoad32 M2 (self + 8)) 2 =
      bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 := by rw [l2p, l2l, l2e]
  have r10 : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m10 r = reg m9 r := fr10
  have r10sp : reg m10 sp = G := by rw [r10 sp (by decide) (by decide) (by decide), r9]; simp +decide
  have r10s0 : reg m10 s0 = 2 := by rw [r10 s0 (by decide) (by decide) (by decide), r9]; simp +decide
  have codeS : ∀ i, i < readerU16Code.length → Sep G 16 (base + BitVec.ofNat 32 i) 1 :=
    fun i hi => hSu.subR (c := i) (l := 1) (by omega)
  have outG : ∀ c, 8 ≤ c → c < 16 → Sep G 8 (G + BitVec.ofNat 32 c) 1 := fun c h1 h2 => by
    have := sep_offsets G (c := 0) (n := 8) (d := c) (k := 1) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have selfG : ∀ c, c < 16 → Sep (self + 8) 4 (G + BitVec.ofNat 32 c) 1 := fun c hc' =>
    (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := c) (l := 1) (by omega)
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  have m10slots : ∀ c, 8 ≤ c → c + 4 ≤ 16 → memLoad32 m10.mem (G + BitVec.ofNat 32 c) =
      memLoad32 M2 (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [mem10]; exact bytesMem_load (fun i hi j hj => by
      rw [add_ofNat_assoc]; exact outG (c + j) (by omega) (by omega) i hi 0 (by omega) ∘ by
        intro e; rwa [add_ofNat_zero])
      (fun i hi j hj => by
        rw [add_ofNat_assoc]; exact selfG (c + j) (by omega) i hi 0 (by omega) ∘ by
          intro e; rwa [add_ofNat_zero])
  have finishRegs : ∀ (n : Machine) (g : Fin 32 → Word),
      (∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → reg n r = g r) → reg n sp = G + 0x10 → reg n ra = reg m ra →
      reg n s0 = reg m s0 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s0 → r ≠ sp →
        g r = reg m r) →
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n r = reg m r :=
    fun n g hn hsp' hra' hs0' hg r h0 h1 h2 h3 h4 h5 => by
      by_cases e1 : r = sp
      · subst e1; rw [hsp', ← hspG]
      by_cases e2 : r = ra
      · subst e2; exact hra'
      by_cases e3 : r = s0
      · subst e3; exact hs0'
      rw [hn r e1 e2 e3]; exact hg r h0 h1 h2 h3 h4 h5 e2 e3 e1
  have r10keep : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s0 →
      r ≠ sp → reg m10 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 => by
    rw [r10 r h3 h4 h5, r9]; simp [h0, h1, h2, h6, h7, h8]
  have m10x : ∀ x, Sep G 16 x 1 → m10.mem x = u16Mem m.mem self x := fun x h => by
    rw [mem10, bytesMem_outside (h.sub (c := 0) (l := 8) (by omega) |> fun h' => by
      rwa [add_ofNat_zero] at h'), hR]
    unfold u16Mem; rw [hptr, hlen]
    rcases bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 with _ | ⟨q, e'⟩
    · exact M2out x h
    · exact memStore32_congr (M2out x h)
  have hc10 : CodeIn m10.mem base readerU16Code := fun i hi => by
    rw [m10x _ (codeS i hi)]; unfold u16Mem; rw [hptr, hlen]
    rcases bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 with _ | ⟨q, e'⟩
    · exact hc i hi
    · dsimp only; rw [memStore32_get_sep (hEu.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have t10 : St m10.mem base m10 0x16 (reg m10) := ⟨by rw [pc10], rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := t10.lw hc10 u16_at_16 (off' := 0x18) (by decide)
    (by rw [r10sp]; exact aligned_add hGa (k := 0) (by decide))
  rw [r10sp, add_lit_zero] at u1
  rcases hR1 : bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 with _ | ⟨p, e⟩
  · obtain ⟨b0, b4⟩ := bytesMem_none (out := G) (hR.trans hR1)
    rw [← mem10] at b0 b4
    rw [b0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.taken hc10 0x30 u16_at_18 (by decide) (by simp +decide [upd])
    obtain ⟨n3, d3, u3⟩ := u2.lbu hc10 u16_at_30 (off' := 0x34) (by decide)
    rw [show upd (reg m10) a0 0 sp = G by simp +decide [upd, r10sp], b4] at u3
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hc10 u16_at_34 (off' := 0x36) (by decide)
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hc10 u16_at_36 (off' := 0x38) (by decide)
    obtain ⟨n6, d6, u6⟩ := u5.jump hc10 u16_at_38 (off' := 0x3C) (by decide)
      (by rw [u5.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x3C (by decide)))
    obtain ⟨n7, c7, pc7, mem7, sp7, ra7, s07, fr7⟩ := u16_epilogue (r0 := reg m ra) (r8 := reg m s0)
      hc10 u6 (by simp +decide [upd, r10sp]) hGa
      (by rw [show G + 0x0C = G + BitVec.ofNat 32 0x0C from rfl, m10slots 0x0C (by omega) (by omega)]
          exact M2slots.1)
      (by rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, m10slots 8 (by omega) (by omega)]
          exact M2slots.2) hret'
    refine ⟨n7, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
      (.cons e9 (c10.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c7))))))))))))))),
      by rw [pc7, hra], by rw [sp7, ← hspG], ?_, ?_, ?_⟩
    · rw [fr7 a0 (by decide) (by decide) (by decide)]
      unfold u16Result; rw [hptr, hlen, hR1]
      simp +decide only [upd, ite_true, ite_false]
    · refine finishRegs n7 _ fr7 sp7 ra7 s07 fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 => ?_
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0]
        exact r10keep r h0 h1 h2 h3 h4 h5 h6 h7 h8
    · intro x hx; rw [mem7]; exact m10x x hx
  · obtain ⟨b0, b4⟩ := bytesMem_some (out := G) (hR.trans hR1)
    rw [← mem10] at b0 b4
    rw [b0] at u1
    have hp0 : p ≠ 0 := bytesResult_ne_zero hbuf.1 hbuf.2 (by decide) hR1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hc10 0x1A u16_at_18 (by decide)
      (by simp +decide only [upd, ite_true, ite_false]; simpa [branchTaken] using hp0)
    obtain ⟨n3, d3, u3⟩ := u2.lw hc10 u16_at_1a (off' := 0x1C) (by decide)
      (by rw [show upd (reg m10) a0 p sp = G by simp +decide [upd, r10sp]]; exact aligned_add hGa (k := 4) (by decide))
    rw [show upd (reg m10) a0 p sp = G by simp +decide [upd, r10sp], b4] at u3
    obtain ⟨n4, d4, u4⟩ := u3.notTaken hc10 0x20 u16_at_1c (by decide)
      (by simp +decide [upd, r10s0])
    have hR' := hR1
    rw [bytesResult_eq] at hR'
    split at hR'
    case isFalse => cases hR'
    rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨hp1, -⟩ := hR'
    rw [show (2 : Word).toNat = 2 from rfl] at hle
    have hpk : ∀ j, j < 2 → p + BitVec.ofNat 32 j =
        ptr + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + j) := fun j _ => by
      rw [← hp1, ← add_ofNat_assoc, ofNat_toNat_self]
    have m10b : ∀ j, j < 2 → m10.mem (p + BitVec.ofNat 32 j) = m.mem (p + BitVec.ofNat 32 j) :=
      fun j hj => by
        have bS : Sep G 16 (p + BitVec.ofNat 32 j) 1 := by
          rw [hpk j hj]; exact (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
        have bE : Sep (self + 8) 4 (p + BitVec.ofNat 32 j) 1 := by
          rw [hpk j hj]; exact (hBE.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
        rw [m10x _ bS]; unfold u16Mem; rw [hptr, hlen, hR1]; exact memStore32_get_sep bE
    have q4a0 : reg n4 a0 = p := by rw [u4.regs]; simp +decide [upd]
    obtain ⟨n5, d5, u5⟩ := u4.self.lbu hc10 u16_at_20 (off' := 0x24) (by decide)
    rw [q4a0, add_lit_zero] at u5
    obtain ⟨n6, d6, u6⟩ := u5.lbu hc10 u16_at_24 (off' := 0x28) (by decide)
    rw [show upd (reg n4) a1 ((m10.mem p).zeroExtend 32) a0 = p by simp +decide [upd, q4a0]] at u6
    obtain ⟨n7, d7, u7⟩ := u6.aluImm hc10 u16_at_28 (off' := 0x2A) (by decide)
    obtain ⟨n8, d8, u8⟩ := u7.aluImm hc10 u16_at_2a (off' := 0x2C) (by decide)
    obtain ⟨n9, d9, u9⟩ := u8.alu hc10 u16_at_2c (off' := 0x2E) (by decide)
    obtain ⟨n10, d10, u10⟩ := u9.jump hc10 u16_at_2e (off' := 0x3C) (by decide)
      (by rw [u9.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x3C (by decide)))
    have q4sp : reg n4 sp = G := by rw [u4.regs]; simp +decide [upd, r10sp]
    obtain ⟨n11, c11, pc11, mem11, sp11, ra11, s011, fr11⟩ := u16_epilogue (r0 := reg m ra)
      (r8 := reg m s0) hc10 u10 (by simp +decide [upd, q4sp]) hGa
      (by rw [show G + 0x0C = G + BitVec.ofNat 32 0x0C from rfl, m10slots 0x0C (by omega) (by omega)]
          exact M2slots.1)
      (by rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, m10slots 8 (by omega) (by omega)]
          exact M2slots.2) hret'
    refine ⟨n11, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
      (.cons e9 (c10.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
      (.cons d8 (.cons d9 (.cons d10 c11))))))))))))))))))), by rw [pc11, hra], by rw [sp11, ← hspG],
      ?_, ?_, ?_⟩
    · rw [fr11 a0 (by decide) (by decide) (by decide)]
      unfold u16Result; rw [hptr, hlen, hR1]
      simp +decide only [upd, ite_true, ite_false]
      have b0' : m10.mem p = m.mem p := by have := m10b 0 (by omega); rwa [add_ofNat_zero] at this
      rw [show aluEval .sll ((m10.mem (p + 1)).zeroExtend 32) 0x18 = _ from sll_zext _ 24 (by omega),
        show aluEval .sll ((m10.mem p).zeroExtend 32) 0x10 = _ from sll_zext _ 16 (by omega), b0',
        show m10.mem (p + 1) = m.mem (p + 1) from m10b 1 (by omega)]
      rfl
    · refine finishRegs n11 _ fr11 sp11 ra11 s011 fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 => ?_
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1]
        rw [u4.regs]; simp [upd, hr, h0, h1]
        exact r10keep r h0 h1 h2 h3 h4 h5 h6 h7 h8
    · intro x hx; rw [mem11]; exact m10x x hx

theorem u16_ok_bit0 (b0 b1 : BitVec 8) :
    ((b1.zeroExtend 32 <<< 24 ||| b0.zeroExtend 32 <<< 16 : Word) &&& 1) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases h : i = 0
  · subst h; simp
  · simp [h]
theorem version_compare (v : Word) :
    aluEval .or (aluEval .add (aluEval .sltu 0 (aluEval .add v 0xFFFFFFFF)) 0xFFFFFFFF) 3 =
      if v == 1 then 0xFFFFFFFF else 3 := by
  by_cases h : v = 1
  · subst h; decide
  · have hx : v + 0xFFFFFFFF ≠ 0 := fun e => h (by
      have := congrArg (· + 1) e
      simp only [BitVec.add_assoc] at this
      rw [show (0xFFFFFFFF : Word) + 1 = 0 from rfl] at this
      exact (BitVec.add_zero v).symm.trans (this.trans (BitVec.zero_add 1)))
    have hu : (0 : Word).ult (v + 0xFFFFFFFF) = true := by
      simp only [BitVec.ult, decide_eq_true_eq]
      have : (v + 0xFFFFFFFF).toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      show 0 < (v + 0xFFFFFFFF).toNat
      omega
    have hb : (v == 1) = false := beq_eq_false_iff_ne.mpr h
    simp only [aluEval, hu, ite_true, hb]
    decide

/-- What `Reader::version_1` returns in `a0`. -/
def version1Result (M : Word → BitVec 8) (self : Word) : Word :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 2 with
  | none => 0
  | some _ => if u16Result M self >>> 16 == 1 then 0xFFFFFFFF else 3

theorem v1_at_00 : fetchRel readerVersion1Code 0x00 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem v1_at_02 : fetchRel readerVersion1Code 0x02 = some (.store .sw sp ra 0x0C, 2) := by decide
theorem v1_at_04 : fetchRel readerVersion1Code 0x04 = some (.auipc ra 0, 4) := by decide
theorem v1_at_08 : fetchRel readerVersion1Code 0x08 = some (.jalr ra ra 0x122, 4) := by decide
theorem v1_at_0c : fetchRel readerVersion1Code 0x0C = some (.aluImm .and a1 a0 1, 4) := by decide
theorem v1_at_10 : fetchRel readerVersion1Code 0x10 = some (.branch .bne a1 x0 0x12, 2) := by decide
theorem v1_at_12 : fetchRel readerVersion1Code 0x12 = some (.aluImm .srl a0 a0 0x10, 2) := by decide
theorem v1_at_14 : fetchRel readerVersion1Code 0x14 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem v1_at_16 : fetchRel readerVersion1Code 0x16 = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem v1_at_1a : fetchRel readerVersion1Code 0x1A = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem v1_at_1c : fetchRel readerVersion1Code 0x1C = some (.aluImm .or a0 a0 3, 4) := by decide
theorem v1_at_20 : fetchRel readerVersion1Code 0x20 = some (.jal x0 4, 2) := by decide
theorem v1_at_22 : fetchRel readerVersion1Code 0x22 = some (.aluImm .srl a0 a0 8, 2) := by decide
theorem v1_at_24 : fetchRel readerVersion1Code 0x24 = some (.load .lw ra sp 0x0C, 2) := by decide
theorem v1_at_26 : fetchRel readerVersion1Code 0x26 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem v1_at_28 : fetchRel readerVersion1Code 0x28 = some (.jalr x0 ra 0, 2) := by decide

theorem v1_epilogue {m : Machine} {M : Word → BitVec 8} {f : Fin 32 → Word} {base G r0 : Word}
    (hc : CodeIn M base readerVersion1Code) (t : St M base m 0x24 f) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) (h1 : memLoad32 M (G + 0x0C) = r0) (hret : r0 &&& ~~~1 = r0) :
    ∃ m', Steps m m' ∧ m'.pc = r0 ∧ m'.mem = M ∧ reg m' sp = G + 0x10 ∧ reg m' ra = r0 ∧
      ∀ r, r ≠ sp → r ≠ ra → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m1, e1, t1⟩ := t.lw hc v1_at_24 (off' := 0x26) (by decide)
    (by rw [hsp]; exact aligned_add hG (k := 0x0C) (by decide))
  rw [hsp, h1] at t1
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc v1_at_26 (off' := 0x28) (by decide)
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := t2.jalr hc v1_at_28
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

/-- **The compiled `Reader::version_1` is correct.** With its bytes at
`base`, `Reader::u16`'s and `Reader::bytes`'s where the image puts them,
the reader and stack as `readerU16_correct` needs them but with 32 bytes of
stack (its frame and `u16`'s), there is an execution that reaches the
return address with `sp` restored, `a0` as `version1Result` says, every
register but `a0` through `a5` unchanged, and memory outside those 32 bytes
as `u16Mem` says. -/
theorem readerVersion1_correct (m : Machine) (base retAddr self : Word)
    (hcode : CodeAt m base readerVersion1Code)
    (hucode : CodeAt m (base + 0x126) readerU16Code)
    (hbcode : CodeAt m (base + 0x126 + 0xFFFFFFDA) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = self) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSv : Sep (reg m sp + 0xFFFFFFE0) 32 base readerVersion1Code.length)
    (hSu : Sep (reg m sp + 0xFFFFFFE0) 32 (base + 0x126) readerU16Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFE0) 32 (base + 0x126 + 0xFFFFFFDA) readerBytesCode.length)
    (hEv : Sep (self + 8) 4 base readerVersion1Code.length)
    (hEu : Sep (self + 8) 4 (base + 0x126) readerU16Code.length)
    (hEb : Sep (self + 8) 4 (base + 0x126 + 0xFFFFFFDA) readerBytesCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFE0) 32)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFE0) 32)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      reg m' a0 = version1Result m.mem self ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFE0) 32 x 1 → m'.mem x = u16Mem m.mem self x := by
  have hc : CodeIn m.mem base readerVersion1Code := hcode
  have s0' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  have hG : reg m sp + 0xFFFFFFF0 = reg m sp + 0xFFFFFFE0 + 16 := by rw [BitVec.add_assoc]; rfl
  have hspG : reg m sp = reg m sp + 0xFFFFFFF0 + 0x10 := by
    rw [BitVec.add_assoc]; exact (BitVec.add_zero _).symm
  obtain ⟨S, hSdef⟩ : ∃ S, reg m sp + 0xFFFFFFE0 = S := ⟨_, rfl⟩
  rw [hSdef] at hSv hSu hSb hRS hBS hG ⊢
  obtain ⟨G, hGdef⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hGdef] at hG hspG
  have hGa : G.toNat % 4 = 0 := hGdef ▸ aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  have hGS : G + 0xFFFFFFF0 = S := by rw [hG, BitVec.add_assoc]; exact BitVec.add_zero S
  have sepG : ∀ c l, c + l ≤ 16 → ∀ (b : Word) (n : Nat), Sep S 32 b n →
      Sep (G + BitVec.ofNat 32 c) l b n := fun c l h b n hs => by
    rw [hG]; show Sep (S + BitVec.ofNat 32 16 + BitVec.ofNat 32 c) l b n
    rw [add_ofNat_assoc]; exact hs.sub (c := 16 + c) (l := l) (by omega)
  have s16 : ∀ (b : Word) (n : Nat), Sep S 32 b n → Sep (G + 0xFFFFFFF0) 16 b n := fun b n h => by
    rw [hGS]; have := h.sub (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at this
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc v1_at_00 (off' := 0x02) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hGdef] at t1
  have r1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  obtain ⟨m2, e2, t2⟩ := t1.sw hc v1_at_02 (off' := 0x04) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 0x0C) (by decide))
  rw [r1sp, show upd (reg m) sp G ra = reg m ra by simp +decide [upd]] at t2
  have hc2 := hc.store32 (v := reg m ra) (show Sep (G + 0x0C) 4 base _ from sepG 0x0C 4 (by omega) _ _ hSv)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 m.mem (G + 0x0C) (reg m ra) = M1 := ⟨_, rfl⟩
  rw [hM1] at t2 hc2
  have M1out : ∀ x, Sep S 32 x 1 → M1 x = m.mem x := fun x h => by
    rw [← hM1, memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from sepG 0x0C 4 (by omega) _ _ h)]
  obtain ⟨m3, e3, t3⟩ := t2.auipc hc2 v1_at_04 (off' := 0x08) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := t3.call hc2 v1_at_08
  have r4 : ∀ r, r ≠ ra → r ≠ sp → reg m4 r = reg m r := fun r h1 h2 => by
    rw [regs4]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h1, h2]
  have r4sp : reg m4 sp = G := by rw [regs4]; simp +decide [upd]
  have r4ra : reg m4 ra = base + BitVec.ofNat 32 0x0C := by
    rw [regs4]; simp +decide only [upd, ite_true, ite_false]; exact add_ofNat_assoc base 8 4
  have hevu : (base + 0x126).toNat % 2 = 0 := even_at base hbase 0x126 (by decide)
  have hpc4 : m4.pc = base + 0x126 := by
    rw [pc4]; simp +decide only [upd, ite_true, ite_false]
    rw [show base + BitVec.ofNat 32 4 + 0 + 0x122 = base + 0x126 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl, even_clear _ hevu]
  have hm4 : m4.mem = M1 := mem4
  have hSself : Sep S 32 self 12 := hRS.symm
  have ld1 : ∀ c, c + 4 ≤ 12 → memLoad32 M1 (self + BitVec.ofNat 32 c) =
      memLoad32 m.mem (self + BitVec.ofNat 32 c) := fun c hc' => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact M1out _ (hSself.subR (c := c + j) (l := 1) (by omega))
  have l1p : memLoad32 M1 self = memLoad32 m.mem self := by
    have := ld1 0 (by omega); rwa [add_ofNat_zero] at this
  have l1l : memLoad32 M1 (self + 4) = memLoad32 m.mem (self + 4) := ld1 4 (by omega)
  have l1e : memLoad32 M1 (self + 8) = memLoad32 m.mem (self + 8) := ld1 8 (by omega)
  have bufS : ∀ j, j < (memLoad32 m.mem (self + 4)).toNat →
      M1 (memLoad32 m.mem self + BitVec.ofNat 32 j) = m.mem (memLoad32 m.mem self + BitVec.ofNat 32 j) :=
    fun j hj => M1out _ (hBS.sub (c := j) (l := 1) hj).symm
  have hu16 : u16Result M1 self = u16Result m.mem self := by
    unfold u16Result; rw [l1p, l1l, l1e]
    rcases hR : bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 2
      with _ | ⟨p, e⟩
    · rfl
    · dsimp only
      rw [bytesResult_eq] at hR
      split at hR
      case isFalse => cases hR
      rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at hR
      obtain ⟨hp, -⟩ := hR
      rw [show (2 : Word).toNat = 2 from rfl] at hle
      have h0 := bufS ((memLoad32 m.mem (self + 8)).toNat) (by omega)
      have h1 := bufS ((memLoad32 m.mem (self + 8)).toNat + 1) (by omega)
      rw [ofNat_toNat_self, hp] at h0
      rw [← add_ofNat_assoc, ofNat_toNat_self, hp] at h1
      have h1' : M1 (p + 1) = m.mem (p + 1) := h1
      rw [h0, h1']
  have hu16m : ∀ x, Sep S 32 x 1 → u16Mem M1 self x = u16Mem m.mem self x := fun x h => by
    unfold u16Mem; rw [l1p, l1l, l1e]
    rcases bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 2
      with _ | ⟨p, e⟩
    · exact M1out x h
    · exact memStore32_congr (M1out x h)
  obtain ⟨m5, c5, pc5, sp5, a05, fr5, mem5⟩ := readerU16_correct m4 (base + 0x126)
    (base + BitVec.ofNat 32 0x0C) self
    (fun i hi => by rw [hm4, M1out _ (hSu.subR (c := i) (l := 1) (by omega))]; exact hucode i hi)
    (fun i hi => by rw [hm4, M1out _ (hSb.subR (c := i) (l := 1) (by omega))]; exact hbcode i hi)
    hevu hpc4 (by rw [r4 a0 (by decide) (by decide), ha0]) r4ra
    (even_clear _ (even_at base hbase 0x0C (by decide))) (by rw [r4sp]; exact hGa) hself
    (by rw [hm4, l1p, l1l]; exact hbuf) (by rw [r4sp]; exact s16 _ _ hSu) (by rw [r4sp]; exact s16 _ _ hSb)
    hEu hEb (by rw [r4sp, hGS]; have := hRS.subR (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [r4sp, hm4, l1p, l1l, hGS]; have := hBS.subR (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [hm4, l1p, l1l]; exact hBE)
  rw [hm4, hu16] at a05
  rw [r4sp] at sp5 mem5
  rw [hm4] at mem5
  have m5x : ∀ x, Sep S 32 x 1 → m5.mem x = u16Mem m.mem self x := fun x h => by
    rw [mem5 x (s16 _ _ h), hu16m x h]
  have codeS : ∀ i, i < readerVersion1Code.length → Sep S 32 (base + BitVec.ofNat 32 i) 1 :=
    fun i hi => hSv.subR (c := i) (l := 1) (by omega)
  have hc5 : CodeIn m5.mem base readerVersion1Code := fun i hi => by
    rw [m5x _ (codeS i hi)]; unfold u16Mem
    rcases bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 2
      with _ | ⟨q, e'⟩
    · exact hc i hi
    · dsimp only; rw [memStore32_get_sep (hEv.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have gS : ∀ c, G + BitVec.ofNat 32 c = S + BitVec.ofNat 32 (16 + c) := fun c => by
    rw [hG]; exact add_ofNat_assoc S 16 c
  have slot : memLoad32 m5.mem (G + 0x0C) = reg m ra := by
    have h : memLoad32 m5.mem (G + BitVec.ofNat 32 0x0C) = memLoad32 M1 (G + BitVec.ofNat 32 0x0C) :=
      memLoad32_congr fun j hj => by
        have hin : Sep (G + 0xFFFFFFF0) 16 (G + BitVec.ofNat 32 (0x0C + j)) 1 := by
          rw [hGS, gS]
          have := sep_offsets S (c := 0) (n := 16) (d := 16 + (0x0C + j)) (k := 1) (by omega) (by omega)
            (by omega)
          rwa [add_ofNat_zero] at this
        have hse : Sep (self + 8) 4 (G + BitVec.ofNat 32 (0x0C + j)) 1 := by
          rw [gS]; exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 16 + (0x0C + j)) (l := 1) (by omega)
        rw [add_ofNat_assoc, mem5 _ hin]
        unfold u16Mem
        rcases bytesResult (memLoad32 M1 self) (memLoad32 M1 (self + 4)) (memLoad32 M1 (self + 8)) 2
          with _ | ⟨q, e'⟩
        · rfl
        · exact memStore32_get_sep hse
    have h2 : memLoad32 M1 (G + 0x0C) = reg m ra := by rw [← hM1]; exact memLoad32_store32_same _ _ _
    exact h.trans h2
  have t5 : St m5.mem base m5 0x0C (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have r5 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp →
      reg m5 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 => by
    rw [fr5 r h0 h1 h2 h3 h4 h5, r4 r h6 h7]
  obtain ⟨n1, d1, u1⟩ := t5.aluImm hc5 v1_at_0c (off' := 0x10) (by decide)
  rw [a05] at u1
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  have fin : ∀ (n : Machine) (g : Fin 32 → Word),
      (∀ r, r ≠ sp → r ≠ ra → reg n r = g r) → reg n sp = G + 0x10 → reg n ra = reg m ra →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → g r = reg m r) →
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n r = reg m r :=
    fun n g hn hsp' hra' hg r h0 h1 h2 h3 h4 h5 => by
      by_cases e1 : r = sp
      · subst e1; rw [hsp', ← hspG]
      by_cases e2 : r = ra
      · subst e2; exact hra'
      rw [hn r e1 e2]; exact hg r h0 h1 h2 h3 h4 h5 e2 e1
  have hz5 := t5.zero
  rcases hR : bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 2
    with _ | ⟨p, e⟩
  · have hu : u16Result m.mem self = 1 := by unfold u16Result; rw [hR]
    rw [hu] at u1
    obtain ⟨n2, d2, u2⟩ := u1.taken hc5 0x22 v1_at_10 (by decide) (by simp +decide [upd])
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hc5 v1_at_22 (off' := 0x24) (by decide)
    obtain ⟨n4, c4, pc4, mem4, sp4, ra4, fr4⟩ := v1_epilogue (r0 := reg m ra) hc5 u3
      (by simp +decide [upd, sp5]) hGa slot hret'
    refine ⟨n4, .cons e1 (.cons e2 (.cons e3 ((Steps.cons e4 c5).trans (.cons d1 (.cons d2
      (.cons d3 c4)))))), by rw [pc4, hra], by rw [sp4, ← hspG], ?_, ?_, ?_⟩
    · rw [fr4 a0 (by decide) (by decide)]
      unfold version1Result; rw [hR]
      simp +decide only [upd, ite_true, ite_false, a05, hu]
    · refine fin n4 _ fr4 sp4 ra4 fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1]
        exact r5 r h0 h1 h2 h3 h4 h5 h6 h7
    · intro x hx; rw [mem4]; exact m5x x hx
  · have hu : u16Result m.mem self =
        (m.mem (p + 1)).zeroExtend 32 <<< 24 ||| (m.mem p).zeroExtend 32 <<< 16 := by
      unfold u16Result; rw [hR]
    rw [hu] at u1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hc5 0x12 v1_at_10 (by decide)
      (by simp +decide only [upd, ite_true, ite_false]; rw [show aluEval .and _ 1 = _ from u16_ok_bit0 _ _]; rfl)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hc5 v1_at_12 (off' := 0x14) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hc5 v1_at_14 (off' := 0x16) (by decide)
    obtain ⟨n5, d5, u5⟩ := u4.alu hc5 v1_at_16 (off' := 0x1A) (by decide)
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hc5 v1_at_1a (off' := 0x1C) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.aluImm hc5 v1_at_1c (off' := 0x20) (by decide)
    obtain ⟨n8, d8, u8⟩ := u7.jump hc5 v1_at_20 (off' := 0x24) (by decide)
      (by rw [u7.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x24 (by decide)))
    obtain ⟨n9, c9, pc9, mem9, sp9, ra9, fr9⟩ := v1_epilogue (r0 := reg m ra) hc5 u8
      (by simp +decide [upd, sp5]) hGa slot hret'
    refine ⟨n9, .cons e1 (.cons e2 (.cons e3 ((Steps.cons e4 c5).trans (.cons d1 (.cons d2
      (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 c9))))))))))), by rw [pc9, hra],
      by rw [sp9, ← hspG], ?_, ?_, ?_⟩
    · rw [fr9 a0 (by decide) (by decide)]
      unfold version1Result; rw [hR]; dsimp only
      simp +decide only [upd, ite_true, ite_false, a05, hz5]
      have hs : aluEval .srl (u16Result m.mem self) 0x10 = u16Result m.mem self >>> 16 := rfl
      rw [hs]
      exact version_compare _
    · refine fin n9 _ fr9 sp9 ra9 fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1]
        exact r5 r h0 h1 h2 h3 h4 h5 h6 h7
    · intro x hx; rw [mem9]; exact m5x x hx

end C3.RV32
