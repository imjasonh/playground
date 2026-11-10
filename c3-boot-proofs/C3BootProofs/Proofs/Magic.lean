import C3BootProofs.Proofs.Outlined

/-!
# `c3_verify::reader::Reader::magic`, as compiled

`Reader::magic` reads 4 bytes with `Reader::array::<4>` and fails with
`Error::BadMagic` (2) unless they equal the magic number. LLVM passes the
magic as a little-endian word in `a1` instead of a pointer, and returns the
`Result<(), Error>` in `a0`: 0xFF in the low byte for `Ok`, the error
otherwise. The 4 bytes are loaded by a machine-outlined helper that `magic`
enters with `auipc t0; jalr t0`. `readerMagic_correct` proves it on the
RV32 model through `readerArray4_correct`.
-/

namespace C3.RV32

open C3.Image

/-- What `Reader::magic` returns in `a0`. -/
def magicResult (M : Word → BitVec 8) (self k : Word) : Word :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with
  | none => 0
  | some (p, _) => if memLoad32 M p == k then 0xFFFFFFFF else 2

/-- Memory after `Reader::magic` returns, outside the stack it uses. -/
def magicMem (M : Word → BitVec 8) (self : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with
  | none => M
  | some (_, e) => memStore32 M (self + 8) e

theorem mg_at_00 : fetchRel readerMagicCode 0x00 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem mg_at_02 : fetchRel readerMagicCode 0x02 = some (.store .sw sp ra 0x0C, 2) := by decide
theorem mg_at_04 : fetchRel readerMagicCode 0x04 = some (.store .sw sp s0 8, 2) := by decide
theorem mg_at_06 : fetchRel readerMagicCode 0x06 = some (.alu .add s0 x0 a1, 2) := by decide
theorem mg_at_08 : fetchRel readerMagicCode 0x08 = some (.alu .add a1 x0 a0, 2) := by decide
theorem mg_at_0a : fetchRel readerMagicCode 0x0A = some (.alu .add a0 x0 sp, 2) := by decide
theorem mg_at_0c : fetchRel readerMagicCode 0x0C = some (.auipc ra 0, 4) := by decide
theorem mg_at_10 : fetchRel readerMagicCode 0x10 = some (.jalr ra ra 0x1A0, 4) := by decide
theorem mg_at_14 : fetchRel readerMagicCode 0x14 = some (.load .lbu a0 sp 0, 4) := by decide
theorem mg_at_18 : fetchRel readerMagicCode 0x18 = some (.branch .beq a0 x0 8, 2) := by decide
theorem mg_at_1a : fetchRel readerMagicCode 0x1A = some (.load .lbu a0 sp 1, 4) := by decide
theorem mg_at_1e : fetchRel readerMagicCode 0x1E = some (.jal x0 0x1C, 2) := by decide
theorem mg_at_20 : fetchRel readerMagicCode 0x20 = some (.load .lw a0 sp 4, 2) := by decide
theorem mg_at_22 : fetchRel readerMagicCode 0x22 = some (.auipc t0 0x16000, 4) := by decide
theorem mg_at_26 : fetchRel readerMagicCode (0x22 + 4) = some (.jalr t0 t0 0x7E2, 4) := by decide
theorem mg_at_2a : fetchRel readerMagicCode 0x2A = some (.alu .or a2 a2 a3, 2) := by decide
theorem mg_at_2c : fetchRel readerMagicCode 0x2C = some (.alu .or a0 a0 a2, 2) := by decide
theorem mg_at_2e : fetchRel readerMagicCode 0x2E = some (.alu .xor a0 a0 s0, 2) := by decide
theorem mg_at_30 : fetchRel readerMagicCode 0x30 = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem mg_at_34 : fetchRel readerMagicCode 0x34 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem mg_at_36 : fetchRel readerMagicCode 0x36 = some (.aluImm .or a0 a0 2, 4) := by decide
theorem mg_at_3a : fetchRel readerMagicCode 0x3A = some (.load .lw ra sp 0x0C, 2) := by decide
theorem mg_at_3c : fetchRel readerMagicCode 0x3C = some (.load .lw s0 sp 8, 2) := by decide
theorem mg_at_3e : fetchRel readerMagicCode 0x3E = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem mg_at_40 : fetchRel readerMagicCode 0x40 = some (.jalr x0 ra 0, 2) := by decide

theorem ml_at_00 : fetchRel magicLoadCode 0x00 = some (.load .lbu a1 a0 1, 4) := by decide
theorem ml_at_04 : fetchRel magicLoadCode 0x04 = some (.load .lbu a2 a0 2, 4) := by decide
theorem ml_at_08 : fetchRel magicLoadCode 0x08 = some (.load .lbu a3 a0 3, 4) := by decide
theorem ml_at_0c : fetchRel magicLoadCode 0x0C = some (.load .lbu a0 a0 0, 4) := by decide
theorem ml_at_10 : fetchRel magicLoadCode 0x10 = some (.aluImm .sll a1 a1 8, 2) := by decide
theorem ml_at_12 : fetchRel magicLoadCode 0x12 = some (.aluImm .sll a2 a2 0x10, 2) := by decide
theorem ml_at_14 : fetchRel magicLoadCode 0x14 = some (.aluImm .sll a3 a3 0x18, 2) := by decide
theorem ml_at_16 : fetchRel magicLoadCode 0x16 = some (.alu .or a0 a0 a1, 2) := by decide
theorem ml_at_18 : fetchRel magicLoadCode 0x18 = some (.jalr x0 t0 0, 2) := by decide

/-- The outlined helper that `magic` loads its 4 bytes with: from the word
at `a0`, it leaves the low two bytes joined in `a0` and the high two bytes
shifted into place in `a2` and `a3`, and returns to `t0`. -/
theorem magicLoad_correct {M : Word → BitVec 8} {b : Word} {m : Machine} {g : Fin 32 → Word}
    (s : St M b m 0 g) (hc : CodeIn M b magicLoadCode) :
    ∃ m', Steps m m' ∧ m'.pc = g t0 &&& ~~~1 ∧ m'.mem = M ∧
      reg m' a0 = ((M (g a0)).zeroExtend 32 ||| (M (g a0 + 1)).zeroExtend 32 <<< 8) ∧
      reg m' a2 = (M (g a0 + 2)).zeroExtend 32 <<< 16 ∧
      reg m' a3 = (M (g a0 + 3)).zeroExtend 32 <<< 24 ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m' r = g r := by
  obtain ⟨m1, e1, t1⟩ := s.lbu hc ml_at_00 (off' := 0x04) (by decide)
  obtain ⟨m2, e2, t2⟩ := t1.lbu hc ml_at_04 (off' := 0x08) (by decide)
  obtain ⟨m3, e3, t3⟩ := t2.lbu hc ml_at_08 (off' := 0x0C) (by decide)
  obtain ⟨m4, e4, t4⟩ := t3.lbu hc ml_at_0c (off' := 0x10) (by decide)
  obtain ⟨m5, e5, t5⟩ := t4.aluImm hc ml_at_10 (off' := 0x12) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.aluImm hc ml_at_12 (off' := 0x14) (by decide)
  obtain ⟨m7, e7, t7⟩ := t6.aluImm hc ml_at_14 (off' := 0x16) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.alu hc ml_at_16 (off' := 0x18) (by decide)
  obtain ⟨m9, e9, pc9, mem9, regs9⟩ := t8.jalr hc ml_at_18
  have sh : ∀ (v : BitVec 8) (k : Nat), k < 32 →
      aluEval .sll (v.zeroExtend 32) (BitVec.ofNat 32 k) = v.zeroExtend 32 <<< k := fun v k hk => by
    show v.zeroExtend 32 <<< ((BitVec.ofNat 32 k).toNat % 32) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32), Nat.mod_eq_of_lt hk]
  refine ⟨m9, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
    (.single e9)))))))), ?_, mem9, ?_, ?_, ?_, fun r h0 h1 h2 h3 => ?_⟩
  · rw [pc9, add_lit_zero]; simp +decide only [upd, ite_true, ite_false]
  · rw [regs9]; simp +decide only [upd, ite_true, ite_false, add_lit_zero]
    rw [show aluEval .sll ((M (g a0 + 1)).zeroExtend 32) 8 = _ from sh _ 8 (by omega)]; rfl
  · rw [regs9]; simp +decide only [upd, ite_true, ite_false]
    exact sh _ 16 (by omega)
  · rw [regs9]; simp +decide only [upd, ite_true, ite_false]
    exact sh _ 24 (by omega)
  · rw [regs9]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; exact t1.zero.symm ▸ s.zero ▸ rfl
    · simp [upd, hr, h0, h1, h2, h3]

/-- `magic`'s compare: `xor`, `sltu`, `addi -1`, `ori 2`. -/
theorem magic_compare (v k : Word) :
    aluEval .or (aluEval .add (aluEval .sltu 0 (aluEval .xor v k)) 0xFFFFFFFF) 2 =
      if v == k then 0xFFFFFFFF else 2 := by
  by_cases h : v = k
  · subst h
    rw [show (v == v) = true from beq_iff_eq.mpr rfl]; simp only [↓reduceIte]
    show aluEval .or (aluEval .add (aluEval .sltu 0 (v ^^^ v)) 0xFFFFFFFF) 2 = 0xFFFFFFFF
    rw [BitVec.xor_self]
    decide
  · have hx : v ^^^ k ≠ 0 := fun e => h (by
      have := congrArg (· ^^^ k) e
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      exact this.trans BitVec.zero_xor)
    have hu : (0 : Word).ult (v ^^^ k) = true := by
      simp only [BitVec.ult, decide_eq_true_eq]
      have : (v ^^^ k).toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      show 0 < (v ^^^ k).toNat
      omega
    have hb : (v == k) = false := beq_eq_false_iff_ne.mpr h
    simp only [aluEval, hu, ite_true, hb]
    decide

theorem mg_epilogue {m : Machine} {M : Word → BitVec 8} {f : Fin 32 → Word} {base G r0 r8 : Word}
    (hc : CodeIn M base readerMagicCode) (t : St M base m 0x3A f) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) (h1 : memLoad32 M (G + 0x0C) = r0) (h2 : memLoad32 M (G + 8) = r8)
    (hret : r0 &&& ~~~1 = r0) :
    ∃ m', Steps m m' ∧ m'.pc = r0 ∧ m'.mem = M ∧ reg m' sp = G + 0x10 ∧ reg m' ra = r0 ∧
      reg m' s0 = r8 ∧ ∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m1, e1, t1⟩ := t.lw hc mg_at_3a (off' := 0x3C) (by decide)
    (by rw [hsp]; exact aligned_add hG (k := 0x0C) (by decide))
  rw [hsp, h1] at t1
  have u1 : upd f ra r0 sp = G := by simp +decide [upd, hsp]
  obtain ⟨m2, e2, t2⟩ := t1.lw hc mg_at_3c (off' := 0x3E) (by decide)
    (by rw [u1]; exact aligned_add hG (k := 8) (by decide))
  rw [u1, h2] at t2
  obtain ⟨m3, e3, t3⟩ := t2.aluImm hc mg_at_3e (off' := 0x40) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := t3.jalr hc mg_at_40
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

/-- **The compiled `Reader::magic` is correct.** With its bytes at `base`,
`Reader::array::<4>`'s, `Reader::bytes`'s, and its load helper's where the
image puts them, a reader `self` over a slice that is not null and doesn't
wrap, the magic `k` in `a1`, everything aligned, and the 48 bytes of stack
below `sp`, the reader, its position, and its buffer kept apart as the
hypotheses list, there is an execution that reaches the return address with
`sp` restored, `a0` as `magicResult` says, every register but `a0` through
`a5` and `t0` unchanged, and memory outside those 48 bytes as `magicMem`
says. -/
theorem readerMagic_correct (m : Machine) (base retAddr self k : Word)
    (hcode : CodeAt m base readerMagicCode)
    (hacode : CodeAt m (base + 0x1AC) readerArray4Code)
    (hbcode : CodeAt m (base + 0x1AC + 0xFFFFFF96) readerBytesCode)
    (hlcode : CodeAt m (base + 0x16804) magicLoadCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = self) (ha1 : reg m a1 = k) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSu : Sep (reg m sp + 0xFFFFFFD0) 48 base readerMagicCode.length)
    (hSa : Sep (reg m sp + 0xFFFFFFD0) 48 (base + 0x1AC) readerArray4Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFD0) 48 (base + 0x1AC + 0xFFFFFF96) readerBytesCode.length)
    (hSl : Sep (reg m sp + 0xFFFFFFD0) 48 (base + 0x16804) magicLoadCode.length)
    (hEu : Sep (self + 8) 4 base readerMagicCode.length)
    (hEa : Sep (self + 8) 4 (base + 0x1AC) readerArray4Code.length)
    (hEb : Sep (self + 8) 4 (base + 0x1AC + 0xFFFFFF96) readerBytesCode.length)
    (hEl : Sep (self + 8) 4 (base + 0x16804) magicLoadCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFD0) 48)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFD0) 48)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧ reg m' a0 = magicResult m.mem self k ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFD0) 48 x 1 → m'.mem x = magicMem m.mem self x := by
  have hc : CodeIn m.mem base readerMagicCode := hcode
  have s0' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  have hG : reg m sp + 0xFFFFFFF0 = reg m sp + 0xFFFFFFD0 + 32 := by rw [BitVec.add_assoc]; rfl
  have hspG : reg m sp = reg m sp + 0xFFFFFFF0 + 0x10 := by
    rw [BitVec.add_assoc]; exact (BitVec.add_zero _).symm
  obtain ⟨S, hSdef⟩ : ∃ S, reg m sp + 0xFFFFFFD0 = S := ⟨_, rfl⟩
  rw [hSdef] at hSu hSa hSb hSl hRS hBS hG ⊢
  obtain ⟨G, hGdef⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hGdef] at hG hspG
  have hGa : G.toNat % 4 = 0 := hGdef ▸ aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  obtain ⟨ptr, hptr⟩ : ∃ ptr, memLoad32 m.mem self = ptr := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, memLoad32 m.mem (self + 4) = len := ⟨_, rfl⟩
  rw [hptr, hlen] at hbuf hBS hBE
  -- 0x00 to 0x04: the frame.
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc mg_at_00 (off' := 0x02) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hGdef] at t1
  have r1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have sepG : ∀ c l, c + l ≤ 16 → ∀ (b : Word) (n : Nat), Sep S 48 b n →
      Sep (G + BitVec.ofNat 32 c) l b n := fun c l h b n hs => by
    rw [hG]; show Sep (S + BitVec.ofNat 32 32 + BitVec.ofNat 32 c) l b n
    rw [add_ofNat_assoc]; exact hs.sub (c := 32 + c) (l := l) (by omega)
  obtain ⟨m2, e2, t2⟩ := t1.sw hc mg_at_02 (off' := 0x04) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 0x0C) (by decide))
  rw [r1sp, show upd (reg m) sp G ra = reg m ra by simp +decide [upd]] at t2
  have hc2 := hc.store32 (v := reg m ra) (show Sep (G + 0x0C) 4 base _ from sepG 0x0C 4 (by omega) _ _ hSu)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 mg_at_04 (off' := 0x06) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [r1sp, show upd (reg m) sp G s0 = reg m s0 by simp +decide [upd]] at t3
  have hc3 := hc2.store32 (v := reg m s0) (show Sep (G + 8) 4 base _ from sepG 8 4 (by omega) _ _ hSu)
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0) = M2 :=
    ⟨_, rfl⟩
  rw [hM2] at t3 hc3
  have M2out : ∀ x, Sep S 48 x 1 → M2 x = m.mem x := fun x h => by
    rw [← hM2, memStore32_get_sep (show Sep (G + 8) 4 x 1 from sepG 8 4 (by omega) _ _ h),
      memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from sepG 0x0C 4 (by omega) _ _ h)]
  have M2slots : memLoad32 M2 (G + 0x0C) = reg m ra ∧ memLoad32 M2 (G + 8) = reg m s0 := by
    rw [← hM2]
    refine ⟨?_, memLoad32_store32_same _ _ _⟩
    rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x0C) 4 from
        sep_offsets G (c := 8) (n := 4) (d := 0x0C) (k := 4) (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  -- 0x06 to 0x10: the call to `Reader::array::<4>`.
  obtain ⟨m4, e4, t4⟩ := t3.alu hc3 mg_at_06 (off' := 0x08) (by decide)
  obtain ⟨m5, e5, t5⟩ := t4.alu hc3 mg_at_08 (off' := 0x0A) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.alu hc3 mg_at_0a (off' := 0x0C) (by decide)
  obtain ⟨m7, e7, t7⟩ := t6.auipc hc3 mg_at_0c (off' := 0x10) (by decide)
  obtain ⟨m8, e8, pc8, mem8, regs8⟩ := t7.call hc3 mg_at_10
  have r8 : ∀ r, reg m8 r = if r = ra then base + BitVec.ofNat 32 0x14 else
      if r = a0 then G else if r = a1 then self else if r = s0 then k else
      if r = sp then G else reg m r := by
    intro r; rw [regs8, show base + BitVec.ofNat 32 0x10 + 4 = base + BitVec.ofNat 32 0x14 from
      add_ofNat_assoc base 0x10 4]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp +decide [upd, hz]
    · by_cases h1 : r = ra
      · subst h1; simp +decide [upd]
      by_cases h2 : r = a0
      · subst h2; simp +decide [upd, aluEval]
      by_cases h3 : r = a1
      · subst h3; simp +decide [upd, aluEval, ha0]
      by_cases h4 : r = s0
      · subst h4; simp +decide [upd, aluEval, ha1]
      by_cases h5 : r = sp
      · subst h5; simp +decide [upd]
      simp [upd, hr, h1, h2, h3, h4, h5]
  have hev : (base + 0x1AC).toNat % 2 = 0 := even_at base hbase 0x1AC (by decide)
  have hev14 : (base + BitVec.ofNat 32 0x14).toNat % 2 = 0 := even_at base hbase 0x14 (by decide)
  have hpc8 : m8.pc = base + 0x1AC := by
    rw [pc8]; simp +decide only [upd, ite_true, ite_false]
    rw [show base + BitVec.ofNat 32 0x0C + 0 + 0x1A0 = base + 0x1AC by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl, even_clear _ hev]
  have hGS : G + 0xFFFFFFE0 = S := by rw [hG, BitVec.add_assoc]; exact BitVec.add_zero S
  have r8sp : reg m8 sp = G := by rw [r8]; simp +decide
  have hSself : Sep S 48 self 12 := hRS.symm
  have ld2 : ∀ c, c + 4 ≤ 12 → memLoad32 M2 (self + BitVec.ofNat 32 c) =
      memLoad32 m.mem (self + BitVec.ofNat 32 c) := fun c hc' => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact M2out _ (hSself.subR (c := c + j) (l := 1) (by omega))
  have l2p : memLoad32 M2 self = ptr := by
    have := ld2 0 (by omega); rw [add_ofNat_zero] at this; rw [this, hptr]
  have l2l : memLoad32 M2 (self + 4) = len := by rw [show self + 4 = self + BitVec.ofNat 32 4 from rfl, ld2 4 (by omega)]; exact hlen
  have l2e : memLoad32 M2 (self + 8) = memLoad32 m.mem (self + 8) := ld2 8 (by omega)
  have cA : CodeIn M2 (base + 0x1AC) readerArray4Code := fun i hi => by
    rw [M2out _ (hSa.subR (c := i) (l := 1) (by omega))]; exact hacode i hi
  have cB : CodeIn M2 (base + 0x1AC + 0xFFFFFF96) readerBytesCode := fun i hi => by
    rw [M2out _ (hSb.subR (c := i) (l := 1) (by omega))]; exact hbcode i hi
  have hm8 : m8.mem = M2 := mem8
  obtain ⟨m9, c9, pc9, sp9, fr9, mem9⟩ := readerArray4_correct m8 (base + 0x1AC)
    (base + 0x1AC + 0xFFFFFF96) (base + BitVec.ofNat 32 0x14) G self
    (fun i hi => by rw [hm8]; exact cA i hi) (fun i hi => by rw [hm8]; exact cB i hi) rfl hev
    hpc8 (by rw [r8]; simp +decide) (by rw [r8]; simp +decide) (by rw [r8]; simp +decide)
    (even_clear _ hev14) (by rw [r8sp]; exact hGa) hGa hself (by rw [hm8, l2p, l2l]; exact hbuf)
    (by rw [r8sp, hGS]; have := hSa.sub (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [r8sp, hGS]; have := hSb.sub (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this)
    (by have := sepG 0 8 (by omega) _ _ hSa; rwa [add_ofNat_zero] at this) hEa hEb
    (by rw [r8sp, hGS]; have := hRS.subR (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this)
    (by
      rw [r8sp, hGS, hG]
      have := sep_offsets S (c := 32) (n := 8) (d := 0) (k := 32) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this)
  have hR : bytesResult (memLoad32 M2 self) (memLoad32 M2 (self + 4)) (memLoad32 M2 (self + 8)) 4 =
      bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 := by rw [l2p, l2l, l2e]
  have mem9' : ∀ x, Sep S 32 x 1 → m9.mem x = array4Mem M2 G self x := fun x hx => by
    rw [mem9 x (by rw [r8sp, hGS]; exact hx), hm8]
  have r9sp : reg m9 sp = G := by rw [sp9, r8sp]
  have r9s0 : reg m9 s0 = k := by
    rw [fr9 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8]; simp +decide
  have r9 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s0 → r ≠ sp →
      reg m9 r = reg m r := fun r h0 h1 h2 h3 h4 h5 hra' hs0 hsp' => by
    rw [fr9 r h0 h1 h2 h3 h4 h5, r8]; simp [hra', h0, h1, hs0, hsp']
  have s32 : ∀ x, Sep S 48 x 1 → Sep S 32 x 1 := fun x h => by
    have := h.sub (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this
  have hGin : ∀ c, c < 16 → Sep S 32 (G + BitVec.ofNat 32 c) 1 := fun c hc' => by
    rw [hG]; show Sep S 32 (S + BitVec.ofNat 32 32 + BitVec.ofNat 32 c) 1
    rw [add_ofNat_assoc]
    have := sep_offsets S (c := 0) (n := 32) (d := 32 + c) (k := 1) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have notG : ∀ x, Sep S 48 x 1 → ∀ c, c < 16 → x ≠ G + BitVec.ofNat 32 c := fun x h c hc' e => by
    have := sepG c 1 (by omega) _ _ h
    exact this 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
  have neG : ∀ c, 0 < c → c < 16 → G + BitVec.ofNat 32 c ≠ G := fun c h1 h2 => by
    have := add_ofNat_ne G (c := c) (d := 0) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have codeS : ∀ i, i < readerMagicCode.length → Sep S 48 (base + BitVec.ofNat 32 i) 1 :=
    fun i hi => hSu.subR (c := i) (l := 1) (by omega)
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  have r9ra : reg m9 ra = base + BitVec.ofNat 32 0x14 := by
    rw [fr9 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8]; simp +decide
  have finishRegs : ∀ (n : Machine) (g : Fin 32 → Word),
      (∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → reg n r = g r) → reg n sp = G + 0x10 → reg n ra = reg m ra →
      reg n s0 = reg m s0 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → r ≠ s0 → r ≠ sp →
        g r = reg m r) →
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg n r = reg m r :=
    fun n g hn hsp' hra' hs0' hg r h0 h1 h2 h3 h4 h5 h6 => by
      by_cases e1 : r = sp
      · subst e1; rw [hsp', ← hspG]
      by_cases e2 : r = ra
      · subst e2; exact hra'
      by_cases e3 : r = s0
      · subst e3; exact hs0'
      rw [hn r e1 e2 e3]; exact hg r h0 h1 h2 h3 h4 h5 h6 e2 e3 e1
  have neG1 : ∀ c, 1 < c → c < 16 → G + BitVec.ofNat 32 c ≠ G + 1 := fun c h1 h2 =>
    add_ofNat_ne G (c := c) (d := 1) (by omega) (by omega) (by omega)
  rcases hR1 : bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 with _ | ⟨p, e⟩
  · -- The reader has fewer than 4 bytes left.
    obtain ⟨g0, g1, gx⟩ := array4Mem_none (G := G) (hR.trans hR1)
    have m9x : ∀ x, Sep S 48 x 1 → m9.mem x = m.mem x := fun x h => by
      rw [mem9' x (s32 x h), gx x (by have := notG x h 0 (by omega); rwa [add_ofNat_zero] at this)
        (notG x h 1 (by omega)), M2out x h]
    have hc9 : CodeIn m9.mem base readerMagicCode := fun i hi => by rw [m9x _ (codeS i hi)]; exact hc i hi
    have t9 : St m9.mem base m9 0x14 (reg m9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
    obtain ⟨n1, d1, u1⟩ := t9.lbu hc9 mg_at_14 (off' := 0x18) (by decide)
    have gm0 : m9.mem G = 1 := by
      rw [mem9' G (by have := hGin 0 (by omega); rwa [add_ofNat_zero] at this), g0]
    rw [r9sp, add_lit_zero, gm0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hc9 0x1A mg_at_18 (by decide) rfl
    obtain ⟨n3, d3, u3⟩ := u2.lbu hc9 mg_at_1a (off' := 0x1E) (by decide)
    have gm1 : m9.mem (G + 1) = 0 := by rw [mem9' (G + 1) (hGin 1 (by omega)), g1]
    rw [show upd (reg m9) a0 ((1 : BitVec 8).zeroExtend 32) sp = G by simp +decide [upd, r9sp], gm1] at u3
    obtain ⟨n4, d4, u4⟩ := u3.jump hc9 mg_at_1e (off' := 0x3A) (by decide)
      (by rw [u3.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x3A (by decide)))
    have m9G : ∀ c, 8 ≤ c → c + 4 ≤ 16 → memLoad32 m9.mem (G + BitVec.ofNat 32 c) =
        memLoad32 M2 (G + BitVec.ofNat 32 c) := fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, mem9' _ (hGin (c + j) (by omega)),
        gx _ (neG (c + j) (by omega) (by omega)) (neG1 (c + j) (by omega) (by omega))]
    obtain ⟨n5, c5, pc5, mem5, sp5, ra5, s05, fr5⟩ := mg_epilogue (r0 := reg m ra) (r8 := reg m s0) hc9 u4
      (by simp +decide [upd, r9sp]) hGa
      (by rw [show G + 0x0C = G + BitVec.ofNat 32 0x0C from rfl, m9G 0x0C (by omega) (by omega)]
          exact M2slots.1)
      (by rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, m9G 8 (by omega) (by omega)]
          exact M2slots.2) hret'
    refine ⟨n5, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
      (c9.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 c5)))))))))))), by rw [pc5, hra],
      by rw [sp5, ← hspG], ?_, ?_, ?_⟩
    · rw [fr5 a0 (by decide) (by decide) (by decide)]
      unfold magicResult; rw [hptr, hlen, hR1]; simp +decide [upd]
    · refine finishRegs n5 _ fr5 sp5 ra5 s05 fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0]
        exact r9 r h0 h1 h2 h3 h4 h5 h7 h8 h9
    · intro x hx
      rw [mem5]; unfold magicMem; rw [hptr, hlen, hR1]; exact m9x x hx
  · -- The reader has 4 bytes.
    obtain ⟨g0, g4, gx⟩ := array4Mem_some (G := G) (hR.trans hR1)
    have hR' := hR1
    rw [bytesResult_eq] at hR'
    split at hR'
    case isFalse => cases hR'
    rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨hp1, -⟩ := hR'
    rw [show (4 : Word).toNat = 4 from rfl] at hle
    have hpk : ∀ j, j < 4 → p + BitVec.ofNat 32 j =
        ptr + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + j) := fun j _ => by
      rw [← hp1, ← add_ofNat_assoc, ofNat_toNat_self]
    have bS : ∀ j, j < 4 → Sep S 48 (p + BitVec.ofNat 32 j) 1 := fun j hj => by
      rw [hpk j hj]; exact (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
    have bE : ∀ j, j < 4 → Sep (self + 8) 4 (p + BitVec.ofNat 32 j) 1 := fun j hj => by
      rw [hpk j hj]; exact (hBE.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
    have m9x : ∀ x, Sep S 48 x 1 → m9.mem x = memStore32 m.mem (self + 8) e x := fun x h => by
      rw [mem9' x (s32 x h), gx x (by have := notG x h 0 (by omega); rwa [add_ofNat_zero] at this)
        (show Sep (G + BitVec.ofNat 32 4) 4 x 1 from sepG 4 4 (by omega) _ _ h)]
      exact memStore32_congr (M2out x h)
    have m9b : ∀ j, j < 4 → m9.mem (p + BitVec.ofNat 32 j) = m.mem (p + BitVec.ofNat 32 j) :=
      fun j hj => by rw [m9x _ (bS j hj), memStore32_get_sep (bE j hj)]
    have hc9 : CodeIn m9.mem base readerMagicCode := fun i hi => by
      rw [m9x _ (codeS i hi), memStore32_get_sep (hEu.subR (c := i) (l := 1) (by omega))]; exact hc i hi
    have hcl : CodeIn m9.mem (base + 0x16804) magicLoadCode := fun i hi => by
      rw [m9x _ (hSl.subR (c := i) (l := 1) (by omega)), memStore32_get_sep (hEl.subR (c := i) (l := 1) (by omega))]
      exact hlcode i hi
    have t9 : St m9.mem base m9 0x14 (reg m9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
    obtain ⟨n1, d1, u1⟩ := t9.lbu hc9 mg_at_14 (off' := 0x18) (by decide)
    have gm0 : m9.mem G = 0 := by
      rw [mem9' G (by have := hGin 0 (by omega); rwa [add_ofNat_zero] at this), g0]
    rw [r9sp, add_lit_zero, gm0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.taken hc9 0x20 mg_at_18 (by decide) rfl
    have q2sp : upd (reg m9) a0 ((0 : BitVec 8).zeroExtend 32) sp = G := by simp +decide [upd, r9sp]
    obtain ⟨n3, d3, u3⟩ := u2.lw hc9 mg_at_20 (off' := 0x22) (by decide)
      (by rw [q2sp]; exact aligned_add hGa (k := 4) (by decide))
    have gp : memLoad32 m9.mem (G + 4) = p := by
      rw [← g4]
      apply memLoad32_congr
      intro j hj
      show m9.mem (G + BitVec.ofNat 32 4 + BitVec.ofNat 32 j) = _
      rw [add_ofNat_assoc, mem9' _ (hGin (4 + j) (by omega)),
        show G + 4 + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (4 + j) from add_ofNat_assoc G 4 j]
    rw [q2sp, gp] at u3
    -- 0x22: the load helper.
    obtain ⟨n4, d4, u4⟩ := u3.auipc hc9 mg_at_22 (off' := 0x22 + 4) (by decide)
    obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.call hc9 mg_at_26
    have hevl : (base + 0x16804).toNat % 2 = 0 := even_at base hbase 0x16804 (by decide)
    have hpc5 : n5.pc = base + 0x16804 := by
      rw [pc5]; simp +decide only [upd, ite_true, ite_false]
      rw [show base + BitVec.ofNat 32 0x22 + 0x16000 + 0x7E2 = base + 0x16804 by
        rw [BitVec.add_assoc, BitVec.add_assoc]; rfl, even_clear _ hevl]
    have v5 : St m9.mem (base + 0x16804) n5 0 (reg n5) := ⟨by rw [hpc5]; simp, mem5, fun _ => rfl⟩
    have q5a0 : reg n5 a0 = p := by rw [regs5]; simp +decide [upd]
    have q5t0 : reg n5 t0 = base + BitVec.ofNat 32 0x2A := by
      rw [regs5]; simp +decide only [upd, ite_true, ite_false]
      exact add_ofNat_assoc base (0x22 + 4) 4
    obtain ⟨n6, c6, pc6, mem6, a06, a26, a36, fr6⟩ := magicLoad_correct v5 hcl
    rw [q5a0] at a06 a26 a36
    have u6 : St m9.mem base n6 0x2A (reg n6) :=
      ⟨by rw [pc6, q5t0]; exact even_clear _ (even_at base hbase 0x2A (by decide)), mem6, fun _ => rfl⟩
    obtain ⟨n7, d7, u7⟩ := u6.alu hc9 mg_at_2a (off' := 0x2C) (by decide)
    obtain ⟨n8, d8, u8⟩ := u7.alu hc9 mg_at_2c (off' := 0x2E) (by decide)
    obtain ⟨n9, d9, u9⟩ := u8.alu hc9 mg_at_2e (off' := 0x30) (by decide)
    obtain ⟨n10, d10, u10⟩ := u9.alu hc9 mg_at_30 (off' := 0x34) (by decide)
    obtain ⟨n11, d11, u11⟩ := u10.aluImm hc9 mg_at_34 (off' := 0x36) (by decide)
    obtain ⟨n12, d12, u12⟩ := u11.aluImm hc9 mg_at_36 (off' := 0x3A) (by decide)
    have fr6' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ t0 → reg n6 r = reg m9 r :=
      fun r h0 h1 h2 h3 h4 => by
        rw [fr6 r h0 h1 h2 h3, regs5]
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; simp [upd]; exact t9.zero.symm
        · simp [upd, hr, h4, h0]
    have n6sp : reg n6 sp = G := by
      rw [fr6' sp (by decide) (by decide) (by decide) (by decide) (by decide), r9sp]
    have n6s0 : reg n6 s0 = k := by
      rw [fr6' s0 (by decide) (by decide) (by decide) (by decide) (by decide), r9s0]
    have n6z : reg n6 x0 = 0 := u6.zero
    have val : reg n12 a0 = magicResult m.mem self k := by
      rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]
      rw [n6s0, a06, a26, a36]
      have hv : (((m9.mem p).zeroExtend 32 ||| (m9.mem (p + 1)).zeroExtend 32 <<< 8) |||
          ((m9.mem (p + 2)).zeroExtend 32 <<< 16 ||| (m9.mem (p + 3)).zeroExtend 32 <<< 24)) =
          memLoad32 m.mem p := by
        rw [or_assemble]
        have b0 : m9.mem p = m.mem p := by have := m9b 0 (by omega); rwa [add_ofNat_zero] at this
        rw [b0, show m9.mem (p + 1) = m.mem (p + 1) from m9b 1 (by omega),
          show m9.mem (p + 2) = m.mem (p + 2) from m9b 2 (by omega),
          show m9.mem (p + 3) = m.mem (p + 3) from m9b 3 (by omega)]
        rfl
      show aluEval .or (aluEval .add (aluEval .sltu 0 (aluEval .xor (aluEval .or _ (aluEval .or _ _)) k))
        0xFFFFFFFF) 2 = _
      rw [show aluEval .or ((m9.mem p).zeroExtend 32 ||| (m9.mem (p + 1)).zeroExtend 32 <<< 8)
          (aluEval .or ((m9.mem (p + 2)).zeroExtend 32 <<< 16) ((m9.mem (p + 3)).zeroExtend 32 <<< 24)) =
          memLoad32 m.mem p from hv, magic_compare]
      unfold magicResult; rw [hptr, hlen, hR1]
    have selfG : ∀ c, c < 16 → Sep (self + 8) 4 (G + BitVec.ofNat 32 c) 1 := fun c hc' => by
      rw [hG]; show Sep _ 4 (S + BitVec.ofNat 32 32 + BitVec.ofNat 32 c) 1
      rw [add_ofNat_assoc]
      exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 32 + c) (l := 1) (by omega)
    have m9G : ∀ c, 8 ≤ c → c + 4 ≤ 16 → memLoad32 m9.mem (G + BitVec.ofNat 32 c) =
        memLoad32 M2 (G + BitVec.ofNat 32 c) := fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, mem9' _ (hGin (c + j) (by omega)),
        gx _ (neG (c + j) (by omega) (by omega))
          (show Sep (G + BitVec.ofNat 32 4) 4 _ 1 from
            sep_offsets G (c := 4) (n := 4) (d := c + j) (k := 1) (by omega) (by omega) (by omega)),
        memStore32_get_sep (selfG (c + j) (by omega))]
    have f12sp : reg n12 sp = G := by
      rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; exact n6sp
    obtain ⟨n13, c13, pc13, mem13, sp13, ra13, s013, fr13⟩ := mg_epilogue (r0 := reg m ra) (r8 := reg m s0)
      hc9 u12.self f12sp hGa
      (by rw [show G + 0x0C = G + BitVec.ofNat 32 0x0C from rfl, m9G 0x0C (by omega) (by omega)]
          exact M2slots.1)
      (by rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, m9G 8 (by omega) (by omega)]
          exact M2slots.2) hret'
    refine ⟨n13, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
      (c9.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (c6.trans (.cons d7 (.cons d8
      (.cons d9 (.cons d10 (.cons d11 (.cons d12 c13)))))))))))))))))))), by rw [pc13, hra],
      by rw [sp13, ← hspG], ?_, ?_, ?_⟩
    · rw [fr13 a0 (by decide) (by decide) (by decide)]; exact val
    · refine finishRegs n13 _ fr13 sp13 ra13 s013 fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_
      rw [show reg n12 r = reg n6 r by
        rw [u12.regs]
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; simp [upd]; exact u6.zero.symm
        · simp [upd, hr, h0, h2]]
      rw [fr6' r h0 h1 h2 h3 h6]
      exact r9 r h0 h1 h2 h3 h4 h5 h7 h8 h9
    · intro x hx
      rw [mem13]; unfold magicMem; rw [hptr, hlen, hR1]; exact m9x x hx

end C3.RV32
