import C3BootProofs.Proofs.ReaderArray

/-!
# `c3_verify::reader::Reader::u32`, as compiled

`Reader::u32` calls `Reader::array::<4>` and returns the 4 bytes as a
little-endian `Result<u32, Error>`: a tag byte (0 for `Ok`, 1 for `Err`),
the error byte at offset 1, and the value at offset 4. The compiled function
saves `ra` and `s0` in a 16-byte frame whose base is `array::<4>`'s result
slot. `readerU32_correct` proves it on the RV32 model through
`readerArray4_correct`, which in turn uses `readerBytes_correct`: two levels
of calls, each through the callee's theorem.
-/

namespace C3.RV32

open C3.Image

/-- Memory after `Reader::u32` returns, outside the stack it uses. -/
def u32Mem (M : Word → BitVec 8) (out self : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with
  | none => memStore8 (memStore8 M (out + 1) 0) out 1
  | some (p, e) => memStore8 (memStore32 (memStore32 M (self + 8) e) (out + 4) (memLoad32 M p)) out 0

theorem or_assemble (b0 b1 b2 b3 : BitVec 8) :
    ((b0.zeroExtend 32 ||| b1.zeroExtend 32 <<< 8) ||| (b2.zeroExtend 32 <<< 16 ||| b3.zeroExtend 32 <<< 24))
      = b3 ++ b2 ++ b1 ++ b0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h0 : i < 8
  · simp [h0, hi]; intro h; rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  · have hb0 := BitVec.getLsbD_of_ge b0 i (by omega)
    by_cases h1 : i < 16
    · simp [h0, h1, hi, hb0, show i - 8 < 32 by omega, show i - 8 < 8 by omega]
      intro h; omega
    · have hb1 := BitVec.getLsbD_of_ge b1 (i - 8) (by omega)
      by_cases h2 : i < 24
      · simp [h0, h1, h2, hi, hb0, hb1, show i - 16 < 32 by omega, show i - 8 - 8 < 8 by omega,
          show ¬ i - 8 < 8 by omega]
        simp only [show i - 8 - 8 = i - 16 by omega]
        exact BitVec.getLsbD_eq_getElem (by omega)
      · have hb2 := BitVec.getLsbD_of_ge b2 (i - 16) (by omega)
        simp [h0, h1, h2, hi, hb0, hb1, hb2, show i - 24 < 32 by omega, show ¬ i - 8 < 8 by omega,
          show ¬ i - 8 - 8 < 8 by omega]
        rw [show i - 8 - 8 - 8 = i - 24 by omega]

theorem u32_at_00 : fetchRel readerU32Code 0x00 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem u32_at_02 : fetchRel readerU32Code 0x02 = some (.store .sw sp ra 0x0C, 2) := by decide
theorem u32_at_04 : fetchRel readerU32Code 0x04 = some (.store .sw sp s0 8, 2) := by decide
theorem u32_at_06 : fetchRel readerU32Code 0x06 = some (.alu .add s0 x0 a0, 2) := by decide
theorem u32_at_08 : fetchRel readerU32Code 0x08 = some (.alu .add a0 x0 sp, 2) := by decide
theorem u32_at_0a : fetchRel readerU32Code 0x0A = some (.auipc ra 0, 4) := by decide
theorem u32_at_0e : fetchRel readerU32Code 0x0E = some (.jalr ra ra 0xFFFFFAD4, 4) := by decide
theorem u32_at_12 : fetchRel readerU32Code 0x12 = some (.load .lbu a0 sp 0, 4) := by decide
theorem u32_at_16 : fetchRel readerU32Code 0x16 = some (.branch .beq a0 x0 0x0E, 2) := by decide
theorem u32_at_18 : fetchRel readerU32Code 0x18 = some (.load .lbu a0 sp 1, 4) := by decide
theorem u32_at_1c : fetchRel readerU32Code 0x1C = some (.store .sb s0 a0 1, 4) := by decide
theorem u32_at_20 : fetchRel readerU32Code 0x20 = some (.aluImm .add a0 x0 1, 2) := by decide
theorem u32_at_22 : fetchRel readerU32Code 0x22 = some (.jal x0 0x22, 2) := by decide
theorem u32_at_24 : fetchRel readerU32Code 0x24 = some (.load .lw a1 sp 4, 2) := by decide
theorem u32_at_26 : fetchRel readerU32Code 0x26 = some (.load .lbu a2 a1 1, 4) := by decide
theorem u32_at_2a : fetchRel readerU32Code 0x2A = some (.load .lbu a3 a1 2, 4) := by decide
theorem u32_at_2e : fetchRel readerU32Code 0x2E = some (.load .lbu a4 a1 3, 4) := by decide
theorem u32_at_32 : fetchRel readerU32Code 0x32 = some (.load .lbu a1 a1 0, 4) := by decide
theorem u32_at_36 : fetchRel readerU32Code 0x36 = some (.aluImm .sll a2 a2 8, 2) := by decide
theorem u32_at_38 : fetchRel readerU32Code 0x38 = some (.aluImm .sll a3 a3 0x10, 2) := by decide
theorem u32_at_3a : fetchRel readerU32Code 0x3A = some (.aluImm .sll a4 a4 0x18, 2) := by decide
theorem u32_at_3c : fetchRel readerU32Code 0x3C = some (.alu .or a1 a1 a2, 2) := by decide
theorem u32_at_3e : fetchRel readerU32Code 0x3E = some (.alu .or a3 a3 a4, 2) := by decide
theorem u32_at_40 : fetchRel readerU32Code 0x40 = some (.alu .or a1 a1 a3, 2) := by decide
theorem u32_at_42 : fetchRel readerU32Code 0x42 = some (.store .sw s0 a1 4, 2) := by decide
theorem u32_at_44 : fetchRel readerU32Code 0x44 = some (.store .sb s0 a0 0, 4) := by decide
theorem u32_at_48 : fetchRel readerU32Code 0x48 = some (.load .lw ra sp 0x0C, 2) := by decide
theorem u32_at_4a : fetchRel readerU32Code 0x4A = some (.load .lw s0 sp 8, 2) := by decide
theorem u32_at_4c : fetchRel readerU32Code 0x4C = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem u32_at_4e : fetchRel readerU32Code 0x4E = some (.jalr x0 ra 0, 2) := by decide

theorem array4Mem_none {M : Word → BitVec 8} {G self : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 = none) :
    array4Mem M G self G = 1 ∧ array4Mem M G self (G + 1) = 0 ∧
    ∀ x, x ≠ G → x ≠ G + 1 → array4Mem M G self x = M x := by
  have n10 : G + 1 ≠ G := by
    have := add_ofNat_ne G (c := 1) (d := 0) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  unfold array4Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, by rw [memStore8_ne n10, memStore8_same], fun x h1 h2 => ?_⟩
  rw [memStore8_ne h1, memStore8_ne h2]

theorem array4Mem_some {M : Word → BitVec 8} {G self p e : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 =
      some (p, e)) :
    array4Mem M G self G = 0 ∧ memLoad32 (array4Mem M G self) (G + 4) = p ∧
    ∀ x, x ≠ G → Sep (G + 4) 4 x 1 → array4Mem M G self x = memStore32 M (self + 8) e x := by
  unfold array4Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, ?_, fun x h1 h2 => ?_⟩
  · rw [memLoad32_store8_sep (by
      have := sep_offsets G (c := 0) (n := 1) (d := 4) (k := 4) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this), memLoad32_store32_same]
  · rw [memStore8_ne h1, memStore32_get_sep h2]


theorem ofNat_toNat_self (x : Word) : BitVec.ofNat 32 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

theorem u32_epilogue {m : Machine} {M : Word → BitVec 8} {f : Fin 32 → Word} {base G r0 r8 : Word}
    (hc : CodeIn M base readerU32Code) (t : St M base m 0x48 f) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) (h1 : memLoad32 M (G + 0x0C) = r0) (h2 : memLoad32 M (G + 8) = r8)
    (hret : r0 &&& ~~~1 = r0) :
    ∃ m', Steps m m' ∧ m'.pc = r0 ∧ m'.mem = M ∧ reg m' sp = G + 0x10 ∧ reg m' ra = r0 ∧
      reg m' s0 = r8 ∧ ∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m1, e1, t1⟩ := t.lw hc u32_at_48 (off' := 0x4A) (by decide)
    (by rw [hsp]; exact aligned_add hG (k := 0x0C) (by decide))
  rw [hsp, h1] at t1
  have u1 : upd f ra r0 sp = G := by simp +decide [upd, hsp]
  obtain ⟨m2, e2, t2⟩ := t1.lw hc u32_at_4a (off' := 0x4C) (by decide)
    (by rw [u1]; exact aligned_add hG (k := 8) (by decide))
  rw [u1, h2] at t2
  obtain ⟨m3, e3, t3⟩ := t2.aluImm hc u32_at_4c (off' := 0x4E) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := t3.jalr hc u32_at_4e
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

/-- **The compiled `Reader::u32` is correct.** With its bytes at `base`,
`Reader::array::<4>`'s and `Reader::bytes`'s where the image puts them, a
result address `out` and a reader `self` over a slice that is not null and
doesn't wrap, everything aligned, and the 48 bytes of stack below `sp` (its
frame and `array::<4>`'s), the result, the reader, its position, and its
buffer kept apart as the hypotheses list, there is an execution that
reaches the return address with `sp`, `ra`, and `s0` restored, every
register but `a0` through `a5` unchanged, and memory outside those 48 bytes
exactly as `u32Mem` says: on success, the new position, tag 0, and the 4
bytes at the slice's position as a little-endian word. -/
theorem readerU32_correct (m : Machine) (base retAddr out self : Word)
    (hcode : CodeAt m base readerU32Code)
    (hacode : CodeAt m (base + 0xFFFFFADE) readerArray4Code)
    (hbcode : CodeAt m (base + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = self) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (hout : out.toNat % 4 = 0) (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSu : Sep (reg m sp + 0xFFFFFFD0) 48 base readerU32Code.length)
    (hSa : Sep (reg m sp + 0xFFFFFFD0) 48 (base + 0xFFFFFADE) readerArray4Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFD0) 48 (base + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode.length)
    (hOu : Sep out 8 base readerU32Code.length)
    (hEu : Sep (self + 8) 4 base readerU32Code.length)
    (hEa : Sep (self + 8) 4 (base + 0xFFFFFADE) readerArray4Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFD0) 48)
    (hOS : Sep out 8 (reg m sp + 0xFFFFFFD0) 48)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFD0) 48)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFD0) 48 x 1 → m'.mem x = u32Mem m.mem out self x := by
  have hc : CodeIn m.mem base readerU32Code := hcode
  have s0' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  have hG : reg m sp + 0xFFFFFFF0 = reg m sp + 0xFFFFFFD0 + 32 := by rw [BitVec.add_assoc]; rfl
  have hspG : reg m sp = reg m sp + 0xFFFFFFF0 + 0x10 := by
    rw [BitVec.add_assoc]; exact (BitVec.add_zero _).symm
  obtain ⟨S, hSdef⟩ : ∃ S, reg m sp + 0xFFFFFFD0 = S := ⟨_, rfl⟩
  rw [hSdef] at hSu hSa hSb hRS hOS hBS hG ⊢
  obtain ⟨G, hGdef⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hGdef] at hG hspG
  have hGa : G.toNat % 4 = 0 := hGdef ▸ aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  -- 0x00: allocate the frame
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc u32_at_00 (off' := 0x02) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hGdef] at t1
  have q1 : ∀ r, upd (reg m) sp G r = if r = sp then G else reg m r := by
    intro r
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp +decide [upd, hz]
    · simp [upd, hr]
  have r1sp : upd (reg m) sp G sp = G := by simp [q1]
  have sepG : ∀ c l, c + l ≤ 16 → ∀ (b : Word) (n : Nat), Sep S 48 b n →
      Sep (G + BitVec.ofNat 32 c) l b n := fun c l h b n hs => by
    rw [hG]; show Sep (S + BitVec.ofNat 32 32 + BitVec.ofNat 32 c) l b n
    rw [add_ofNat_assoc]; exact hs.sub (c := 32 + c) (l := l) (by omega)
  -- 0x02, 0x04: save ra and s0
  obtain ⟨m2, e2, t2⟩ := t1.sw hc u32_at_02 (off' := 0x04) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 0x0C) (by decide))
  rw [r1sp, show upd (reg m) sp G ra = reg m ra by simp +decide [q1]] at t2
  have hc2 := hc.store32 (v := reg m ra) (show Sep (G + 0x0C) 4 base _ from sepG 0x0C 4 (by omega) _ _ hSu)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 u32_at_04 (off' := 0x06) (by decide)
    (by rw [r1sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [r1sp, show upd (reg m) sp G s0 = reg m s0 by simp +decide [q1]] at t3
  have hc3 := hc2.store32 (v := reg m s0) (show Sep (G + 8) 4 base _ from sepG 8 4 (by omega) _ _ hSu)
  obtain ⟨m4, e4, t4⟩ := t3.alu hc3 u32_at_06 (off' := 0x08) (by decide)
  obtain ⟨m5, e5, t5⟩ := t4.alu hc3 u32_at_08 (off' := 0x0A) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.auipc hc3 u32_at_0a (off' := 0x0E) (by decide)
  obtain ⟨m7, e7, pc7, mem7, regs7⟩ := t6.call hc3 u32_at_0e
  have hGS : G + 0xFFFFFFE0 = S := by rw [hG, BitVec.add_assoc]; exact BitVec.add_zero S
  have hsum : base + BitVec.ofNat 32 0x0A + 0 + 0xFFFFFAD4 = base + 0xFFFFFADE := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hev : (base + 0xFFFFFADE).toNat % 2 = 0 := by
    rw [BitVec.toNat_add, show (0xFFFFFADE : Word).toNat = 0xFFFFFADE from rfl]; omega
  have hev2 : (base + BitVec.ofNat 32 0x12).toNat % 2 = 0 := even_at base hbase 0x12 (by decide)
  have r7 : ∀ r, reg m7 r = if r = ra then base + BitVec.ofNat 32 0x12 else
      if r = a0 then G else if r = s0 then out else if r = sp then G else reg m r := by
    intro r; rw [regs7, show base + BitVec.ofNat 32 0x0E + 4 = base + BitVec.ofNat 32 0x12 from
      add_ofNat_assoc base 0x0E 4]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp +decide [upd, hz]
    · by_cases h1 : r = ra
      · subst h1; simp +decide [upd]
      by_cases h2 : r = a0
      · subst h2; simp +decide [upd, aluEval]
      by_cases h3 : r = s0
      · subst h3; simp +decide [upd, aluEval, ha0]
      by_cases h4 : r = sp
      · subst h4; simp +decide [upd]
      simp [upd, hr, h1, h2, h3, h4]
  have mem2 : ∀ a, Sep S 48 a 4 →
      memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0)) a =
        memLoad32 m.mem a := fun a h => by
    rw [memLoad32_store32_sep (show Sep (G + 8) 4 a 4 from sepG 8 4 (by omega) _ _ h),
      memLoad32_store32_sep (show Sep (G + 0x0C) 4 a 4 from sepG 0x0C 4 (by omega) _ _ h)]
  have hSself : Sep S 48 self 12 := hRS.symm
  have hcA : CodeIn (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0))
      (base + 0xFFFFFADE) readerArray4Code :=
    ((show CodeIn m.mem _ _ from hacode).store32 (show Sep (G + 0x0C) 4 _ _ from sepG 0x0C 4 (by omega) _ _ hSa)).store32
      (show Sep (G + 8) 4 _ _ from sepG 8 4 (by omega) _ _ hSa)
  have hcB : CodeIn (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0))
      (base + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode :=
    ((show CodeIn m.mem _ _ from hbcode).store32 (show Sep (G + 0x0C) 4 _ _ from sepG 0x0C 4 (by omega) _ _ hSb)).store32
      (show Sep (G + 8) 4 _ _ from sepG 8 4 (by omega) _ _ hSb)
  have r7sp : reg m7 sp = G := by rw [r7]; simp +decide
  have h0self : Sep S 48 self 4 := by
    have := hSself.subR (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have h4self : Sep S 48 (self + 4) 4 := hSself.subR (c := 4) (l := 4) (by omega)
  have hbuf7 : memLoad32 m7.mem self ≠ 0 ∧
      (memLoad32 m7.mem self).toNat + (memLoad32 m7.mem (self + 4)).toNat ≤ 2 ^ 32 := by
    rw [mem7, mem2 self h0self, mem2 (self + 4) h4self]; exact hbuf
  have hS32a : Sep (reg m7 sp + 0xFFFFFFE0) 32 (base + 0xFFFFFADE) readerArray4Code.length := by
    rw [r7sp, hGS]; have := hSa.sub (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this
  have hS32b : Sep (reg m7 sp + 0xFFFFFFE0) 32 (base + 0xFFFFFADE + 0xFFFFFF96)
      readerBytesCode.length := by
    rw [r7sp, hGS]; have := hSb.sub (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this
  have hOa : Sep G 8 (base + 0xFFFFFADE) readerArray4Code.length := by
    have := sepG 0 8 (by omega) _ _ hSa; rwa [add_ofNat_zero] at this
  have hRS32 : Sep self 12 (reg m7 sp + 0xFFFFFFE0) 32 := by
    rw [r7sp, hGS]; have := hRS.subR (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this
  have hGS32 : Sep G 8 (reg m7 sp + 0xFFFFFFE0) 32 := by
    rw [r7sp, hGS, hG]
    have := sep_offsets S (c := 32) (n := 8) (d := 0) (k := 32) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have hpc7 : m7.pc = base + 0xFFFFFADE := by
    rw [pc7]; simp +decide only [upd, ite_true, ite_false]; rw [hsum, even_clear _ hev]
  obtain ⟨m8, c8, pc8, sp8, fr8, mem8⟩ := readerArray4_correct m7 (base + 0xFFFFFADE)
    (base + 0xFFFFFADE + 0xFFFFFF96) (base + BitVec.ofNat 32 0x12) G self
    (fun i hi => by rw [mem7]; exact hcA i hi) (fun i hi => by rw [mem7]; exact hcB i hi) rfl hev
    hpc7 (by rw [r7]; simp +decide) (by rw [r7]; simp +decide [ha1]) (by rw [r7]; simp +decide)
    (even_clear _ hev2) (by rw [r7sp]; exact hGa) hGa hself hbuf7 hS32a hS32b hOa hEa hEb hRS32 hGS32
  have mem8' : ∀ x, Sep S 32 x 1 →
      m8.mem x = array4Mem (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0))
        G self x := fun x hx => by
    rw [mem8 x (by rw [r7sp, hGS]; exact hx), mem7]
  have r8sp : reg m8 sp = G := by rw [sp8, r7sp]
  have r8s0 : reg m8 s0 = out := by
    rw [fr8 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r7]; simp +decide
  have r8 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ s0 → r ≠ sp →
      reg m8 r = reg m r := fun r h0 h1 h2 h3 h4 h5 hra' hs0 hsp' => by
    rw [fr8 r h0 h1 h2 h3 h4 h5, r7]; simp [hra', h0, hs0, hsp']
  have h8self : Sep S 48 (self + 8) 4 := hSself.subR (c := 8) (l := 4) (by omega)
  have hRe : bytesResult
      (memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0)) self)
      (memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0)) (self + 4))
      (memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0)) (self + 8)) 4 =
      bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 4 := by
    rw [mem2 self h0self, mem2 (self + 4) h4self, mem2 (self + 8) h8self]
  have s32 : ∀ x, Sep S 48 x 1 → Sep S 32 x 1 := fun x h => by
    have := h.sub (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this
  have notG : ∀ x, Sep S 48 x 1 → ∀ k, k < 16 → x ≠ G + BitVec.ofNat 32 k := fun x h k hk e => by
    have := sepG k 1 (by omega) _ _ h
    exact this 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
  have sepG4 : ∀ x, Sep S 48 x 1 → Sep (G + 4) 4 x 1 := fun x h =>
    show Sep (G + BitVec.ofNat 32 4) 4 x 1 from sepG 4 4 (by omega) _ _ h
  have hGin : ∀ k, k < 16 → Sep S 32 (G + BitVec.ofNat 32 k) 1 := fun k hk => by
    rw [hG]; show Sep S 32 (S + BitVec.ofNat 32 32 + BitVec.ofNat 32 k) 1
    rw [add_ofNat_assoc]
    have := sep_offsets S (c := 0) (n := 32) (d := 32 + k) (k := 1) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have hc8 : ∀ (M3 : Word → BitVec 8), (∀ i, i < readerU32Code.length →
      M3 (base + BitVec.ofNat 32 i) = m.mem (base + BitVec.ofNat 32 i)) →
      CodeIn M3 base readerU32Code := fun M3 h i hi => by rw [h i hi]; exact hc i hi
  have codeS : ∀ i, i < readerU32Code.length → Sep S 48 (base + BitVec.ofNat 32 i) 1 :=
    fun i hi => hSu.subR (c := i) (l := 1) (by omega)
  have M2out : ∀ x, Sep S 48 x 1 →
      memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0) x = m.mem x :=
    fun x h => by
      rw [memStore32_get_sep (show Sep (G + 8) 4 x 1 from sepG 8 4 (by omega) _ _ h),
        memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from sepG 0x0C 4 (by omega) _ _ h)]
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  have slotsM2 : memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0))
        (G + 0x0C) = reg m ra ∧
      memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0)) (G + 8) =
        reg m s0 := by
    refine ⟨?_, memLoad32_store32_same _ _ _⟩
    rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x0C) 4 from
        sep_offsets G (c := 8) (n := 4) (d := 0x0C) (k := 4) (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  have r8ra : reg m8 ra = base + BitVec.ofNat 32 0x12 := by
    rw [fr8 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r7]; simp +decide
  rcases hR : bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4))
    (memLoad32 m.mem (self + 8)) 4 with _ | ⟨p, e⟩
  · obtain ⟨g0, g1, gx⟩ := array4Mem_none (G := G) (hRe.trans hR)
    have m8x : ∀ x, Sep S 48 x 1 → m8.mem x = m.mem x := fun x h => by
      rw [mem8' x (s32 x h), gx x (by have := notG x h 0 (by omega); rwa [add_ofNat_zero] at this)
        (notG x h 1 (by omega)), M2out x h]
    have hc8' : CodeIn m8.mem base readerU32Code := hc8 _ fun i hi => m8x _ (codeS i hi)
    have t8 : St m8.mem base m8 0x12 (reg m8) :=
      ⟨by rw [pc8], rfl, fun _ => rfl⟩
    have neG : ∀ k, 0 < k → k < 16 → G + BitVec.ofNat 32 k ≠ G := fun k h1 h2 => by
      have := add_ofNat_ne G (c := k) (d := 0) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have neG1 : ∀ k, 1 < k → k < 16 → G + BitVec.ofNat 32 k ≠ G + 1 := fun k h1 h2 =>
      add_ofNat_ne G (c := k) (d := 1) (by omega) (by omega) (by omega)
    have m8G : ∀ c, 8 ≤ c → c + 4 ≤ 16 → memLoad32 m8.mem (G + BitVec.ofNat 32 c) =
        memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0))
          (G + BitVec.ofNat 32 c) := fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, mem8' _ (hGin (c + j) (by omega)),
        gx _ (neG (c + j) (by omega) (by omega)) (neG1 (c + j) (by omega) (by omega))]
    have outG : ∀ o, o < 8 → ∀ c, c + 4 ≤ 16 → Sep (out + BitVec.ofNat 32 o) 1 (G + BitVec.ofNat 32 c) 4 :=
      fun o ho c hc => by
        rw [hG]; show Sep _ 1 (S + BitVec.ofNat 32 32 + BitVec.ofNat 32 c) 4
        rw [add_ofNat_assoc]
        exact (hOS.sub (c := o) (l := 1) (by omega)).subR (c := 32 + c) (l := 4) (by omega)
    have hz8 := t8.zero
    obtain ⟨n1, d1, u1⟩ := t8.lbu hc8' u32_at_12 (off' := 0x16) (by decide)
    have gm0 : m8.mem G = 1 := by
      rw [mem8' G (by have := hGin 0 (by omega); rwa [add_ofNat_zero] at this), g0]
    rw [r8sp, add_lit_zero, gm0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hc8' 0x18 u32_at_16 (by decide) rfl
    obtain ⟨n3, d3, u3⟩ := u2.lbu hc8' u32_at_18 (off' := 0x1C) (by decide)
    have gm1 : m8.mem (G + 1) = 0 := by rw [mem8' (G + 1) (hGin 1 (by omega)), g1]
    rw [show upd (reg m8) a0 ((1 : BitVec 8).zeroExtend 32) sp = G from by simp +decide [upd, r8sp],
      gm1] at u3
    obtain ⟨n4, d4, u4⟩ := u3.sb hc8' u32_at_1c (off' := 0x20) (by decide)
    rw [show upd (upd (reg m8) a0 ((1 : BitVec 8).zeroExtend 32)) a0 ((0 : BitVec 8).zeroExtend 32) s0
        = out from by simp +decide [upd, r8s0],
      show (upd (upd (reg m8) a0 ((1 : BitVec 8).zeroExtend 32)) a0 ((0 : BitVec 8).zeroExtend 32)
        a0).extractLsb' 0 8 = 0 from by simp +decide [upd]] at u4
    have hc9 := hc8'.store8 (a := out + 1) (v := 0)
      (show Sep (out + 1) 1 base _ from hOu.sub (c := 1) (l := 1) (by omega))
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hc9 u32_at_20 (off' := 0x22) (by decide)
    obtain ⟨n6, d6, u6⟩ := u5.jump hc9 u32_at_22 (off' := 0x44) (by decide)
      (by rw [u5.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x44 (by decide)))
    obtain ⟨n7, d7, u7⟩ := u6.sb hc9 u32_at_44 (off' := 0x48) (by decide)
    rw [show upd (upd (upd (reg m8) a0 ((1 : BitVec 8).zeroExtend 32)) a0
        ((0 : BitVec 8).zeroExtend 32)) a0 (aluEval .add (upd (upd (reg m8) a0
        ((1 : BitVec 8).zeroExtend 32)) a0 ((0 : BitVec 8).zeroExtend 32) x0) 1) s0 = out from by
        simp +decide [upd, r8s0],
      show (upd (upd (upd (reg m8) a0 ((1 : BitVec 8).zeroExtend 32)) a0
        ((0 : BitVec 8).zeroExtend 32)) a0 (aluEval .add (upd (upd (reg m8) a0
        ((1 : BitVec 8).zeroExtend 32)) a0 ((0 : BitVec 8).zeroExtend 32) x0) 1) a0).extractLsb' 0 8
          = 1 from by simp +decide [upd, aluEval],
      add_lit_zero] at u7
    have hc10 := hc9.store8 (a := out) (v := 1)
      (by have := hOu.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this)
    have ldG : ∀ c, 8 ≤ c → c + 4 ≤ 16 →
        memLoad32 (memStore8 (memStore8 m8.mem (out + 1) 0) out 1) (G + BitVec.ofNat 32 c) =
        memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0))
          (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
      rw [memLoad32_store8_sep (by have := outG 0 (by omega) c (by omega); rwa [add_ofNat_zero] at this),
        memLoad32_store8_sep (show Sep (out + 1) 1 _ 4 from outG 1 (by omega) c (by omega)), m8G c h1 h2]
    obtain ⟨n8, c8', pc8', mem8'', sp8', ra8', s08', fr8'⟩ := u32_epilogue (r0 := reg m ra)
      (r8 := reg m s0) hc10 u7 (by simp +decide [upd, r8sp]) hGa
      (by rw [show G + 0x0C = G + BitVec.ofNat 32 0x0C from rfl, ldG 0x0C (by omega) (by omega)]
          exact slotsM2.1)
      (by rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, ldG 8 (by omega) (by omega)]
          exact slotsM2.2)
      hret'
    refine ⟨n8, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 ((Steps.cons e7 c8).trans
      (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c8'))))))))))))),
      by rw [pc8', hra], by rw [sp8', ← hspG], ?_, ?_⟩
    · intro r r0 r1 r2 r3 r4 r5
      by_cases hsp' : r = sp
      · subst hsp'; rw [sp8', ← hspG]
      by_cases hra' : r = ra
      · subst hra'; exact ra8'
      by_cases hs0 : r = s0
      · subst hs0; exact s08'
      rw [fr8' r hsp' hra' hs0]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp; rfl
      · simp [upd, hr, r0]
        exact r8 r r0 r1 r2 r3 r4 r5 hra' hs0 hsp'
    · intro x hx
      rw [mem8'']
      unfold u32Mem
      rw [hR]
      dsimp only
      apply memStore8_congr
      apply memStore8_congr
      exact m8x x hx
  · obtain ⟨g0, g4, gx⟩ := array4Mem_some (G := G) (hRe.trans hR)
    have hR' := hR
    rw [bytesResult_eq] at hR'
    split at hR'
    case isFalse => cases hR'
    rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at hR'
    obtain ⟨hp1, -⟩ := hR'
    rw [show (4 : Word).toNat = 4 from rfl] at hle
    have hpk : ∀ k, k < 4 → p + BitVec.ofNat 32 k =
        memLoad32 m.mem self + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + k) := fun k _ => by
      rw [← hp1, ← add_ofNat_assoc, ofNat_toNat_self]
    have bS : ∀ k, k < 4 → Sep S 48 (p + BitVec.ofNat 32 k) 1 := fun k hk => by
      rw [hpk k hk]; exact (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + k) (l := 1) (by omega)).symm
    have bE : ∀ k, k < 4 → Sep (self + 8) 4 (p + BitVec.ofNat 32 k) 1 := fun k hk => by
      rw [hpk k hk]; exact (hBE.sub (c := (memLoad32 m.mem (self + 8)).toNat + k) (l := 1) (by omega)).symm
    have m8x : ∀ x, Sep S 48 x 1 → m8.mem x = memStore32 m.mem (self + 8) e x := fun x h => by
      rw [mem8' x (s32 x h), gx x (by have := notG x h 0 (by omega); rwa [add_ofNat_zero] at this)
        (sepG4 x h)]
      exact memStore32_congr (M2out x h)
    have m8b : ∀ k, k < 4 → m8.mem (p + BitVec.ofNat 32 k) = m.mem (p + BitVec.ofNat 32 k) :=
      fun k hk => by rw [m8x _ (bS k hk), memStore32_get_sep (bE k hk)]
    have hc8' : CodeIn m8.mem base readerU32Code := hc8 _ fun i hi => by
      rw [m8x _ (codeS i hi), memStore32_get_sep (hEu.subR (c := i) (l := 1) (by omega))]
    have t8 : St m8.mem base m8 0x12 (reg m8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
    have hz8 := t8.zero
    obtain ⟨n1, d1, u1⟩ := t8.lbu hc8' u32_at_12 (off' := 0x16) (by decide)
    have gm0 : m8.mem G = 0 := by
      rw [mem8' G (by have := hGin 0 (by omega); rwa [add_ofNat_zero] at this), g0]
    rw [r8sp, add_lit_zero, gm0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.taken hc8' 0x24 u32_at_16 (by decide) rfl
    obtain ⟨n3, d3, u3⟩ := u2.lw hc8' u32_at_24 (off' := 0x26) (by decide)
      (by simp +decide only [upd, r8sp, ite_false]; exact aligned_add hGa (k := 4) (by decide))
    have gp : memLoad32 m8.mem (G + 4) = p := by
      rw [← g4]
      apply memLoad32_congr
      intro j hj
      show m8.mem (G + BitVec.ofNat 32 4 + BitVec.ofNat 32 j) = _
      rw [add_ofNat_assoc, mem8' _ (hGin (4 + j) (by omega)),
        show G + 4 + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (4 + j) from add_ofNat_assoc G 4 j]
    rw [show upd (reg m8) a0 ((0 : BitVec 8).zeroExtend 32) sp = G from by simp +decide [upd, r8sp],
      gp] at u3
    have v3 : ∀ r, reg n3 r = upd (upd (reg m8) a0 ((0 : BitVec 8).zeroExtend 32)) a1 p r := u3.regs
    have q3a1 : reg n3 a1 = p := by rw [v3]; simp +decide [upd]
    have b1 : m8.mem (p + 1) = m.mem (p + 1) := m8b 1 (by omega)
    have b2 : m8.mem (p + 2) = m.mem (p + 2) := m8b 2 (by omega)
    have b3 : m8.mem (p + 3) = m.mem (p + 3) := m8b 3 (by omega)
    have b0 : m8.mem p = m.mem p := by have := m8b 0 (by omega); rwa [add_ofNat_zero] at this
    obtain ⟨n4, d4, u4⟩ := u3.self.lbu hc8' u32_at_26 (off' := 0x2A) (by decide)
    rw [q3a1, b1] at u4
    obtain ⟨n5, d5, u5⟩ := u4.self.lbu hc8' u32_at_2a (off' := 0x2E) (by decide)
    have q4a1 : reg n4 a1 = p := by rw [u4.regs]; simp +decide [upd, q3a1]
    rw [q4a1, b2] at u5
    obtain ⟨n6, d6, u6⟩ := u5.self.lbu hc8' u32_at_2e (off' := 0x32) (by decide)
    have q5a1 : reg n5 a1 = p := by rw [u5.regs]; simp +decide [upd, q4a1]
    rw [q5a1, b3] at u6
    obtain ⟨n7, d7, u7⟩ := u6.self.lbu hc8' u32_at_32 (off' := 0x36) (by decide)
    have q6a1 : reg n6 a1 = p := by rw [u6.regs]; simp +decide [upd, q5a1]
    rw [q6a1, add_lit_zero, b0] at u7
    obtain ⟨n8', d8, u8⟩ := u7.self.aluImm hc8' u32_at_36 (off' := 0x38) (by decide)
    obtain ⟨n9, d9, u9⟩ := u8.aluImm hc8' u32_at_38 (off' := 0x3A) (by decide)
    obtain ⟨n10, d10, u10⟩ := u9.aluImm hc8' u32_at_3a (off' := 0x3C) (by decide)
    obtain ⟨n11, d11, u11⟩ := u10.alu hc8' u32_at_3c (off' := 0x3E) (by decide)
    obtain ⟨n12, d12, u12⟩ := u11.alu hc8' u32_at_3e (off' := 0x40) (by decide)
    obtain ⟨n13, d13, u13⟩ := u12.alu hc8' u32_at_40 (off' := 0x42) (by decide)
    have r7a2 : reg n7 a2 = (m.mem (p + 1)).zeroExtend 32 := by
      rw [u7.regs]; simp +decide only [upd, ite_false]; rw [u6.regs]; simp +decide only [upd, ite_false]; rw [u5.regs]; simp +decide only [upd, ite_false]
      rw [u4.regs]; simp +decide only [upd, ite_true, ite_false]
    have r7a3 : reg n7 a3 = (m.mem (p + 2)).zeroExtend 32 := by
      rw [u7.regs]; simp +decide only [upd, ite_false]; rw [u6.regs]; simp +decide only [upd, ite_false]; rw [u5.regs]; simp +decide only [upd, ite_true, ite_false]
    have r7a4 : reg n7 a4 = (m.mem (p + 3)).zeroExtend 32 := by
      rw [u7.regs]; simp +decide only [upd, ite_false]; rw [u6.regs]; simp +decide only [upd, ite_true, ite_false]
    have r7a1 : reg n7 a1 = (m.mem p).zeroExtend 32 := by rw [u7.regs]; simp +decide [upd]
    have val : reg n13 a1 = memLoad32 m.mem p := by
      rw [u13.regs]
      simp +decide only [upd, ite_true, ite_false]
      rw [r7a1, r7a2, r7a3, r7a4]
      exact or_assemble _ _ _ _
    have k : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n13 r = reg n3 r :=
      fun r h1 h2 h3 h4 => by
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; rfl
        · rw [u13.regs]; simp [upd, hr, h1, h2, h3, h4]
          rw [u7.regs]; simp [upd, hr, h1]
          rw [u6.regs]; simp [upd, hr, h4]
          rw [u5.regs]; simp [upd, hr, h3]
          rw [u4.regs]; simp [upd, hr, h2]
    have n13s0 : reg n13 s0 = out := by
      rw [k s0 (by decide) (by decide) (by decide) (by decide), v3]; simp +decide [upd, r8s0]
    have n13sp : reg n13 sp = G := by
      rw [k sp (by decide) (by decide) (by decide) (by decide), v3]; simp +decide [upd, r8sp]
    have n13a0 : reg n13 a0 = (0 : BitVec 8).zeroExtend 32 := by
      rw [k a0 (by decide) (by decide) (by decide) (by decide), v3]; simp +decide [upd]
    obtain ⟨n14, d14, u14⟩ := u13.self.sw hc8' u32_at_42 (off' := 0x44) (by decide)
      (by rw [n13s0]; exact aligned_add hout (k := 4) (by decide))
    rw [n13s0, val] at u14
    have hc9 := hc8'.store32 (a := out + 4) (v := memLoad32 m.mem p)
      (show Sep (out + 4) 4 base _ from hOu.sub (c := 4) (l := 4) (by omega))
    obtain ⟨n15, d15, u15⟩ := u14.sb hc9 u32_at_44 (off' := 0x48) (by decide)
    rw [n13s0, n13a0, add_lit_zero,
      show ((0 : BitVec 8).zeroExtend 32 : Word).extractLsb' 0 8 = 0 from by decide] at u15
    have hc10 := hc9.store8 (a := out) (v := 0)
      (by have := hOu.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this)
    have outG : ∀ o l, o + l ≤ 8 → ∀ c, c + 4 ≤ 16 →
        Sep (out + BitVec.ofNat 32 o) l (G + BitVec.ofNat 32 c) 4 := fun o l hol c hc => by
      rw [hG]; show Sep _ l (S + BitVec.ofNat 32 32 + BitVec.ofNat 32 c) 4
      rw [add_ofNat_assoc]
      exact (hOS.sub (c := o) (l := l) hol).subR (c := 32 + c) (l := 4) (by omega)
    have selfG : ∀ c, c + 4 ≤ 16 → Sep (self + 8) 4 (G + BitVec.ofNat 32 c) 4 := fun c hc => by
      rw [hG]; show Sep _ 4 (S + BitVec.ofNat 32 32 + BitVec.ofNat 32 c) 4
      rw [add_ofNat_assoc]
      exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 32 + c) (l := 4) (by omega)
    have m8G : ∀ c, 8 ≤ c → c + 4 ≤ 16 → memLoad32 m8.mem (G + BitVec.ofNat 32 c) =
        memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0))
          (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
      rw [← memLoad32_store32_sep
        (M := memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0)) (v := e)
        (selfG c (by omega))]
      apply memLoad32_congr
      intro j hj
      rw [add_ofNat_assoc, mem8' _ (hGin (c + j) (by omega))]
      apply gx
      · have := add_ofNat_ne G (c := c + j) (d := 0) (by omega) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      · show Sep (G + BitVec.ofNat 32 4) 4 _ 1
        exact sep_offsets G (c := 4) (n := 4) (d := c + j) (k := 1) (by omega) (by omega) (by omega)
    have ldG : ∀ c, 8 ≤ c → c + 4 ≤ 16 →
        memLoad32 (memStore8 (memStore32 m8.mem (out + 4) (memLoad32 m.mem p)) out 0)
          (G + BitVec.ofNat 32 c) =
        memLoad32 (memStore32 (memStore32 m.mem (G + 0x0C) (reg m ra)) (G + 8) (reg m s0))
          (G + BitVec.ofNat 32 c) := fun c h1 h2 => by
      rw [memLoad32_store8_sep (by have := outG 0 1 (by omega) c (by omega); rwa [add_ofNat_zero] at this),
        memLoad32_store32_sep (show Sep (out + 4) 4 _ 4 from outG 4 4 (by omega) c (by omega)),
        m8G c h1 h2]
    obtain ⟨n16, c16, pc16, mem16, sp16, ra16, s016, fr16⟩ := u32_epilogue (r0 := reg m ra)
      (r8 := reg m s0) hc10 u15 n13sp hGa
      (by rw [show G + 0x0C = G + BitVec.ofNat 32 0x0C from rfl, ldG 0x0C (by omega) (by omega)]
          exact slotsM2.1)
      (by rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, ldG 8 (by omega) (by omega)]
          exact slotsM2.2)
      hret'
    refine ⟨n16, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 ((Steps.cons e7 c8).trans
      (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 c16))))))))))))))))))))),
      by rw [pc16, hra], by rw [sp16, ← hspG], ?_, ?_⟩
    · intro r r0 r1 r2 r3 r4 r5
      by_cases hsp' : r = sp
      · subst hsp'; rw [sp16, ← hspG]
      by_cases hra' : r = ra
      · subst hra'; exact ra16
      by_cases hs0 : r = s0
      · subst hs0; exact s016
      rw [fr16 r hsp' hra' hs0, k r r1 r2 r3 r4, v3]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp; rfl
      · simp [upd, hr, r0, r1]
        exact r8 r r0 r1 r2 r3 r4 r5 hra' hs0 hsp'
    · intro x hx
      rw [mem16]
      unfold u32Mem
      rw [hR]
      dsimp only
      apply memStore8_congr
      apply memStore32_congr
      exact m8x x hx

end C3.RV32
