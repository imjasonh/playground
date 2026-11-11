import C3BootProofs.Proofs.Outlined

/-!
# `c3_verify::manifest::part`, as compiled

`part(r, min, max)` reads two little-endian `u32`s, an offset and a length,
with `Reader::u32`, and fails with `Error::OutOfRange` (5) unless
`min ≤ length ≤ max`. It returns `Result<Part, Error>` through `a0`: a tag
byte (0 for `Ok`, 1 for `Err`), the error byte at offset 1, and the offset
and length at offsets 4 and 8. The compiled function saves `ra` and `s0`
through `s3` with a machine-outlined save helper, saves `s4` itself, and
restores all six with an outlined restore helper. `manifestPart_correct` proves it on the
RV32 model with both `Reader::u32` calls through `readerU32_correct`.
-/

namespace C3.RV32

open C3.ImageV0

/-- The span of code that `part` runs: from `Reader::bytes`, the lowest of
the functions it reaches, to the end of the save helper `part` calls, the
highest, relative to `part`'s address. -/
abbrev partWindow (base : Word) : Word := base + 0xFFFFC3C0

abbrev partWindowLen : Nat := 0x16802

/-- What `part`'s save helper stores, and where in the frame. -/
abbrev partSavePs : List (Fin 32 × Word) := [(ra, 0x1C), (s0, 0x18), (s1, 0x14), (s2, 0x10), (s3, 0x0C)]

/-- What `part`'s restore helper loads, and from where in the frame. -/
abbrev partRestorePs : List (Fin 32 × Word) :=
  [(ra, 0x1C), (s0, 0x18), (s1, 0x14), (s2, 0x10), (s3, 0x0C), (s4, 8)]

/-- Registers after `part`'s restore helper. -/
abbrev partRestored (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) : Fin 32 → Word :=
  restoreRegs M G f partRestorePs

theorem partSave_shape : SaveAt partSaveCode 0 partSavePs := by simp only [SaveAt]; decide

theorem partRestore_shape : RestoreAt partRestoreCode 0 partRestorePs := by simp only [RestoreAt]; decide

/-- Memory after `part` returns, outside the stack it uses. -/
def partMem (M : Word → BitVec 8) (out self lo hi : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with
  | none => memStore8 (memStore8 M (out + 1) 0) out 1
  | some (p1, e1) =>
    match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) e1 4 with
    | none => memStore8 (memStore8 (memStore32 M (self + 8) e1) (out + 1) 0) out 1
    | some (p2, e2) =>
      if (memLoad32 M p2).ult lo || hi.ult (memLoad32 M p2) then
        memStore8 (memStore8 (memStore32 M (self + 8) e2) (out + 1) 5) out 1
      else
        memStore8 (memStore32 (memStore32 (memStore32 M (self + 8) e2) (out + 4) (memLoad32 M p1))
          (out + 8) (memLoad32 M p2)) out 0

theorem part_at_00 : fetchRel manifestPartCode 0x00 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem part_at_02 : fetchRel manifestPartCode 0x02 = some (.auipc t0 0x13000, 4) := by decide
theorem part_at_06 : fetchRel manifestPartCode (0x02 + 4) = some (.jalr t0 t0 0xFFFFFBB4, 4) := by decide
theorem part_at_0a : fetchRel manifestPartCode 0x0A = some (.store .sw sp s4 8, 2) := by decide
theorem part_at_0c : fetchRel manifestPartCode 0x0C = some (.alu .add s2 x0 a3, 2) := by decide
theorem part_at_0e : fetchRel manifestPartCode 0x0E = some (.alu .add s3 x0 a2, 2) := by decide
theorem part_at_10 : fetchRel manifestPartCode 0x10 = some (.alu .add s1 x0 a1, 2) := by decide
theorem part_at_12 : fetchRel manifestPartCode 0x12 = some (.alu .add s0 x0 a0, 2) := by decide
theorem part_at_14 : fetchRel manifestPartCode 0x14 = some (.alu .add a0 x0 sp, 2) := by decide
theorem part_at_16 : fetchRel manifestPartCode 0x16 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem part_at_1a : fetchRel manifestPartCode (0x16 + 4) = some (.jalr ra ra 0xFFFFF936, 4) := by decide
theorem part_at_1e : fetchRel manifestPartCode 0x1E = some (.load .lbu a0 sp 0, 4) := by decide
theorem part_at_22 : fetchRel manifestPartCode 0x22 = some (.branch .bne a0 x0 0x16, 2) := by decide
theorem part_at_24 : fetchRel manifestPartCode 0x24 = some (.load .lw s4 sp 4, 2) := by decide
theorem part_at_26 : fetchRel manifestPartCode 0x26 = some (.alu .add a0 x0 sp, 2) := by decide
theorem part_at_28 : fetchRel manifestPartCode 0x28 = some (.alu .add a1 x0 s1, 2) := by decide
theorem part_at_2a : fetchRel manifestPartCode 0x2A = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem part_at_2e : fetchRel manifestPartCode (0x2A + 4) = some (.jalr ra ra 0xFFFFF922, 4) := by decide
theorem part_at_32 : fetchRel manifestPartCode 0x32 = some (.load .lbu a0 sp 0, 4) := by decide
theorem part_at_36 : fetchRel manifestPartCode 0x36 = some (.branch .beq a0 x0 0x1C, 2) := by decide
theorem part_at_38 : fetchRel manifestPartCode 0x38 = some (.load .lbu a0 sp 1, 4) := by decide
theorem part_at_3c : fetchRel manifestPartCode 0x3C = some (.store .sb s0 a0 1, 4) := by decide
theorem part_at_40 : fetchRel manifestPartCode 0x40 = some (.aluImm .add a0 x0 1, 2) := by decide
theorem part_at_42 : fetchRel manifestPartCode 0x42 = some (.store .sb s0 a0 0, 4) := by decide
theorem part_at_46 : fetchRel manifestPartCode 0x46 = some (.auipc t0 0x13000, 4) := by decide
theorem part_at_4a : fetchRel manifestPartCode (0x46 + 4) = some (.jalr t0 t0 0xFFFFF9AE, 4) := by decide
theorem part_at_4e : fetchRel manifestPartCode (0x46 + 8) = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem part_at_50 : fetchRel manifestPartCode 0x50 = some (.jalr x0 ra 0, 2) := by decide
theorem part_at_52 : fetchRel manifestPartCode 0x52 = some (.load .lw a1 sp 4, 2) := by decide
theorem part_at_54 : fetchRel manifestPartCode 0x54 = some (.branch .bltu a1 s3 0x12, 4) := by decide
theorem part_at_58 : fetchRel manifestPartCode 0x58 = some (.branch .bltu s2 a1 0x0E, 4) := by decide
theorem part_at_5c : fetchRel manifestPartCode 0x5C = some (.aluImm .add a0 x0 0, 2) := by decide
theorem part_at_5e : fetchRel manifestPartCode 0x5E = some (.store .sw s0 s4 4, 4) := by decide
theorem part_at_62 : fetchRel manifestPartCode 0x62 = some (.store .sw s0 a1 8, 2) := by decide
theorem part_at_64 : fetchRel manifestPartCode 0x64 = some (.jal x0 0xFFFFFFDE, 2) := by decide
theorem part_at_66 : fetchRel manifestPartCode 0x66 = some (.aluImm .add a0 x0 5, 2) := by decide
theorem part_at_68 : fetchRel manifestPartCode 0x68 = some (.jal x0 0xFFFFFFD4, 2) := by decide

theorem memStore32_overwrite (M : Word → BitVec 8) (a v w x : Word) :
    memStore32 (memStore32 M a v) a w x = memStore32 M a w x := by
  simp only [memStore32, memStore8]
  by_cases h3 : x = a + 3
  · simp [h3]
  by_cases h2 : x = a + 2
  · simp [h2]
  by_cases h1 : x = a + 1
  · simp [h1]
  by_cases h0 : x = a
  · simp [h0]
  simp only [h3, h2, h1, h0, ite_false]

/-- A call from `part` to `Reader::u32` with `auipc ra, imm; jalr ra, o(ra)`
at offset `off`, through `readerU32_correct`: the result goes to the frame
at `G` and the call uses the 48 bytes below it. -/
theorem part_call_u32 {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} {G self : Word} (s : St M base m off f) (hc : CodeIn M base manifestPartCode)
    {imm o : Word} (h1 : fetchRel manifestPartCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestPartCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = base + 0xFFFFC94C)
    (hl : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hbase : base.toNat % 2 = 0)
    (hu : CodeIn M (base + 0xFFFFC94C) readerU32Code)
    (ha : CodeIn M (base + 0xFFFFC94C + 0xFFFFFADE) readerArray4Code)
    (hbb : CodeIn M (base + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode)
    (hsp : f sp = G) (ha0 : f a0 = G) (ha1 : f a1 = self)
    (hG : G.toNat % 4 = 0) (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 M self ≠ 0 ∧ (memLoad32 M self).toNat + (memLoad32 M (self + 4)).toNat ≤ 2 ^ 32)
    (hSu : Sep (G + 0xFFFFFFD0) 48 (base + 0xFFFFC94C) readerU32Code.length)
    (hSa : Sep (G + 0xFFFFFFD0) 48 (base + 0xFFFFC94C + 0xFFFFFADE) readerArray4Code.length)
    (hSb : Sep (G + 0xFFFFFFD0) 48 (base + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode.length)
    (hOu : Sep G 8 (base + 0xFFFFC94C) readerU32Code.length)
    (hEu : Sep (self + 8) 4 (base + 0xFFFFC94C) readerU32Code.length)
    (hEa : Sep (self + 8) 4 (base + 0xFFFFC94C + 0xFFFFFADE) readerArray4Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode.length)
    (hRS : Sep self 12 (G + 0xFFFFFFD0) 48)
    (hBS : Sep (memLoad32 M self) (memLoad32 M (self + 4)).toNat (G + 0xFFFFFFD0) 48)
    (hBE : Sep (memLoad32 M self) (memLoad32 M (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ St m'.mem base m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' ra = base + BitVec.ofNat 32 (off + 8) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (G + 0xFFFFFFD0) 48 x 1 → m'.mem x = u32Mem M G self x := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  have r2 : ∀ r, r ≠ ra → reg m2 r = f r := fun r h => by
    rw [regs2]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [hz]
    · simp [upd, hr, h]
  have r2ra : reg m2 ra = base + BitVec.ofNat 32 (off + 8) := by rw [regs2, hL]; simp +decide [upd]
  have hev : (base + 0xFFFFC94C).toNat % 2 = 0 := even_at base hbase 0xFFFFC94C (by decide)
  have hp2 : m2.pc = base + 0xFFFFC94C := by
    rw [pc2, show upd f ra (base + BitVec.ofNat 32 off + imm) ra = base + BitVec.ofNat 32 off + imm from
      by simp +decide [upd], hb]; exact even_clear _ hev
  have sp2 : reg m2 sp = G := by rw [r2 sp (by decide), hsp]
  have hOS : Sep G 8 (G + 0xFFFFFFD0) 48 := by
    have := sep_offsets (G + 0xFFFFFFD0) (c := 48) (n := 8) (d := 0) (k := 48) (by omega) (by omega)
      (by omega)
    rw [add_ofNat_zero, show G + 0xFFFFFFD0 + BitVec.ofNat 32 48 = G by
      rw [BitVec.add_assoc]; exact BitVec.add_zero G] at this
    exact this
  have hm : m2.mem = M := mem2
  obtain ⟨m3, c3, pc3, sp3, fr3, mem3⟩ := readerU32_correct m2 (base + 0xFFFFC94C)
    (base + BitVec.ofNat 32 (off + 8)) G self
    (fun i hi => by rw [hm]; exact hu i hi) (fun i hi => by rw [hm]; exact ha i hi)
    (fun i hi => by rw [hm]; exact hbb i hi) hev hp2 (by rw [r2 a0 (by decide), ha0])
    (by rw [r2 a1 (by decide), ha1]) r2ra (even_clear _ hl) (by rw [sp2]; exact hG) hG hself
    (by rw [hm]; exact hbuf) (by rw [sp2]; exact hSu) (by rw [sp2]; exact hSa) (by rw [sp2]; exact hSb)
    hOu hEu hEa hEb (by rw [sp2]; exact hRS) (by rw [sp2]; exact hOS) (by rw [sp2, hm]; exact hBS)
    (by rw [hm]; exact hBE)
  refine ⟨m3, .cons e1 (.cons e2 c3), ⟨by rw [pc3], rfl, fun _ => rfl⟩, by rw [sp3, sp2], ?_,
    fun r h0 h1 h2 h3 h4 h5 h6 => by rw [fr3 r h0 h1 h2 h3 h4 h5, r2 r h6], fun x hx => ?_⟩
  · rw [fr3 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r2ra]
  · rw [mem3 x (by rw [sp2]; exact hx), hm]

/-- `part`'s epilogue from offset 0x46: the restore helper restores the
saved registers from the frame at `G`, then `part` frees the frame and
returns to the saved `ra`. -/
theorem part_tail {M : Word → BitVec 8} {base : Word} {m : Machine} {f : Fin 32 → Word} {G : Word}
    (s : St M base m 0x46 f) (hc : CodeIn M base manifestPartCode) (hbase : base.toNat % 2 = 0)
    (h57 : CodeIn M (base + 0x129F4) partRestoreCode) (hsp : f sp = G) (hG : G.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = memLoad32 M (G + 0x1C) &&& ~~~1 ∧ m'.mem = M ∧
      ∀ r, reg m' r = upd (partRestored M G (upd f t0 (base + BitVec.ofNat 32 0x4E))) sp (G + 0x20) r := by
  obtain ⟨m1, e1, t1⟩ := s.callRestore hc part_at_46 part_at_4a
    (b := base + 0x129F4) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at base hbase 0x129F4 (by decide)) (even_at base hbase (0x46 + 8) (by decide)) h57
    partRestore_shape (by decide) (fun p hp => by
      rw [hsp]
      simp only [partRestorePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x1C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x18) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x14) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x10) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x0C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 8) (by decide)⟩)
  rw [hsp] at t1
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc part_at_4e (off' := 0x50) (by decide)
  have q : restoreRegs M G (upd f t0 (base + BitVec.ofNat 32 (0x46 + 8))) partRestorePs sp = G := by
    simp +decide only [restoreRegs, upd]; simp [hsp]
  rw [q, show aluEval .add G 0x20 = G + 0x20 from rfl] at t2
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := t2.jalr hc part_at_50
  refine ⟨m3, e1.trans (.cons e2 (.single e3)), ?_, mem3, regs3⟩
  rw [pc3, add_lit_zero]; simp +decide only [restoreRegs, upd, ite_true, ite_false]

/-- From offset 0x42: `part` stores the tag from `a0` at `out`, then runs
`part_tail`. -/
theorem part_from42 {M : Word → BitVec 8} {base : Word} {m : Machine} {f : Fin 32 → Word}
    {G out : Word} (s : St M base m 0x42 f) (hc : CodeIn M base manifestPartCode)
    (hbase : base.toNat % 2 = 0) (h57 : CodeIn M (base + 0x129F4) partRestoreCode)
    (hsp : f sp = G) (hG : G.toNat % 4 = 0) (hs0 : f s0 = out)
    (hOp : Sep out 1 base manifestPartCode.length) (hO57 : Sep out 1 (base + 0x129F4) partRestoreCode.length) :
    ∃ m', Steps m m' ∧
      m'.pc = memLoad32 (memStore8 M out ((f a0).extractLsb' 0 8)) (G + 0x1C) &&& ~~~1 ∧
      m'.mem = memStore8 M out ((f a0).extractLsb' 0 8) ∧
      ∀ r, reg m' r = upd (partRestored (memStore8 M out ((f a0).extractLsb' 0 8)) G
        (upd f t0 (base + BitVec.ofNat 32 0x4E))) sp (G + 0x20) r := by
  obtain ⟨m1, e1, t1⟩ := s.sb hc part_at_42 (off' := 0x46) (by decide)
  rw [hs0, add_lit_zero] at t1
  obtain ⟨m2, c2, pc2, mem2, regs2⟩ := part_tail t1 (hc.store8 hOp) hbase (h57.store8 hO57) hsp hG
  exact ⟨m2, .cons e1 c2, pc2, mem2, regs2⟩

/-- From offset 0x3C: `part` stores the error byte from `a0` at `out + 1`
and tag 1 at `out`, then runs `part_tail`. -/
theorem part_from3c {M : Word → BitVec 8} {base : Word} {m : Machine} {f : Fin 32 → Word}
    {G out : Word} (s : St M base m 0x3C f) (hc : CodeIn M base manifestPartCode)
    (hbase : base.toNat % 2 = 0) (h57 : CodeIn M (base + 0x129F4) partRestoreCode)
    (hsp : f sp = G) (hG : G.toNat % 4 = 0) (hs0 : f s0 = out)
    (hOp : Sep out 2 base manifestPartCode.length) (hO57 : Sep out 2 (base + 0x129F4) partRestoreCode.length) :
    ∃ m', Steps m m' ∧
      m'.pc = memLoad32 (memStore8 (memStore8 M (out + 1) ((f a0).extractLsb' 0 8)) out 1) (G + 0x1C)
        &&& ~~~1 ∧
      m'.mem = memStore8 (memStore8 M (out + 1) ((f a0).extractLsb' 0 8)) out 1 ∧
      ∀ r, reg m' r = upd (partRestored (memStore8 (memStore8 M (out + 1) ((f a0).extractLsb' 0 8)) out 1) G
        (upd (upd f a0 1) t0 (base + BitVec.ofNat 32 0x4E))) sp (G + 0x20) r := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.sb hc part_at_3c (off' := 0x40) (by decide)
  rw [hs0] at t1
  have hc1 := hc.store8 (a := out + 1) (v := (f a0).extractLsb' 0 8) (hOp.sub (c := 1) (l := 1) (by omega))
  have h571 := h57.store8 (a := out + 1) (v := (f a0).extractLsb' 0 8) (hO57.sub (c := 1) (l := 1) (by omega))
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc1 part_at_40 (off' := 0x42) (by decide)
  rw [show aluEval .add (f x0) 1 = 1 by rw [hz]; rfl] at t2
  have h0p : Sep out 1 base manifestPartCode.length := by
    have := hOp.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this
  have h057 : Sep out 1 (base + 0x129F4) partRestoreCode.length := by
    have := hO57.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this
  obtain ⟨m3, c3, pc3, mem3, regs3⟩ := part_from42 t2 hc1 hbase h571
    (by simp +decide [upd, hsp]) hG (by simp +decide [upd, hs0]) h0p h057
  rw [show (upd f a0 1 a0).extractLsb' 0 8 = 1 by simp +decide [upd]] at pc3 mem3 regs3
  exact ⟨m3, .cons e1 (.cons e2 c3), pc3, mem3, regs3⟩

theorem u32Mem_none {M : Word → BitVec 8} {G self : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 = none) :
    u32Mem M G self G = 1 ∧ u32Mem M G self (G + 1) = 0 ∧
    ∀ x, x ≠ G → x ≠ G + 1 → u32Mem M G self x = M x := by
  have n10 : G + 1 ≠ G := by
    have := add_ofNat_ne G (c := 1) (d := 0) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  unfold u32Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, by rw [memStore8_ne n10, memStore8_same], fun x h1 h2 => ?_⟩
  rw [memStore8_ne h1, memStore8_ne h2]

theorem u32Mem_some {M : Word → BitVec 8} {G self p e : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 =
      some (p, e)) :
    u32Mem M G self G = 0 ∧ memLoad32 (u32Mem M G self) (G + 4) = memLoad32 M p ∧
    ∀ x, x ≠ G → Sep (G + 4) 4 x 1 → u32Mem M G self x = memStore32 M (self + 8) e x := by
  unfold u32Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, ?_, fun x h1 h2 => ?_⟩
  · rw [memLoad32_store8_sep (by
      have := sep_offsets G (c := 0) (n := 1) (d := 4) (k := 4) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this), memLoad32_store32_same]
  · rw [memStore8_ne h1, memStore32_get_sep h2]

/-- The registers `part` writes before it restores the saved ones. -/
abbrev partClob : List (Fin 32) := [a0, a1, a2, a3, a4, a5, t0, ra, sp, s0, s1, s2, s3, s4]

theorem keep_upd {g h : Fin 32 → Word} {rd : Fin 32} {v : Word}
    (hk : ∀ r, r ∉ partClob → g r = h r) (h0 : h 0 = 0) (hrd : rd ∈ partClob) :
    ∀ r, r ∉ partClob → upd g rd v r = h r := by
  intro r hr
  by_cases hr0 : r.val = 0
  · have : r = 0 := Fin.ext hr0
    subst this; simp [upd, h0]
  · have : r ≠ rd := fun e => hr (e ▸ hrd)
    simp [upd, hr0, this, hk r hr]

/-- The registers after `part_tail`, from the saved slots of the frame at
`G` and the registers `g` before it. -/
theorem part_finish {Mf : Word → BitVec 8} {g h : Fin 32 → Word} {G L : Word}
    (hk : ∀ r, r ∉ partClob → g r = h r) (h0 : h 0 = 0)
    (hra : memLoad32 Mf (G + 0x1C) = h ra) (hs0 : memLoad32 Mf (G + 0x18) = h s0)
    (hs1 : memLoad32 Mf (G + 0x14) = h s1) (hs2 : memLoad32 Mf (G + 0x10) = h s2)
    (hs3 : memLoad32 Mf (G + 0x0C) = h s3) (hs4 : memLoad32 Mf (G + 8) = h s4)
    (hsp : G + 0x20 = h sp) :
    ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 →
      upd (partRestored Mf G (upd g t0 L)) sp (G + 0x20) r = h r := by
  intro r h1 h2 h3 h4 h5 h6 h7
  by_cases hr0 : r.val = 0
  · have : r = 0 := Fin.ext hr0
    subst this; simp [upd, h0]
  by_cases e : r = sp
  · subst e; simp +decide [upd]; exact hsp
  by_cases e1 : r = ra
  · subst e1; simp +decide [partRestored, restoreRegs, upd]; exact hra
  by_cases e2 : r = s0
  · subst e2; simp +decide [partRestored, restoreRegs, upd]; exact hs0
  by_cases e3 : r = s1
  · subst e3; simp +decide [partRestored, restoreRegs, upd]; exact hs1
  by_cases e4 : r = s2
  · subst e4; simp +decide [partRestored, restoreRegs, upd]; exact hs2
  by_cases e5 : r = s3
  · subst e5; simp +decide [partRestored, restoreRegs, upd]; exact hs3
  by_cases e6 : r = s4
  · subst e6; simp +decide [partRestored, restoreRegs, upd]; exact hs4
  have hr : r ∉ partClob := by
    simp only [partClob, List.mem_cons, List.not_mem_nil, or_false]
    intro hh
    rcases hh with hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh <;> contradiction
  simp only [partRestored, restoreRegs, upd, hr0, e, e1, e2, e3, e4, e5, e6, h7, ite_false]
  exact hk r hr

theorem add_ofNat_assoc' (p q : Word) (j : Nat) :
    p + q + BitVec.ofNat 32 j = p + BitVec.ofNat 32 (q.toNat + j) := by
  rw [← add_ofNat_assoc, ofNat_toNat_self]

/-- **The compiled `manifest::part` is correct.** With its bytes at `base`,
the helpers' and the `Reader` functions' where the image puts them, a result
address `out`, a reader `self` over a slice that is not null and doesn't
wrap, bounds `lo` and `hi`, everything aligned, and the 80 bytes of stack
below `sp` (its frame and `Reader::u32`'s), the result, the reader, its
position, its buffer, and the code it runs kept apart as the hypotheses
list, there is an execution that reaches the return address with `sp`
restored, every register but `a0` through `a5` and `t0` unchanged, and
memory outside those 80 bytes exactly as `partMem` says. -/
theorem manifestPart_correct (m : Machine) (base retAddr out self lo hi : Word)
    (hcode : CodeAt m base manifestPartCode)
    (h83 : CodeAt m (base + 0x12BB6) partSaveCode)
    (h57 : CodeAt m (base + 0x129F4) partRestoreCode)
    (hu : CodeAt m (base + 0xFFFFC94C) readerU32Code)
    (ha : CodeAt m (base + 0xFFFFC94C + 0xFFFFFADE) readerArray4Code)
    (hb : CodeAt m (base + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = self) (ha2 : reg m a2 = lo) (ha3 : reg m a3 = hi)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hout : out.toNat % 4 = 0) (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSW : Sep (reg m sp + 0xFFFFFFB0) 80 (partWindow base) partWindowLen)
    (hOW : Sep out 12 (partWindow base) partWindowLen)
    (hEW : Sep (self + 8) 4 (partWindow base) partWindowLen)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFB0) 80)
    (hOS : Sep out 12 (reg m sp + 0xFFFFFFB0) 80)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFB0) 80)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFB0) 80 x 1 → m'.mem x = partMem m.mem out self lo hi x := by
  -- The stack: 80 bytes at `S`, `part`'s frame at `G = S + 48`.
  obtain ⟨S, hSdef⟩ : ∃ S, reg m sp + 0xFFFFFFB0 = S := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G, reg m sp + 0xFFFFFFE0 = G := ⟨_, rfl⟩
  have hGS : G = S + BitVec.ofNat 32 48 := by rw [← hGdef, ← hSdef, BitVec.add_assoc]; rfl
  have hSG : G + 0xFFFFFFD0 = S := by rw [← hGdef, ← hSdef, BitVec.add_assoc]; rfl
  have hsp0 : G + 0x20 = reg m sp := by rw [← hGdef, BitVec.add_assoc]; exact BitVec.add_zero _
  rw [hSdef] at hSW hRS hOS hBS ⊢
  have hGa : G.toNat % 4 = 0 := hGdef ▸ aligned_add hsp (k := 0xFFFFFFE0) (by decide)
  -- The code window at `W`.
  obtain ⟨W, hWdef⟩ : ∃ W, base + 0xFFFFC3C0 = W := ⟨_, rfl⟩
  have hSW' : Sep S 80 W partWindowLen := by rw [← hWdef]; exact hSW
  have hOW' : Sep out 12 W partWindowLen := by rw [← hWdef]; exact hOW
  have hEW' : Sep (self + 8) 4 W partWindowLen := by rw [← hWdef]; exact hEW
  have wa : ∀ (b : Word) (c : Nat), b = W + BitVec.ofNat 32 c → ∀ i,
      b + BitVec.ofNat 32 i = W + BitVec.ofNat 32 (c + i) := fun b c h i => by rw [h, add_ofNat_assoc]
  have bP : base = W + BitVec.ofNat 32 0x3C40 := by
    rw [← hWdef, BitVec.add_assoc, show (0xFFFFC3C0 : Word) + BitVec.ofNat 32 0x3C40 = 0 from rfl]
    exact (BitVec.add_zero base).symm
  have bU : base + 0xFFFFC94C = W + BitVec.ofNat 32 0x58C := by rw [← hWdef, BitVec.add_assoc]; rfl
  have bA : base + 0xFFFFC94C + 0xFFFFFADE = W + BitVec.ofNat 32 0x6A := by
    rw [← hWdef]; simp only [BitVec.add_assoc]; rfl
  have bB : base + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96 = W + BitVec.ofNat 32 0 := by
    rw [← hWdef]; simp only [BitVec.add_assoc]; rfl
  have b57 : base + 0x129F4 = W + BitVec.ofNat 32 0x16634 := by rw [← hWdef, BitVec.add_assoc]; rfl
  have b83 : base + 0x12BB6 = W + BitVec.ofNat 32 0x167F6 := by rw [← hWdef, BitVec.add_assoc]; rfl
  have wS : ∀ k, k < partWindowLen → Sep S 80 (W + BitVec.ofNat 32 k) 1 :=
    fun k hk => hSW'.subR (c := k) (l := 1) (by omega)
  have wE : ∀ k, k < partWindowLen → Sep (self + 8) 4 (W + BitVec.ofNat 32 k) 1 :=
    fun k hk => hEW'.subR (c := k) (l := 1) (by omega)
  have codeAll : ∀ Mx : Word → BitVec 8, (∀ k, k < partWindowLen →
      Mx (W + BitVec.ofNat 32 k) = m.mem (W + BitVec.ofNat 32 k)) →
      CodeIn Mx base manifestPartCode ∧ CodeIn Mx (base + 0x12BB6) partSaveCode ∧
      CodeIn Mx (base + 0x129F4) partRestoreCode ∧ CodeIn Mx (base + 0xFFFFC94C) readerU32Code ∧
      CodeIn Mx (base + 0xFFFFC94C + 0xFFFFFADE) readerArray4Code ∧
      CodeIn Mx (base + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96) readerBytesCode := by
    intro Mx hx
    have tr : ∀ (b : Word) (c : Nat) (code : List Nat), b = W + BitVec.ofNat 32 c →
        c + code.length ≤ partWindowLen → CodeAt m b code → CodeIn Mx b code :=
      fun b c code hb hl hcd i hi => by
        rw [wa b c hb i, hx _ (by omega), ← wa b c hb i]; exact hcd i hi
    exact ⟨tr _ _ _ bP (by decide) hcode, tr _ _ _ b83 (by decide) h83, tr _ _ _ b57 (by decide) h57,
      tr _ _ _ bU (by decide) hu, tr _ _ _ bA (by decide) ha, tr _ _ _ bB (by decide) hb⟩
  have cs : ∀ (b : Word) (c : Nat) (code : List Nat), b = W + BitVec.ofNat 32 c →
      c + code.length ≤ partWindowLen →
      Sep S 80 b code.length ∧ Sep (self + 8) 4 b code.length ∧ Sep out 12 b code.length :=
    fun b c code hb hl => by
      rw [hb]; exact ⟨hSW'.subR hl, hEW'.subR hl, hOW'.subR hl⟩
  obtain ⟨-, -, OP⟩ := cs _ _ manifestPartCode bP (by decide)
  obtain ⟨S83, -, -⟩ := cs _ _ partSaveCode b83 (by decide)
  obtain ⟨-, -, O57⟩ := cs _ _ partRestoreCode b57 (by decide)
  obtain ⟨SU, EU, -⟩ := cs _ _ readerU32Code bU (by decide)
  obtain ⟨SA, EA, -⟩ := cs _ _ readerArray4Code bA (by decide)
  obtain ⟨SB, EB, -⟩ := cs _ _ readerBytesCode bB (by decide)
  -- Byte ranges around the frame.
  have fr : ∀ c l, c + l ≤ 32 → ∀ (x : Word) (n : Nat), Sep S 80 x n →
      Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := 48 + c) (l := l) (by omega)
  have s48 : ∀ (x : Word) (n : Nat), Sep S 80 x n → Sep (G + 0xFFFFFFD0) 48 x n := fun x n hx => by
    rw [hSG]; have := hx.sub (c := 0) (l := 48) (by omega); rwa [add_ofNat_zero] at this
  have gk48 : ∀ k, k < 32 → Sep (G + 0xFFFFFFD0) 48 (G + BitVec.ofNat 32 k) 1 := fun k hk => by
    rw [hSG, hGS, add_ofNat_assoc]
    have := sep_offsets S (c := 0) (n := 48) (d := 48 + k) (k := 1) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have gne : ∀ x, Sep S 80 x 1 → ∀ k, k < 32 → x ≠ G + BitVec.ofNat 32 k := fun x hx k hk e => by
    have := fr k 1 (by omega) x 1 hx
    exact this 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
  have gkne : ∀ j k, j < 32 → k < 32 → j ≠ k → G + BitVec.ofNat 32 j ≠ G + BitVec.ofNat 32 k :=
    fun j k hj hk h => add_ofNat_ne G (by omega) (by omega) h
  have g0 : G + BitVec.ofNat 32 0 = G := add_ofNat_zero G
  have outG : ∀ k, k < 32 → Sep out 12 (G + BitVec.ofNat 32 k) 1 := fun k hk => by
    rw [hGS, add_ofNat_assoc]; exact hOS.subR (c := 48 + k) (l := 1) (by omega)
  have selfS : ∀ c, c < 12 → Sep S 80 (self + BitVec.ofNat 32 c) 1 :=
    fun c hc => (hRS.sub (c := c) (l := 1) (by omega)).symm
  have selfE : ∀ c, c < 8 → Sep (self + 8) 4 (self + BitVec.ofNat 32 c) 1 := fun c hc => by
    have := sep_offsets self (c := 8) (n := 4) (d := c) (k := 1) (by omega) (by omega) (by omega)
    exact this
  have ldS : ∀ (Mx Mx' : Word → BitVec 8), (∀ x, Sep S 80 x 1 → Mx x = Mx' x) → ∀ c, c + 4 ≤ 12 →
      memLoad32 Mx (self + BitVec.ofNat 32 c) = memLoad32 Mx' (self + BitVec.ofNat 32 c) :=
    fun Mx Mx' h c hc => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact h _ (selfS _ (by omega))
  -- `ptr` and `len` don't change: the stores land in the stack or at `self + 8`.
  have ld : ∀ (Mx : Word → BitVec 8) (e : Word),
      (∀ x, Sep S 80 x 1 → Mx x = memStore32 m.mem (self + 8) e x) →
      memLoad32 Mx self = memLoad32 m.mem self ∧ memLoad32 Mx (self + 4) = memLoad32 m.mem (self + 4) ∧
      memLoad32 Mx (self + 8) = e := by
    intro Mx e h
    have k : ∀ c, c + 4 ≤ 8 → memLoad32 Mx (self + BitVec.ofNat 32 c) = memLoad32 m.mem (self + BitVec.ofNat 32 c) :=
      fun c hc => by
        rw [ldS Mx _ h c (by omega)]
        exact memLoad32_congr fun j hj => by
          rw [add_ofNat_assoc]; exact memStore32_get_sep (selfE _ (by omega))
    refine ⟨by have := k 0 (by omega); rwa [add_ofNat_zero] at this, k 4 (by omega), ?_⟩
    rw [show self + 8 = self + BitVec.ofNat 32 8 from rfl, ldS Mx _ h 8 (by omega)]
    exact memLoad32_store32_same _ _ _
  have ld0 : ∀ (Mx : Word → BitVec 8), (∀ x, Sep S 80 x 1 → Mx x = m.mem x) →
      memLoad32 Mx self = memLoad32 m.mem self ∧ memLoad32 Mx (self + 4) = memLoad32 m.mem (self + 4) ∧
      memLoad32 Mx (self + 8) = memLoad32 m.mem (self + 8) := by
    intro Mx h
    have k : ∀ c, c + 4 ≤ 12 → memLoad32 Mx (self + BitVec.ofNat 32 c) =
        memLoad32 m.mem (self + BitVec.ofNat 32 c) := fun c hc => ldS Mx _ h c hc
    exact ⟨by have := k 0 (by omega); rwa [add_ofNat_zero] at this, k 4 (by omega), k 8 (by omega)⟩
  -- The buffer.
  obtain ⟨ptr, hptr⟩ : ∃ ptr, memLoad32 m.mem self = ptr := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, memLoad32 m.mem (self + 4) = len := ⟨_, rfl⟩
  rw [hptr, hlen] at hBS hBE hbuf
  have bufS : ∀ k, k < len.toNat → Sep S 80 (ptr + BitVec.ofNat 32 k) 1 :=
    fun k hk => (hBS.sub (c := k) (l := 1) (by omega)).symm
  have bufE : ∀ k, k < len.toNat → Sep (self + 8) 4 (ptr + BitVec.ofNat 32 k) 1 :=
    fun k hk => (hBE.sub (c := k) (l := 1) (by omega)).symm
  -- A load from the buffer at a position that `bytesResult` accepted.
  have bufLd : ∀ (Mx : Word → BitVec 8) (pos p e' : Word),
      (∀ x, Sep S 80 x 1 → Sep (self + 8) 4 x 1 → Mx x = m.mem x) →
      bytesResult ptr len pos 4 = some (p, e') → memLoad32 Mx p = memLoad32 m.mem p := by
    intro Mx pos p e' h hR
    rw [bytesResult_eq] at hR
    split at hR
    case isFalse => cases hR
    rename_i hle
    simp only [Option.some.injEq, Prod.mk.injEq] at hR
    obtain ⟨hp, -⟩ := hR
    rw [show (4 : Word).toNat = 4 from rfl] at hle
    subst hp
    exact memLoad32_congr fun j hj => h _ (by rw [add_ofNat_assoc']; exact bufS (pos.toNat + j) (by omega))
      (by rw [add_ofNat_assoc']; exact bufE (pos.toNat + j) (by omega))
  have selfG : ∀ k, k < 32 → Sep (self + 8) 4 (G + BitVec.ofNat 32 k) 1 := fun k hk => by
    rw [hGS, add_ofNat_assoc]
    exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 48 + k) (l := 1) (by omega)
  -- 0x00: allocate the frame.
  have s0' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  obtain ⟨c0, c083, -, -, -, -⟩ := codeAll m.mem (fun _ _ => rfl)
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm c0 part_at_00 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFE0 = G from hGdef] at t1
  have f1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h]
  -- 0x02: the save helper saves `ra` and `s0` through `s3`.
  obtain ⟨m2, k2, t2⟩ := t1.callSave c0 part_at_02 part_at_06 (b := base + 0x12BB6)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0x12BB6 (by decide))
    (even_at base hbase (2 + 8) (by decide)) c083 partSave_shape (by decide) (fun p hp => by
      rw [f1sp]
      simp only [partSavePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, aligned_add hGa (k := 0x1C) (by decide), fr 0x1C 4 (by omega) _ _ S83⟩
      · exact ⟨by decide, aligned_add hGa (k := 0x18) (by decide), fr 0x18 4 (by omega) _ _ S83⟩
      · exact ⟨by decide, aligned_add hGa (k := 0x14) (by decide), fr 0x14 4 (by omega) _ _ S83⟩
      · exact ⟨by decide, aligned_add hGa (k := 0x10) (by decide), fr 0x10 4 (by omega) _ _ S83⟩
      · exact ⟨by decide, aligned_add hGa (k := 0x0C) (by decide), fr 0x0C 4 (by omega) _ _ S83⟩)
  rw [f1sp] at t2
  obtain ⟨M1, hM1⟩ : ∃ M1, saveMem m.mem G (upd (reg m) sp G) partSavePs = M1 := ⟨_, rfl⟩
  rw [hM1] at t2
  have M1out : ∀ x, Sep S 80 x 1 → M1 x = m.mem x := fun x hx => by
    rw [← hM1]; simp only [saveMem]
    rw [memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from fr 0x0C 4 (by omega) x 1 hx),
      memStore32_get_sep (show Sep (G + 0x10) 4 x 1 from fr 0x10 4 (by omega) x 1 hx),
      memStore32_get_sep (show Sep (G + 0x14) 4 x 1 from fr 0x14 4 (by omega) x 1 hx),
      memStore32_get_sep (show Sep (G + 0x18) 4 x 1 from fr 0x18 4 (by omega) x 1 hx),
      memStore32_get_sep (show Sep (G + 0x1C) 4 x 1 from fr 0x1C 4 (by omega) x 1 hx)]
  obtain ⟨c1, -, -, -, -, -⟩ := codeAll M1 (fun k hk => M1out _ (wS k hk))
  -- 0x0A: save `s4`.
  have g2 : ∀ r, r ≠ sp → r ≠ t0 →
      upd (upd (reg m) sp G) t0 (base + BitVec.ofNat 32 (2 + 8)) r = reg m r := fun r h1 h2 => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h1, h2]
  have g2sp : upd (upd (reg m) sp G) t0 (base + BitVec.ofNat 32 (2 + 8)) sp = G := by simp +decide [upd]
  obtain ⟨m3, e3, t3⟩ := t2.sw c1 part_at_0a (off' := 0x0C) (by decide)
    (by rw [g2sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [g2sp, g2 s4 (by decide) (by decide)] at t3
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 M1 (G + 8) (reg m s4) = M2 := ⟨_, rfl⟩
  rw [hM2] at t3
  have M2out : ∀ x, Sep S 80 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2, memStore32_get_sep (show Sep (G + 8) 4 x 1 from fr 8 4 (by omega) x 1 hx), M1out x hx]
  have M2slots : memLoad32 M2 (G + 0x1C) = reg m ra ∧ memLoad32 M2 (G + 0x18) = reg m s0 ∧
      memLoad32 M2 (G + 0x14) = reg m s1 ∧ memLoad32 M2 (G + 0x10) = reg m s2 ∧
      memLoad32 M2 (G + 0x0C) = reg m s3 ∧ memLoad32 M2 (G + 8) = reg m s4 := by
    have so : ∀ c d, c < 32 → d < 32 → c + 4 ≤ d ∨ d + 4 ≤ c →
        Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 :=
      fun c d hc hd h => sep_offsets G h (by omega) (by omega)
    rw [← hM2, ← hM1]; simp only [saveMem]
    refine ⟨?_, ?_, ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x1C) 4 from so 8 0x1C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x1C) 4 from so 0x0C 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x1C) 4 from so 0x10 0x1C (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x14) 4 (G + 0x1C) 4 from so 0x14 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x18) 4 (G + 0x1C) 4 from so 0x18 0x1C (by omega) (by omega) (by omega)), memLoad32_store32_same, f1 ra (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x18) 4 from so 8 0x18 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x18) 4 from so 0x0C 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x18) 4 from so 0x10 0x18 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x14) 4 (G + 0x18) 4 from so 0x14 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_same, f1 s0 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x14) 4 from so 8 0x14 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x14) 4 from so 0x0C 0x14 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x14) 4 from so 0x10 0x14 (by omega) (by omega) (by omega)), memLoad32_store32_same, f1 s1 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x10) 4 from so 8 0x10 (by omega) (by omega) (by omega)), memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x10) 4 from so 0x0C 0x10 (by omega) (by omega) (by omega)),
        memLoad32_store32_same, f1 s2 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x0C) 4 from so 8 0x0C (by omega) (by omega) (by omega)), memLoad32_store32_same, f1 s3 (by decide)]
  -- Every later memory that agrees with `M2` on the saved slots restores the registers.
  have slots : ∀ Mx : Word → BitVec 8, (∀ k, 8 ≤ k → k < 32 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) →
      memLoad32 Mx (G + 0x1C) = reg m ra ∧ memLoad32 Mx (G + 0x18) = reg m s0 ∧
      memLoad32 Mx (G + 0x14) = reg m s1 ∧ memLoad32 Mx (G + 0x10) = reg m s2 ∧
      memLoad32 Mx (G + 0x0C) = reg m s3 ∧ memLoad32 Mx (G + 8) = reg m s4 := by
    intro Mx h
    have e : ∀ c, 8 ≤ c → c + 4 ≤ 32 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M2 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := M2slots
    exact ⟨(e 0x1C (by omega) (by omega)).trans q1, (e 0x18 (by omega) (by omega)).trans q2,
      (e 0x14 (by omega) (by omega)).trans q3, (e 0x10 (by omega) (by omega)).trans q4,
      (e 0x0C (by omega) (by omega)).trans q5, (e 8 (by omega) (by omega)).trans q6⟩
  -- 0x0C to 0x14: move the arguments to saved registers.
  obtain ⟨c2, -, -, c2u, c2a, c2b⟩ := codeAll M2 (fun k hk => M2out _ (wS k hk))
  obtain ⟨m4, e4, t4⟩ := t3.alu c2 part_at_0c (off' := 0x0E) (by decide)
  obtain ⟨m5, e5, t5⟩ := t4.alu c2 part_at_0e (off' := 0x10) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.alu c2 part_at_10 (off' := 0x12) (by decide)
  obtain ⟨m7, e7, t7⟩ := t6.alu c2 part_at_12 (off' := 0x14) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.alu c2 part_at_14 (off' := 0x16) (by decide)
  have keep8 : ∀ r, r ∉ partClob → reg m8 r = reg m r := fun r hr => by
    rw [t8.regs]
    exact keep_upd (keep_upd (keep_upd (keep_upd (keep_upd (keep_upd (keep_upd (fun _ _ => rfl) hz
      (by decide)) hz (by decide)) hz (by decide)) hz (by decide)) hz (by decide)) hz (by decide)) hz
      (by decide) r hr
  have q8 : reg m8 sp = G ∧ reg m8 a0 = G ∧ reg m8 a1 = self ∧ reg m8 s0 = out ∧ reg m8 s1 = self ∧
      reg m8 s2 = hi ∧ reg m8 s3 = lo ∧ reg m8 s4 = reg m s4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp +decide [t8.regs, upd, aluEval, ha0, ha1, ha2, ha3]
  obtain ⟨q8sp, q8a0, q8a1, q8s0, q8s1, q8s2, q8s3, q8s4⟩ := q8
  -- What every path ends with.
  have finish : ∀ (n : Machine) (Mf : Word → BitVec 8) (g : Fin 32 → Word),
      (∀ k, 8 ≤ k → k < 32 → Mf (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) →
      (∀ r, r ∉ partClob → g r = reg m r) →
      n.pc = memLoad32 Mf (G + 0x1C) &&& ~~~1 → n.mem = Mf →
      (∀ r, reg n r = upd (partRestored Mf G (upd g t0 (base + BitVec.ofNat 32 0x4E))) sp (G + 0x20) r) →
      (∀ x, Sep S 80 x 1 → Mf x = partMem m.mem out self lo hi x) →
      n.pc = retAddr ∧ reg n sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg n r = reg m r) ∧
      ∀ x, Sep S 80 x 1 → n.mem x = partMem m.mem out self lo hi x := by
    intro n Mf g hsl hk hpc' hmem hregs hx
    obtain ⟨sl1, sl2, sl3, sl4, sl5, sl6⟩ := slots Mf hsl
    have fin := part_finish (L := base + BitVec.ofNat 32 0x4E) hk hz sl1 sl2 sl3 sl4 sl5 sl6 hsp0
    refine ⟨by rw [hpc', sl1, hra, hret], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => by
      rw [hregs]; exact fin r h1 h2 h3 h4 h5 h6 h7, fun x h => by rw [hmem]; exact hx x h⟩
    rw [hregs]
    exact fin sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have nc : ∀ r, r ∉ partClob → ∀ q, q ∈ partClob → r ≠ q := fun r hr q hq e => hr (e ▸ hq)
  have outne : ∀ k, k < 32 → ∀ c, c < 12 → G + BitVec.ofNat 32 k ≠ out + BitVec.ofNat 32 c :=
    fun k hk c hc e => outG k hk c hc 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)
  have outne1 : ∀ k, k < 32 → G + BitVec.ofNat 32 k ≠ out + 1 := fun k hk => outne k hk 1 (by omega)
  have outne0 : ∀ k, k < 32 → G + BitVec.ofNat 32 k ≠ out := fun k hk => by
    have := outne k hk 0 (by omega); rwa [add_ofNat_zero] at this
  have O2 : Sep out 2 base manifestPartCode.length := by
    have := OP.sub (c := 0) (l := 2) (by omega); rwa [add_ofNat_zero] at this
  have O257 : Sep out 2 (base + 0x129F4) partRestoreCode.length := by
    have := O57.sub (c := 0) (l := 2) (by omega); rwa [add_ofNat_zero] at this
  have O1 : Sep out 1 base manifestPartCode.length := by
    have := OP.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this
  have O157 : Sep out 1 (base + 0x129F4) partRestoreCode.length := by
    have := O57.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this
  -- 0x16: the first `Reader::u32`, for the offset.
  have hRS48 : Sep self 12 (G + 0xFFFFFFD0) 48 := by
    rw [hSG]; have := hRS.subR (c := 0) (l := 48) (by omega); rwa [add_ofNat_zero] at this
  have hOu : Sep G 8 (base + 0xFFFFC94C) readerU32Code.length := by
    have := fr 0 8 (by omega) _ _ SU; rwa [g0] at this
  have hBS48 : Sep ptr len.toNat (G + 0xFFFFFFD0) 48 := by
    rw [hSG]; have := hBS.subR (c := 0) (l := 48) (by omega); rwa [add_ofNat_zero] at this
  obtain ⟨l2a, l2b, l2c⟩ := ld0 M2 M2out
  obtain ⟨m9, k9, t9, sp9, -, fr9, mem9⟩ := part_call_u32 t8.self c2 part_at_16 part_at_1a
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase (0x16 + 8) (by decide)) hbase
    c2u c2a c2b q8sp q8a0 q8a1 hGa hself (by rw [l2a, l2b, hptr, hlen]; exact hbuf)
    (s48 _ _ SU) (s48 _ _ SA) (s48 _ _ SB) hOu EU EA EB hRS48 (by rw [l2a, l2b, hptr, hlen]; exact hBS48)
    (by rw [l2a, l2b, hptr, hlen]; exact hBE)
  have keep9 : ∀ r, r ∉ partClob → reg m9 r = reg m r := fun r hr => by
    rw [fr9 r (nc r hr a0 (by decide)) (nc r hr a1 (by decide)) (nc r hr a2 (by decide))
      (nc r hr a3 (by decide)) (nc r hr a4 (by decide)) (nc r hr a5 (by decide)) (nc r hr ra (by decide))]
    exact keep8 r hr
  have s9 : ∀ r, r = s0 ∨ r = s1 ∨ r = s2 ∨ r = s3 ∨ r = s4 → reg m9 r = reg m8 r := fun r hr => by
    apply fr9 <;> rcases hr with h | h | h | h | h <;> subst h <;> decide
  have hR1e : bytesResult (memLoad32 M2 self) (memLoad32 M2 (self + 4)) (memLoad32 M2 (self + 8)) 4 =
      bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 := by rw [l2a, l2b, l2c, hptr, hlen]
  have g04 : G + 4 = G + BitVec.ofNat 32 4 := rfl
  have g01 : G + 1 = G + BitVec.ofNat 32 1 := rfl
  have G48 : Sep (G + 0xFFFFFFD0) 48 G 1 := by have := gk48 0 (by omega); rwa [g0] at this
  rcases hR1 : bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 with _ | ⟨p1, e1'⟩
  · -- The offset is truncated.
    obtain ⟨u0, u1, ux⟩ := u32Mem_none (G := G) (hR1e.trans hR1)
    have m9G : m9.mem G = 1 := by rw [mem9 G G48, u0]
    have m9G1 : m9.mem (G + 1) = 0 := by rw [g01, mem9 _ (gk48 1 (by omega))]; exact u1
    have m9out : ∀ x, Sep S 80 x 1 → m9.mem x = m.mem x := fun x hx => by
      rw [mem9 x (s48 _ _ hx), ux x (by have := gne x hx 0 (by omega); rwa [g0] at this)
        (gne x hx 1 (by omega)), M2out x hx]
    have m9slot : ∀ k, 8 ≤ k → k < 32 → m9.mem (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k) :=
      fun k h1 h2 => by
        rw [mem9 _ (gk48 k h2), ux _ (by have := gkne k 0 h2 (by omega) (by omega); rwa [g0] at this)
          (gkne k 1 h2 (by omega) (by omega))]
    obtain ⟨c9, -, c957, -, -, -⟩ := codeAll m9.mem (fun k hk => m9out _ (wS k hk))
    obtain ⟨n1, d1, u1'⟩ := t9.lbu c9 part_at_1e (off' := 0x22) (by decide)
    rw [sp9, add_lit_zero, m9G] at u1'
    obtain ⟨n2, d2, u2⟩ := u1'.taken c9 0x38 part_at_22 (by decide) (by simp +decide [upd])
    obtain ⟨n3, d3, u3⟩ := u2.lbu c9 part_at_38 (off' := 0x3C) (by decide)
    rw [show upd (reg m9) a0 ((1 : BitVec 8).zeroExtend 32) sp = G by simp +decide [upd, sp9], m9G1] at u3
    obtain ⟨n4, k4, pc4, mem4, regs4⟩ := part_from3c u3 c9 hbase c957 (by simp +decide [upd, sp9]) hGa
      (by simp +decide [upd, s9 s0 (by decide), q8s0]) O2 O257
    rw [show (upd (upd (reg m9) a0 ((1 : BitVec 8).zeroExtend 32)) a0 ((0 : BitVec 8).zeroExtend 32) a0).extractLsb' 0 8
      = 0 by simp +decide [upd]] at pc4 mem4 regs4
    obtain ⟨A, B, C, D⟩ := finish n4 _ _
      (fun k h1 h2 => by
        rw [memStore8_ne (outne0 k h2), memStore8_ne (outne1 k h2), m9slot k h1 h2])
      (keep_upd (keep_upd (keep_upd keep9 hz (by decide)) hz (by decide)) hz (by decide)) pc4 mem4 regs4
      (fun x hx => by
        unfold partMem; rw [hptr, hlen, hR1]; dsimp only
        exact memStore8_congr (memStore8_congr (m9out x hx)))
    exact ⟨n4, .cons e1 (k2.trans (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
      (k9.trans (.cons d1 (.cons d2 (.cons d3 k4))))))))))), A, B, C, D⟩
  · -- The offset is read.
    obtain ⟨u0, u4, ux⟩ := u32Mem_some (G := G) (hR1e.trans hR1)
    have m9G : m9.mem G = 0 := by rw [mem9 G G48, u0]
    have m9out : ∀ x, Sep S 80 x 1 → m9.mem x = memStore32 m.mem (self + 8) e1' x := fun x hx => by
      rw [mem9 x (s48 _ _ hx), ux x (by have := gne x hx 0 (by omega); rwa [g0] at this)
        (by rw [g04]; exact fr 4 4 (by omega) x 1 hx)]
      exact memStore32_congr (M2out x hx)
    have m9slot : ∀ k, 8 ≤ k → k < 32 → m9.mem (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k) :=
      fun k h1 h2 => by
        rw [mem9 _ (gk48 k h2), ux _ (by have := gkne k 0 h2 (by omega) (by omega); rwa [g0] at this)
          (by rw [g04]; exact sep_offsets G (c := 4) (n := 4) (d := k) (k := 1) (by omega) (by omega) (by omega)),
          memStore32_get_sep (selfG k h2)]
    have m9v : memLoad32 m9.mem (G + 4) = memLoad32 m.mem p1 := by
      have h1 : memLoad32 m9.mem (G + BitVec.ofNat 32 4) = memLoad32 (u32Mem M2 G self) (G + BitVec.ofNat 32 4) :=
        memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact mem9 _ (gk48 (4 + j) (by omega))
      rw [g04, h1]
      exact u4.trans (bufLd M2 _ p1 e1' (fun x hx _ => M2out x hx) hR1)
    have m9agree : ∀ k, k < partWindowLen → m9.mem (W + BitVec.ofNat 32 k) = m.mem (W + BitVec.ofNat 32 k) :=
      fun k hk => by rw [m9out _ (wS k hk), memStore32_get_sep (wE k hk)]
    obtain ⟨c9, -, -, c9u, c9a, c9b⟩ := codeAll m9.mem m9agree
    obtain ⟨n1, d1, u1'⟩ := t9.lbu c9 part_at_1e (off' := 0x22) (by decide)
    rw [sp9, add_lit_zero, m9G] at u1'
    obtain ⟨n2, d2, u2⟩ := u1'.notTaken c9 0x24 part_at_22 (by decide) (by simp +decide [upd])
    have r2sp : upd (reg m9) a0 ((0 : BitVec 8).zeroExtend 32) sp = G := by simp +decide [upd, sp9]
    obtain ⟨n3, d3, u3⟩ := u2.lw c9 part_at_24 (off' := 0x26) (by decide)
      (by rw [r2sp]; exact aligned_add hGa (k := 4) (by decide))
    rw [r2sp, m9v] at u3
    obtain ⟨n4, d4, u4'⟩ := u3.alu c9 part_at_26 (off' := 0x28) (by decide)
    obtain ⟨n5, d5, u5⟩ := u4'.alu c9 part_at_28 (off' := 0x2A) (by decide)
    have keep5 : ∀ r, r ∉ partClob → reg n5 r = reg m r := fun r hr => by
      rw [u5.regs]
      exact keep_upd (keep_upd (keep_upd (keep_upd keep9 hz (by decide)) hz (by decide)) hz (by decide)) hz
        (by decide) r hr
    have q5 : reg n5 sp = G ∧ reg n5 a0 = G ∧ reg n5 a1 = self ∧ reg n5 s0 = out ∧ reg n5 s2 = hi ∧
        reg n5 s3 = lo ∧ reg n5 s4 = memLoad32 m.mem p1 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp +decide [u5.regs, upd, aluEval, sp9, s9 s0 (by decide), s9 s1 (by decide),
          s9 s2 (by decide), s9 s3 (by decide), q8s0, q8s1, q8s2, q8s3]
    obtain ⟨q5sp, q5a0, q5a1, q5s0, q5s2, q5s3, q5s4⟩ := q5
    -- 0x2A: the second `Reader::u32`, for the length.
    obtain ⟨l9a, l9b, l9c⟩ := ld m9.mem e1' m9out
    obtain ⟨m10, k10, t10, sp10, -, fr10, mem10⟩ := part_call_u32 u5.self c9 part_at_2a part_at_2e
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase (0x2A + 8) (by decide)) hbase
      c9u c9a c9b q5sp q5a0 q5a1 hGa hself (by rw [l9a, l9b, hptr, hlen]; exact hbuf)
      (s48 _ _ SU) (s48 _ _ SA) (s48 _ _ SB) hOu EU EA EB hRS48 (by rw [l9a, l9b, hptr, hlen]; exact hBS48)
      (by rw [l9a, l9b, hptr, hlen]; exact hBE)
    have keep10 : ∀ r, r ∉ partClob → reg m10 r = reg m r := fun r hr => by
      rw [fr10 r (nc r hr a0 (by decide)) (nc r hr a1 (by decide)) (nc r hr a2 (by decide))
        (nc r hr a3 (by decide)) (nc r hr a4 (by decide)) (nc r hr a5 (by decide)) (nc r hr ra (by decide))]
      exact keep5 r hr
    have s10 : ∀ r, r = s0 ∨ r = s2 ∨ r = s3 ∨ r = s4 → reg m10 r = reg n5 r := fun r hr => by
      apply fr10 <;> rcases hr with h | h | h | h <;> subst h <;> decide
    have hR2e : bytesResult (memLoad32 m9.mem self) (memLoad32 m9.mem (self + 4)) (memLoad32 m9.mem (self + 8)) 4 =
        bytesResult ptr len e1' 4 := by rw [l9a, l9b, l9c, hptr, hlen]
    have pre : ∀ (n : Machine), Steps m10 n → Steps m n := fun n h =>
      .cons e1 (k2.trans (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (k9.trans
        (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (k10.trans h))))))))))))))
    rcases hR2 : bytesResult ptr len e1' 4 with _ | ⟨p2, e2'⟩
    · -- The length is truncated.
      obtain ⟨w0, w1, wx⟩ := u32Mem_none (G := G) (hR2e.trans hR2)
      have m10G : m10.mem G = 1 := by rw [mem10 G G48, w0]
      have m10G1 : m10.mem (G + 1) = 0 := by rw [g01, mem10 _ (gk48 1 (by omega))]; exact w1
      have m10out : ∀ x, Sep S 80 x 1 → m10.mem x = memStore32 m.mem (self + 8) e1' x := fun x hx => by
        rw [mem10 x (s48 _ _ hx), wx x (by have := gne x hx 0 (by omega); rwa [g0] at this)
          (gne x hx 1 (by omega)), m9out x hx]
      have m10slot : ∀ k, 8 ≤ k → k < 32 → m10.mem (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k) :=
        fun k h1 h2 => by
          rw [mem10 _ (gk48 k h2), wx _ (by have := gkne k 0 h2 (by omega) (by omega); rwa [g0] at this)
            (gkne k 1 h2 (by omega) (by omega)), m9slot k h1 h2]
      obtain ⟨c10, -, c1057, -, -, -⟩ := codeAll m10.mem
        (fun k hk => by rw [m10out _ (wS k hk), memStore32_get_sep (wE k hk)])
      obtain ⟨n6, d6, u6⟩ := t10.lbu c10 part_at_32 (off' := 0x36) (by decide)
      rw [sp10, add_lit_zero, m10G] at u6
      obtain ⟨n7, d7, u7⟩ := u6.notTaken c10 0x38 part_at_36 (by decide) (by simp +decide [upd])
      obtain ⟨n8, d8, u8⟩ := u7.lbu c10 part_at_38 (off' := 0x3C) (by decide)
      rw [show upd (reg m10) a0 ((1 : BitVec 8).zeroExtend 32) sp = G by simp +decide [upd, sp10], m10G1] at u8
      obtain ⟨n9, k9', pc9, mem9', regs9⟩ := part_from3c u8 c10 hbase c1057 (by simp +decide [upd, sp10]) hGa
        (by simp +decide [upd, s10 s0 (by decide), q5s0]) O2 O257
      rw [show (upd (upd (reg m10) a0 ((1 : BitVec 8).zeroExtend 32)) a0 ((0 : BitVec 8).zeroExtend 32) a0).extractLsb' 0 8
        = 0 by simp +decide [upd]] at pc9 mem9' regs9
      obtain ⟨A, B, C, D⟩ := finish n9 _ _
        (fun k h1 h2 => by
          rw [memStore8_ne (outne0 k h2), memStore8_ne (outne1 k h2), m10slot k h1 h2])
        (keep_upd (keep_upd (keep_upd keep10 hz (by decide)) hz (by decide)) hz (by decide)) pc9 mem9' regs9
        (fun x hx => by
          unfold partMem; rw [hptr, hlen, hR1]; dsimp only; rw [hR2]; dsimp only
          exact memStore8_congr (memStore8_congr (m10out x hx)))
      exact ⟨n9, pre _ (.cons d6 (.cons d7 (.cons d8 k9'))), A, B, C, D⟩
    · -- The length is read.
      obtain ⟨w0, w4, wx⟩ := u32Mem_some (G := G) (hR2e.trans hR2)
      have m10G : m10.mem G = 0 := by rw [mem10 G G48, w0]
      have m10out : ∀ x, Sep S 80 x 1 → m10.mem x = memStore32 m.mem (self + 8) e2' x := fun x hx => by
        rw [mem10 x (s48 _ _ hx), wx x (by have := gne x hx 0 (by omega); rwa [g0] at this)
          (by rw [g04]; exact fr 4 4 (by omega) x 1 hx), memStore32_congr (m9out x hx)]
        exact memStore32_overwrite _ _ _ _ _
      have m10slot : ∀ k, 8 ≤ k → k < 32 → m10.mem (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k) :=
        fun k h1 h2 => by
          rw [mem10 _ (gk48 k h2), wx _ (by have := gkne k 0 h2 (by omega) (by omega); rwa [g0] at this)
            (by rw [g04]; exact sep_offsets G (c := 4) (n := 4) (d := k) (k := 1) (by omega) (by omega) (by omega)),
            memStore32_get_sep (selfG k h2), m9slot k h1 h2]
      have m10v : memLoad32 m10.mem (G + 4) = memLoad32 m.mem p2 := by
        have h1 : memLoad32 m10.mem (G + BitVec.ofNat 32 4) =
            memLoad32 (u32Mem m9.mem G self) (G + BitVec.ofNat 32 4) :=
          memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact mem10 _ (gk48 (4 + j) (by omega))
        rw [g04, h1]
        exact w4.trans (bufLd m9.mem _ p2 e2' (fun x hx hx' => by rw [m9out x hx, memStore32_get_sep hx']) hR2)
      obtain ⟨c10, -, c1057, -, -, -⟩ := codeAll m10.mem
        (fun k hk => by rw [m10out _ (wS k hk), memStore32_get_sep (wE k hk)])
      obtain ⟨n6, d6, u6⟩ := t10.lbu c10 part_at_32 (off' := 0x36) (by decide)
      rw [sp10, add_lit_zero, m10G] at u6
      obtain ⟨n7, d7, u7⟩ := u6.taken c10 0x52 part_at_36 (by decide) (by simp +decide [upd])
      have r7sp : upd (reg m10) a0 ((0 : BitVec 8).zeroExtend 32) sp = G := by simp +decide [upd, sp10]
      obtain ⟨n8, d8, u8⟩ := u7.lw c10 part_at_52 (off' := 0x54) (by decide)
        (by rw [r7sp]; exact aligned_add hGa (k := 4) (by decide))
      rw [r7sp, m10v] at u8
      obtain ⟨v1, hv1⟩ : ∃ v1, memLoad32 m.mem p1 = v1 := ⟨_, rfl⟩
      obtain ⟨v2, hv2⟩ : ∃ v2, memLoad32 m.mem p2 = v2 := ⟨_, rfl⟩
      rw [hv2] at u8
      have r8 : reg n8 a1 = v2 ∧ reg n8 s0 = out ∧ reg n8 s2 = hi ∧ reg n8 s3 = lo ∧ reg n8 s4 = v1 ∧
          reg n8 sp = G ∧ ∀ r, r ∉ partClob → reg n8 r = reg m r := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
        · rw [u8.regs]; simp +decide [upd]
        · rw [u8.regs]; simp +decide [upd, s10 s0 (by decide), q5s0]
        · rw [u8.regs]; simp +decide [upd, s10 s2 (by decide), q5s2]
        · rw [u8.regs]; simp +decide [upd, s10 s3 (by decide), q5s3]
        · rw [u8.regs]; simp +decide [upd, s10 s4 (by decide), q5s4, hv1]
        · rw [u8.regs]; simp +decide [upd, sp10]
        · rw [u8.regs]; exact keep_upd (keep_upd keep10 hz (by decide)) hz (by decide) r hr
      obtain ⟨r8a1, r8s0, r8s2, r8s3, r8s4, r8sp, keep8'⟩ := r8
      have u8' := u8.self
      have hz8 := u8'.zero
      have memF : ∀ x, Sep S 80 x 1 →
          partMem m.mem out self lo hi x =
            if v2.ult lo || hi.ult v2 then
              memStore8 (memStore8 (memStore32 m.mem (self + 8) e2') (out + 1) 5) out 1 x
            else
              memStore8 (memStore32 (memStore32 (memStore32 m.mem (self + 8) e2') (out + 4) v1)
                (out + 8) v2) out 0 x := fun x _ => by
        unfold partMem; rw [hptr, hlen, hR1]; dsimp only; rw [hR2]; dsimp only; rw [hv1, hv2]
        split <;> rfl
      by_cases hc : (v2.ult lo || hi.ult v2) = true
      · -- The length is out of range.
        have h66 : ∃ n, Steps n8 n ∧ St m10.mem base n 0x66 (reg n8) := by
          cases hlo : v2.ult lo
          · have hhi : hi.ult v2 = true := by simpa [hlo] using hc
            obtain ⟨na, da, ua⟩ := u8'.notTaken c10 0x58 part_at_54 (by decide)
              (by rw [r8a1, r8s3]; exact hlo)
            obtain ⟨nb, db, ub⟩ := ua.taken c10 0x66 part_at_58 (by decide) (by rw [r8s2, r8a1]; exact hhi)
            exact ⟨nb, .cons da (.single db), ub⟩
          · obtain ⟨na, da, ua⟩ := u8'.taken c10 0x66 part_at_54 (by decide) (by rw [r8a1, r8s3]; exact hlo)
            exact ⟨na, .single da, ua⟩
        obtain ⟨na, da, ua⟩ := h66
        obtain ⟨nb, db, ub⟩ := ua.aluImm c10 part_at_66 (off' := 0x68) (by decide)
        obtain ⟨nc', dc, uc⟩ := ub.jump c10 part_at_68 (off' := 0x3C) (by decide)
          (by rw [ub.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x3C (by decide)))
        obtain ⟨nd, kd, pcd, memd, regsd⟩ := part_from3c uc c10 hbase c1057
          (by simp +decide [upd, r8sp]) hGa (by simp +decide [upd, r8s0]) O2 O257
        rw [show (upd (reg n8) a0 (aluEval .add (reg n8 x0) 5) a0).extractLsb' 0 8 = 5 by
          simp +decide [upd, aluEval, hz8]] at pcd memd regsd
        obtain ⟨A, B, C, D⟩ := finish nd _ _
          (fun k h1 h2 => by
            rw [memStore8_ne (outne0 k h2), memStore8_ne (outne1 k h2), m10slot k h1 h2])
          (keep_upd (keep_upd keep8' hz (by decide)) hz (by decide)) pcd memd regsd
          (fun x hx => by
            rw [memF x hx]; simp only [hc, ite_true]
            exact memStore8_congr (memStore8_congr (m10out x hx)))
        exact ⟨nd, pre _ (.cons d6 (.cons d7 (.cons d8 (da.trans (.cons db (.cons dc kd)))))), A, B, C, D⟩
      · -- The length is in range.
        have hlo : v2.ult lo = false := by
          cases h : v2.ult lo
          · rfl
          · simp [h] at hc
        have hhi : hi.ult v2 = false := by
          cases h : hi.ult v2
          · rfl
          · simp [h] at hc
        obtain ⟨na, da, ua⟩ := u8'.notTaken c10 0x58 part_at_54 (by decide) (by rw [r8a1, r8s3]; exact hlo)
        obtain ⟨nb, db, ub⟩ := ua.notTaken c10 0x5C part_at_58 (by decide) (by rw [r8s2, r8a1]; exact hhi)
        obtain ⟨nc', dc, uc⟩ := ub.aluImm c10 part_at_5c (off' := 0x5E) (by decide)
        have qc : ∀ r, r ≠ a0 → upd (reg n8) a0 (aluEval .add (reg n8 x0) 0) r = reg n8 r := fun r h => by
          by_cases hr : r.val = 0
          · have : r = 0 := Fin.ext hr
            subst this; simp [upd, hz8]
          · simp [upd, hr, h]
        obtain ⟨nd, dd, ud⟩ := uc.sw c10 part_at_5e (off' := 0x62) (by decide)
          (by rw [qc s0 (by decide), r8s0]; exact aligned_add hout (k := 4) (by decide))
        rw [qc s0 (by decide), qc s4 (by decide), r8s0, r8s4] at ud
        have O4 : Sep (out + 4) 4 base manifestPartCode.length := OP.sub (c := 4) (l := 4) (by omega)
        have O457 : Sep (out + 4) 4 (base + 0x129F4) partRestoreCode.length := O57.sub (c := 4) (l := 4) (by omega)
        have O8 : Sep (out + 8) 4 base manifestPartCode.length := OP.sub (c := 8) (l := 4) (by omega)
        have O857 : Sep (out + 8) 4 (base + 0x129F4) partRestoreCode.length := O57.sub (c := 8) (l := 4) (by omega)
        obtain ⟨ne, de, ue⟩ := ud.sw (c10.store32 O4) part_at_62 (off' := 0x64) (by decide)
          (by rw [qc s0 (by decide), r8s0]; exact aligned_add hout (k := 8) (by decide))
        rw [qc s0 (by decide), qc a1 (by decide), r8s0, r8a1] at ue
        have c11 := (c10.store32 (v := v1) O4).store32 (v := v2) O8
        obtain ⟨nf, df, uf⟩ := ue.jump c11 part_at_64 (off' := 0x42) (by decide)
          (by rw [ue.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x42 (by decide)))
        obtain ⟨ng, kg, pcg, memg, regsg⟩ := part_from42 uf c11 hbase
          ((c1057.store32 O457).store32 O857) (by rw [qc sp (by decide), r8sp]) hGa
          (by rw [qc s0 (by decide), r8s0]) O1 O157
        rw [show (upd (reg n8) a0 (aluEval .add (reg n8 x0) 0) a0).extractLsb' 0 8 = 0 by
          simp +decide [upd, aluEval, hz8]] at pcg memg regsg
        obtain ⟨A, B, C, D⟩ := finish ng _ _
          (fun k h1 h2 => by
            rw [memStore8_ne (outne0 k h2),
              memStore32_get_sep (show Sep (out + 8) 4 (G + BitVec.ofNat 32 k) 1 from
                (outG k h2).sub (c := 8) (l := 4) (by omega)),
              memStore32_get_sep (show Sep (out + 4) 4 (G + BitVec.ofNat 32 k) 1 from
                (outG k h2).sub (c := 4) (l := 4) (by omega)), m10slot k h1 h2])
          (keep_upd keep8' hz (by decide)) pcg memg regsg
          (fun x hx => by
            rw [memF x hx]; simp only [hc]
            exact memStore8_congr (memStore32_congr (memStore32_congr (m10out x hx))))
        exact ⟨ng, pre _ (.cons d6 (.cons d7 (.cons d8 (.cons da (.cons db (.cons dc (.cons dd
          (.cons de (.cons df kg))))))))), A, B, C, D⟩

end C3.RV32
