import C3BootProofs.Proofs.Reader
import C3BootProofs.Proof.Mem

/-!
# `c3_verify::reader::Reader::array::<4>`, as compiled

`Reader::array::<4>` calls `Reader::bytes` for 4 bytes and returns them as a
`Result<&[u8; 4], Error>`. The compiled function saves `ra`, `s0`, and `s1`
in a 32-byte stack frame, calls `bytes` with its result slot in the frame,
and writes its own result through `a0`: a tag byte (0 for `Ok`, 1 for
`Err`), the error byte at offset 1, and the array's address at offset 4.
`readerArray4_correct` proves it on the RV32 model, using
`readerBytes_correct` for the call: the first machine-code proof that
composes a call through the callee's theorem.
-/

namespace C3.RV32

open C3.Image

abbrev sp : Fin 32 := 2
abbrev s0 : Fin 32 := 8
abbrev s1 : Fin 32 := 9

/-- Memory after `Reader::array::<4>` returns, outside its stack frame. -/
def array4Mem (M : Word → BitVec 8) (out self : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with
  | none => memStore8 (memStore8 M (out + 1) 0) out 1
  | some (p, e) => memStore8 (memStore32 (memStore32 M (self + 8) e) (out + 4) p) out 0

theorem even_mask_bits : ∀ i, i < 32 → (4294967294 : Nat).testBit i = decide (i ≠ 0) := by
  decide

theorem even_clear (x : Word) (h : x.toNat % 2 = 0) : x &&& ~~~1 = x := by
  rw [show (~~~1 : Word) = 0xFFFFFFFE#32 from by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  show (x.toNat.testBit i && (4294967294 % 2 ^ 32).testBit i) = x.toNat.testBit i
  rw [show (4294967294 % 2 ^ 32 : Nat) = 4294967294 from rfl, even_mask_bits i hi]
  by_cases h0 : i = 0
  · subst h0
    rw [Nat.testBit_zero]
    simp [h]
  · simp [h0]

theorem memStore8_congr {M M' : Word → BitVec 8} {a x : Word} {v : BitVec 8} (h : M x = M' x) :
    memStore8 M a v x = memStore8 M' a v x := by
  unfold memStore8; split <;> simp_all

theorem memStore32_congr {M M' : Word → BitVec 8} {a x v : Word} (h : M x = M' x) :
    memStore32 M a v x = memStore32 M' a v x := by
  unfold memStore32
  exact memStore8_congr (memStore8_congr (memStore8_congr (memStore8_congr h)))

theorem CodeIn.ofBytesMem {M : Word → BitVec 8} {b out self n : Word} {code : List Nat}
    (hc : CodeIn M b code) (h1 : Sep out 8 b code.length) (h2 : Sep (self + 8) 4 b code.length) :
    CodeIn (bytesMem M out self n) b code := by
  have h0 : Sep out 4 b code.length := by
    have := h1.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  unfold bytesMem
  split
  · exact (hc.store32 h0).store8 (h1.sub (c := 4) (l := 1) (by omega))
  · exact ((hc.store32 h2).store32 h0).store32 (h1.sub (c := 4) (l := 4) (by omega))

theorem sep_out4 (out : Word) : Sep (out + 4) 4 out 4 := by
  have := sep_offsets out (c := 4) (n := 4) (d := 0) (k := 4) (by omega) (by omega) (by omega)
  rwa [add_ofNat_zero] at this

theorem sep_out4' (out : Word) : Sep (out + 4) 1 out 4 := by
  have := sep_offsets out (c := 4) (n := 1) (d := 0) (k := 4) (by omega) (by omega) (by omega)
  rwa [add_ofNat_zero] at this

/-- What the result slot holds after `Reader::bytes`. -/
theorem bytesMem_none {M : Word → BitVec 8} {out self n : Word}
    (h : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n = none) :
    memLoad32 (bytesMem M out self n) out = 0 ∧ bytesMem M out self n (out + 4) = 0 := by
  unfold bytesMem; rw [h]
  exact ⟨by rw [memLoad32_store8_sep (sep_out4' out), memLoad32_store32_same],
    memStore8_same _ _ _⟩

theorem bytesMem_some {M : Word → BitVec 8} {out self n p e : Word}
    (h : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n =
      some (p, e)) :
    memLoad32 (bytesMem M out self n) out = p ∧ memLoad32 (bytesMem M out self n) (out + 4) = n := by
  unfold bytesMem; rw [h]
  exact ⟨by rw [memLoad32_store32_sep (sep_out4 out), memLoad32_store32_same],
    memLoad32_store32_same _ _ _⟩

/-- Outside the result slot, `Reader::bytes` changes at most the reader's
position. -/
theorem bytesMem_outside {M : Word → BitVec 8} {out self n x : Word} (hx : Sep out 8 x 1) :
    bytesMem M out self n x =
      match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n with
      | none => M x
      | some (_, e) => memStore32 M (self + 8) e x := by
  have h0 : Sep out 4 x 1 := by
    have := hx.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have h4 : x ≠ out + 4 := fun e => hx 4 (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)
  unfold bytesMem
  rcases hres : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) n
    with _ | ⟨p, e⟩
  · dsimp only
    rw [memStore8_ne h4, memStore32_get_sep h0]
  · dsimp only
    rw [memStore32_get_sep (show Sep (out + 4) 4 x 1 from hx.sub (c := 4) (l := 4) (by omega)),
      memStore32_get_sep h0]

theorem ra4_at_00 : fetchRel readerArray4Code 0x00 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem ra4_at_02 : fetchRel readerArray4Code 0x02 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem ra4_at_04 : fetchRel readerArray4Code 0x04 = some (.store .sw sp s0 0x18, 2) := by decide
theorem ra4_at_06 : fetchRel readerArray4Code 0x06 = some (.store .sw sp s1 0x14, 2) := by decide
theorem ra4_at_08 : fetchRel readerArray4Code 0x08 = some (.alu .add s0 x0 a0, 2) := by decide
theorem ra4_at_0a : fetchRel readerArray4Code 0x0A = some (.aluImm .add a0 sp 0x0C, 2) := by decide
theorem ra4_at_0c : fetchRel readerArray4Code 0x0C = some (.aluImm .add a2 x0 4, 2) := by decide
theorem ra4_at_0e : fetchRel readerArray4Code 0x0E = some (.aluImm .add s1 x0 4, 2) := by decide
theorem ra4_at_10 : fetchRel readerArray4Code 0x10 = some (.auipc ra 0, 4) := by decide
theorem ra4_at_14 : fetchRel readerArray4Code 0x14 = some (.jalr ra ra 0xFFFFFF86, 4) := by decide
theorem ra4_at_18 : fetchRel readerArray4Code 0x18 = some (.load .lw a1 sp 0x0C, 2) := by decide
theorem ra4_at_1a : fetchRel readerArray4Code 0x1A = some (.branch .beq a1 x0 0x0E, 2) := by decide
theorem ra4_at_1c : fetchRel readerArray4Code 0x1C = some (.load .lw a0 sp 0x10, 2) := by decide
theorem ra4_at_1e : fetchRel readerArray4Code 0x1E = some (.branch .bne a0 s1 0x14, 4) := by decide
theorem ra4_at_22 : fetchRel readerArray4Code 0x22 = some (.aluImm .add a0 x0 0, 2) := by decide
theorem ra4_at_24 : fetchRel readerArray4Code 0x24 = some (.store .sw s0 a1 4, 2) := by decide
theorem ra4_at_26 : fetchRel readerArray4Code 0x26 = some (.jal x0 0x12, 2) := by decide
theorem ra4_at_28 : fetchRel readerArray4Code 0x28 = some (.load .lbu a0 sp 0x10, 4) := by decide
theorem ra4_at_2c : fetchRel readerArray4Code 0x2C = some (.store .sb s0 a0 1, 4) := by decide
theorem ra4_at_30 : fetchRel readerArray4Code 0x30 = some (.jal x0 6, 2) := by decide
theorem ra4_at_36 : fetchRel readerArray4Code 0x36 = some (.aluImm .add a0 x0 1, 2) := by decide
theorem ra4_at_38 : fetchRel readerArray4Code 0x38 = some (.store .sb s0 a0 0, 4) := by decide
theorem ra4_at_3c : fetchRel readerArray4Code 0x3C = some (.load .lw ra sp 0x1C, 2) := by decide
theorem ra4_at_3e : fetchRel readerArray4Code 0x3E = some (.load .lw s0 sp 0x18, 2) := by decide
theorem ra4_at_40 : fetchRel readerArray4Code 0x40 = some (.load .lw s1 sp 0x14, 2) := by decide
theorem ra4_at_42 : fetchRel readerArray4Code 0x42 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem ra4_at_44 : fetchRel readerArray4Code 0x44 = some (.jalr x0 ra 0, 2) := by decide

/-- The frame's stores: `ra`, `s0`, and `s1` at offsets 0x1C, 0x18, and 0x14. -/
def saves (M : Word → BitVec 8) (F r0 r8 r9 : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 M (F + 0x1C) r0) (F + 0x18) r8) (F + 0x14) r9

theorem ra4_prologue {m : Machine} {base : Word} (hc : CodeIn m.mem base readerArray4Code)
    (hpc : m.pc = base) (hsp : (reg m sp).toNat % 4 = 0)
    (hFc : Sep (reg m sp + 0xFFFFFFE0) 32 base readerArray4Code.length) :
    ∃ m' f', Steps m m' ∧
      St (saves m.mem (reg m sp + 0xFFFFFFE0) (reg m ra) (reg m s0) (reg m s1)) base m' 0x14 f' ∧
      f' sp = reg m sp + 0xFFFFFFE0 ∧ f' s0 = reg m a0 ∧ f' a0 = reg m sp + 0xFFFFFFE0 + 0x0C ∧
      f' a2 = 4 ∧ f' s1 = 4 ∧ f' ra = base + BitVec.ofNat 32 0x10 + 0 ∧ f' a1 = reg m a1 ∧
      ∀ r, r ≠ sp → r ≠ s0 → r ≠ a0 → r ≠ a2 → r ≠ s1 → r ≠ ra → f' r = reg m r := by
  have s0' : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  have hF : (reg m sp + 0xFFFFFFE0).toNat % 4 = 0 := aligned_add hsp (k := 0xFFFFFFE0) (by decide)
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc ra4_at_00 (off' := 0x02) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFE0 = reg m sp + 0xFFFFFFE0 from rfl] at t1
  obtain ⟨F, hFdef⟩ : ∃ F, reg m sp + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  rw [hFdef] at t1 hF hFc ⊢
  have q1 : ∀ r, upd (reg m) sp F r = if r = sp then F else reg m r := by
    intro r
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp +decide [upd, hz]
    · simp [upd, hr]
  obtain ⟨m2, e2, t2⟩ := t1.sw hc ra4_at_02 (off' := 0x04) (by decide)
    (by simp only [q1]; exact aligned_add hF (k := 0x1C) (by decide))
  have r1sp : upd (reg m) sp F sp = F := by simp [q1]
  rw [r1sp, show upd (reg m) sp F ra = reg m ra by simp +decide [q1]] at t2
  have hc2 := hc.store32 (v := reg m ra)
    (show Sep (F + 0x1C) 4 base _ from hFc.sub (c := 0x1C) (l := 4) (by omega))
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 ra4_at_04 (off' := 0x06) (by decide)
    (by rw [r1sp]; exact aligned_add hF (k := 0x18) (by decide))
  rw [r1sp, show upd (reg m) sp F s0 = reg m s0 by simp +decide [q1]] at t3
  have hc3 := hc2.store32 (v := reg m s0)
    (show Sep (F + 0x18) 4 base _ from hFc.sub (c := 0x18) (l := 4) (by omega))
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 ra4_at_06 (off' := 0x08) (by decide)
    (by rw [r1sp]; exact aligned_add hF (k := 0x14) (by decide))
  rw [r1sp, show upd (reg m) sp F s1 = reg m s1 by simp +decide [q1]] at t4
  have hc4 := hc3.store32 (v := reg m s1)
    (show Sep (F + 0x14) 4 base _ from hFc.sub (c := 0x14) (l := 4) (by omega))
  obtain ⟨m5, e5, t5⟩ := t4.alu hc4 ra4_at_08 (off' := 0x0A) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.aluImm hc4 ra4_at_0a (off' := 0x0C) (by decide)
  obtain ⟨m7, e7, t7⟩ := t6.aluImm hc4 ra4_at_0c (off' := 0x0E) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.aluImm hc4 ra4_at_0e (off' := 0x10) (by decide)
  obtain ⟨m9, e9, t9⟩ := t8.auipc hc4 ra4_at_10 (off' := 0x14) (by decide)
  refine ⟨m9, _, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
    (.single e9)))))))), t9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [upd]
  · simp +decide [upd, aluEval]
  · simp +decide [upd, aluEval]
  · simp +decide [upd, aluEval]
  · simp +decide [upd, aluEval]
  · simp +decide [upd]
  · simp +decide [upd]
  · intro r h1 h2 h3 h4 h5 h6
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [hz]
    · simp [upd, hr, h1, h2, h3, h4, h5, h6]

theorem ra4_call {m : Machine} {base bbase F self : Word} {f : Fin 32 → Word}
    {M : Word → BitVec 8} (hc : CodeIn M base readerArray4Code)
    (hbc : CodeIn M bbase readerBytesCode) (hb : bbase = base + 0xFFFFFF96)
    (hbase : base.toNat % 2 = 0) (t : St M base m 0x14 f) (hra : f ra = base + BitVec.ofNat 32 0x10 + 0)
    (ha0 : f a0 = F + 0x0C) (ha1 : f a1 = self) (ha2 : f a2 = 4) (hF : F.toNat % 4 = 0)
    (hself : self.toNat % 4 = 0) (hslot : Sep (F + 0x0C) 8 bbase readerBytesCode.length)
    (hSb : Sep (self + 8) 4 bbase readerBytesCode.length) :
    ∃ m', Steps m m' ∧ St (bytesMem M (F + 0x0C) self 4) base m' 0x18 (reg m') ∧
      ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m1, e1, pc1, mem1, regs1⟩ := t.call hc ra4_at_14
  have hsum : base + BitVec.ofNat 32 0x10 + 0 + 0xFFFFFF86 = bbase := by
    rw [hb, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hev : bbase.toNat % 2 = 0 := by
    rw [hb, BitVec.toNat_add, show (0xFFFFFF96 : Word).toNat = 0xFFFFFF96 from rfl]; omega
  have target : m1.pc = bbase := by rw [pc1, hra, hsum, even_clear _ hev]
  have hret0 : base + BitVec.ofNat 32 0x14 + 4 = base + BitVec.ofNat 32 0x18 :=
    add_ofNat_assoc base 0x14 4
  have hev2 : (base + BitVec.ofNat 32 0x18).toNat % 2 = 0 := by
    rw [BitVec.toNat_add]; have := base.isLt; simp only [BitVec.toNat_ofNat]; omega
  have r1 : ∀ r, reg m1 r = if r = ra then base + BitVec.ofNat 32 0x18 else f r := by
    intro r; rw [regs1, hret0]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp +decide [upd, hz]
    · simp [upd, hr]
  obtain ⟨m2, c2, pc2, mem2, regs2⟩ := readerBytes_correct m1 bbase (base + BitVec.ofNat 32 0x18)
    (F + 0x0C) self 4 (fun i hi => by rw [mem1]; exact hbc i hi) target
    (by rw [r1]; simp +decide [ha0]) (by rw [r1]; simp +decide [ha1]) (by rw [r1]; simp +decide [ha2])
    (by rw [r1]; simp) (even_clear _ hev2) (aligned_add hF (k := 0x0C) (by decide)) hself hslot hSb
  refine ⟨m2, .cons e1 c2, ⟨pc2, by rw [mem2, mem1], fun _ => rfl⟩, ?_⟩
  intro r r3 r4 r5 rr
  rw [regs2 r r3 r4 r5, r1]; simp [rr]


theorem CodeIn.saves {M : Word → BitVec 8} {b F r0 r8 r9 : Word} {code : List Nat}
    (hc : CodeIn M b code) (h : Sep F 32 b code.length) : CodeIn (saves M F r0 r8 r9) b code :=
  ((hc.store32 (show Sep (F + 0x1C) 4 b _ from h.sub (c := 0x1C) (l := 4) (by omega))).store32
    (show Sep (F + 0x18) 4 b _ from h.sub (c := 0x18) (l := 4) (by omega))).store32
    (show Sep (F + 0x14) 4 b _ from h.sub (c := 0x14) (l := 4) (by omega))

theorem saves_outside {M : Word → BitVec 8} {F r0 r8 r9 x : Word} (hx : Sep F 32 x 1) :
    saves M F r0 r8 r9 x = M x := by
  unfold saves
  rw [memStore32_get_sep (show Sep (F + 0x14) 4 x 1 from hx.sub (c := 0x14) (l := 4) (by omega)),
    memStore32_get_sep (show Sep (F + 0x18) 4 x 1 from hx.sub (c := 0x18) (l := 4) (by omega)),
    memStore32_get_sep (show Sep (F + 0x1C) 4 x 1 from hx.sub (c := 0x1C) (l := 4) (by omega))]

theorem saves_load {M : Word → BitVec 8} {F r0 r8 r9 a : Word} (h : Sep F 32 a 4) :
    memLoad32 (saves M F r0 r8 r9) a = memLoad32 M a := by
  unfold saves
  rw [memLoad32_store32_sep (show Sep (F + 0x14) 4 a 4 from h.sub (c := 0x14) (l := 4) (by omega)),
    memLoad32_store32_sep (show Sep (F + 0x18) 4 a 4 from h.sub (c := 0x18) (l := 4) (by omega)),
    memLoad32_store32_sep (show Sep (F + 0x1C) 4 a 4 from h.sub (c := 0x1C) (l := 4) (by omega))]

theorem sepF (F : Word) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 32)
    (hd : d + k ≤ 32) : Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 d) k :=
  sep_offsets F h (by omega) (by omega)

theorem saves_slots (M : Word → BitVec 8) (F r0 r8 r9 : Word) :
    memLoad32 (saves M F r0 r8 r9) (F + 0x1C) = r0 ∧
    memLoad32 (saves M F r0 r8 r9) (F + 0x18) = r8 ∧
    memLoad32 (saves M F r0 r8 r9) (F + 0x14) = r9 := by
  unfold saves
  refine ⟨?_, ?_, memLoad32_store32_same _ _ _⟩
  · rw [memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x1C) 4 from sepF F (c := 0x14) (n := 4) (d := 0x1C) (k := 4) (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (F + 0x18) 4 (F + 0x1C) 4 from sepF F (c := 0x18) (n := 4) (d := 0x1C) (k := 4) (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  · rw [memLoad32_store32_sep (show Sep (F + 0x14) 4 (F + 0x18) 4 from sepF F (c := 0x14) (n := 4) (d := 0x18) (k := 4) (by omega) (by omega) (by omega)),
      memLoad32_store32_same]

/-- A load outside the result slot after `Reader::bytes`. -/
theorem bytesMem_load {M : Word → BitVec 8} {out self n b : Word} (hx : Sep out 8 b 4)
    (hs : Sep (self + 8) 4 b 4) : memLoad32 (bytesMem M out self n) b = memLoad32 M b := by
  apply memLoad32_congr
  intro j hj
  rw [bytesMem_outside (fun i hi k hk => hx i hi j hj ∘ by
    intro e; have : k = 0 := by omega
    subst this; rwa [add_ofNat_zero] at e)]
  split
  · rfl
  · exact memStore32_get_sep (fun i hi k hk => hs i hi j hj ∘ by
      intro e; have : k = 0 := by omega
      subst this; rwa [add_ofNat_zero] at e)


theorem Sep.subR {a b : Word} {n k : Nat} (h : Sep a n b k) {c l : Nat} (hcl : c + l ≤ k) :
    Sep a n (b + BitVec.ofNat 32 c) l :=
  (h.symm.sub hcl).symm

theorem even_bit0 {x : Word} (h : x.toNat % 2 = 0) : x.getLsbD 0 = false := by
  show x.toNat.testBit 0 = false
  rw [Nat.testBit_zero]; simp [h]

theorem even_at (base : Word) (hbase : base.toNat % 2 = 0) (k : Nat) (hk : k % 2 = 0) :
    (base + BitVec.ofNat 32 k).toNat % 2 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := base.isLt; omega

theorem ra4_epilogue {m : Machine} {M : Word → BitVec 8} {f : Fin 32 → Word} {base F r0 r8 r9 : Word}
    (hc : CodeIn M base readerArray4Code) (t : St M base m 0x3C f) (hsp : f sp = F)
    (hF : F.toNat % 4 = 0) (h1 : memLoad32 M (F + 0x1C) = r0) (h2 : memLoad32 M (F + 0x18) = r8)
    (h3 : memLoad32 M (F + 0x14) = r9) (hret : r0 &&& ~~~1 = r0) :
    ∃ m', Steps m m' ∧ m'.pc = r0 ∧ m'.mem = M ∧ reg m' sp = F + 0x20 ∧ reg m' ra = r0 ∧
      reg m' s0 = r8 ∧ reg m' s1 = r9 ∧
      ∀ r, r ≠ sp → r ≠ ra → r ≠ s0 → r ≠ s1 → reg m' r = f r := by
  have hz := t.zero
  obtain ⟨m1, e1, t1⟩ := t.lw hc ra4_at_3c (off' := 0x3E) (by decide)
    (by rw [hsp]; exact aligned_add hF (k := 0x1C) (by decide))
  rw [hsp, h1] at t1
  have u1 : upd f ra r0 sp = F := by simp +decide [upd, hsp]
  obtain ⟨m2, e2, t2⟩ := t1.lw hc ra4_at_3e (off' := 0x40) (by decide)
    (by rw [u1]; exact aligned_add hF (k := 0x18) (by decide))
  rw [u1, h2] at t2
  have u2 : upd (upd f ra r0) s0 r8 sp = F := by simp +decide [upd, hsp]
  obtain ⟨m3, e3, t3⟩ := t2.lw hc ra4_at_40 (off' := 0x42) (by decide)
    (by rw [u2]; exact aligned_add hF (k := 0x14) (by decide))
  rw [u2, h3] at t3
  obtain ⟨m4, e4, t4⟩ := t3.aluImm hc ra4_at_42 (off' := 0x44) (by decide)
  obtain ⟨m5, e5, pc5, mem5, regs5⟩ := t4.jalr hc ra4_at_44
  refine ⟨m5, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.single e5)))), ?_, mem5, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc5]; simp +decide only [upd]; simpa using hret
  · rw [regs5]; simp +decide [upd, aluEval, hsp]
  · rw [regs5]; simp +decide [upd]
  · rw [regs5]; simp +decide [upd]
  · rw [regs5]; simp +decide [upd]
  · intro r h1' h2' h3' h4'
    rw [regs5]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [hz]
    · simp [upd, hr, h1', h2', h3', h4']

/-- **The compiled `Reader::array::<4>` is correct.** With its bytes at
`base` and `Reader::bytes`'s at `bbase`, where the image puts it, a result
address `out` in `a0` and a reader `self` in `a1` over a slice that is not
null and doesn't wrap, everything aligned, and its 32-byte stack frame, the
result, and the reader's position kept apart from each other and from both
functions' code, there is an execution that reaches the return address
with `sp`, `ra`, `s0`, and `s1` restored, every register but `a0` through
`a5` unchanged, and memory outside the frame exactly as `array4Mem` says. -/
theorem readerArray4_correct (m : Machine) (base bbase retAddr out self : Word)
    (hcode : CodeAt m base readerArray4Code) (hbcode : CodeAt m bbase readerBytesCode)
    (hb : bbase = base + 0xFFFFFF96) (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = self) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (hout : out.toNat % 4 = 0) (hself : self.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hFc : Sep (reg m sp + 0xFFFFFFE0) 32 base readerArray4Code.length)
    (hFb : Sep (reg m sp + 0xFFFFFFE0) 32 bbase readerBytesCode.length)
    (hOc : Sep out 8 base readerArray4Code.length)
    (hSc : Sep (self + 8) 4 base readerArray4Code.length)
    (hSb : Sep (self + 8) 4 bbase readerBytesCode.length)
    (hSF : Sep self 12 (reg m sp + 0xFFFFFFE0) 32)
    (hOF : Sep out 8 (reg m sp + 0xFFFFFFE0) 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFE0) 32 x 1 → m'.mem x = array4Mem m.mem out self x := by
  have hF : (reg m sp + 0xFFFFFFE0).toNat % 4 = 0 := aligned_add hsp (k := 0xFFFFFFE0) (by decide)
  obtain ⟨m9, f9, c9, t9, f9sp, f9s0, f9a0, f9a2, f9s1, f9ra, f9a1, f9fr⟩ :=
    ra4_prologue hcode hpc hsp hFc
  have hspF : reg m sp = reg m sp + 0xFFFFFFE0 + 0x20 := by
    rw [BitVec.add_assoc]; exact (BitVec.add_zero _).symm
  obtain ⟨F, hFdef⟩ : ∃ F, reg m sp + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  rw [hFdef] at hF hFc hFb hSF hOF t9 f9sp f9a0 hspF ⊢
  have hcA := CodeIn.saves (r0 := reg m ra) (r8 := reg m s0) (r9 := reg m s1) hcode hFc
  have hcB := CodeIn.saves (r0 := reg m ra) (r8 := reg m s0) (r9 := reg m s1) hbcode hFb
  obtain ⟨m11, c11, t11, f11fr⟩ := ra4_call hcA hcB hb hbase t9 f9ra f9a0 (by rw [f9a1, ha1]) f9a2
    hF hself (show Sep (F + 0x0C) 8 bbase _ from hFb.sub (c := 0x0C) (l := 8) (by omega)) hSb
  have hFS : Sep F 32 self 12 := hSF.symm
  have hL : ∀ c, c + 4 ≤ 12 → memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1))
      (self + BitVec.ofNat 32 c) = memLoad32 m.mem (self + BitVec.ofNat 32 c) :=
    fun c hc => saves_load (hFS.subR (c := c) (l := 4) hc)
  have hL0 : memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) self = memLoad32 m.mem self := by
    have := hL 0 (by omega); rwa [add_ofNat_zero] at this
  have hL4 : memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) (self + 4) =
      memLoad32 m.mem (self + 4) := hL 4 (by omega)
  have hL8 : memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) (self + 8) =
      memLoad32 m.mem (self + 8) := hL 8 (by omega)
  have hcC := hcA.ofBytesMem (out := F + 0x0C) (n := 4)
    (show Sep (F + 0x0C) 8 base _ from hFc.sub (c := 0x0C) (l := 8) (by omega)) hSc
  have q11 : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ s0 → r ≠ a0 → r ≠ a2 → r ≠ s1 →
      reg m11 r = reg m r := fun r h3 h4 h5 hra' hsp' hs0 ha0' ha2' hs1 => by
    rw [f11fr r h3 h4 h5 hra', f9fr r hsp' hs0 ha0' ha2' hs1 hra']
  have r11sp : reg m11 sp = F := by rw [f11fr sp (by decide) (by decide) (by decide) (by decide), f9sp]
  have r11s0 : reg m11 s0 = out := by
    rw [f11fr s0 (by decide) (by decide) (by decide) (by decide), f9s0, ha0]
  have r11s1 : reg m11 s1 = 4 := by rw [f11fr s1 (by decide) (by decide) (by decide) (by decide), f9s1]
  have hz11 := t11.zero
  have slotF : ∀ c, c + 4 ≤ 32 → c ≥ 0x14 →
      Sep (F + 0x0C) 8 (F + BitVec.ofNat 32 c) 4 := fun c h1 h2 =>
    sepF F (c := 0x0C) (n := 8) (d := c) (k := 4) (by omega) (by omega) h1
  have selfF : ∀ c, c + 4 ≤ 32 → Sep (self + 8) 4 (F + BitVec.ofNat 32 c) 4 := fun c h =>
    (hSF.sub (c := 8) (l := 4) (by omega)).subR (c := c) (l := 4) h
  have outF : ∀ o c, o + 4 ≤ 8 → c + 4 ≤ 32 → Sep (out + BitVec.ofNat 32 o) 4 (F + BitVec.ofNat 32 c) 4 :=
    fun o c h1 h2 => (hOF.sub (c := o) (l := 4) h1).subR (c := c) (l := 4) h2
  have outF1 : ∀ o c, o + 1 ≤ 8 → c + 4 ≤ 32 → Sep (out + BitVec.ofNat 32 o) 1 (F + BitVec.ofNat 32 c) 4 :=
    fun o c h1 h2 => (hOF.sub (c := o) (l := 1) h1).subR (c := c) (l := 4) h2
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  rcases hR : bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4))
    (memLoad32 m.mem (self + 8)) 4 with _ | ⟨p, e⟩
  · have hR3 : bytesResult (memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) self)
        (memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) (self + 4))
        (memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) (self + 8)) 4 = none := by
      rw [hL0, hL4, hL8]; exact hR
    obtain ⟨sl0, sl4⟩ := bytesMem_none (out := F + 0x0C) hR3
    obtain ⟨n1, d1, u1⟩ := t11.lw hcC ra4_at_18 (off' := 0x1A) (by decide)
      (by rw [r11sp]; exact aligned_add hF (k := 0x0C) (by decide))
    rw [r11sp, sl0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.taken hcC 0x28 ra4_at_1a (by decide)
      rfl
    obtain ⟨n3, d3, u3⟩ := u2.lbu hcC ra4_at_28 (off' := 0x2C) (by decide)
    have sp2 : upd (reg m11) a1 0 sp = F := by simp +decide [upd, r11sp]
    rw [sp2, show F + 0x10 = F + 0x0C + 4 from by rw [BitVec.add_assoc]; rfl, sl4] at u3
    obtain ⟨n4, d4, u4⟩ := u3.sb hcC ra4_at_2c (off' := 0x30) (by decide)
    rw [show upd (upd (reg m11) a1 0) a0 ((0 : BitVec 8).zeroExtend 32) s0 = out from by
        simp +decide [upd, r11s0],
      show (upd (upd (reg m11) a1 0) a0 ((0 : BitVec 8).zeroExtend 32) a0).extractLsb' 0 8 = 0 from by
        simp +decide [upd]] at u4
    have hcD := hcC.store8 (a := out + 1) (v := 0)
      (show Sep (out + 1) 1 base _ from hOc.sub (c := 1) (l := 1) (by omega))
    obtain ⟨n5, d5, u5⟩ := u4.jump hcD ra4_at_30 (off' := 0x36) (by decide)
      (by rw [u4.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x36 (by decide)))
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hcD ra4_at_36 (off' := 0x38) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.sb hcD ra4_at_38 (off' := 0x3C) (by decide)
    rw [show upd (upd (upd (reg m11) a1 0) a0 ((0 : BitVec 8).zeroExtend 32)) a0
        (aluEval .add (upd (upd (reg m11) a1 0) a0 ((0 : BitVec 8).zeroExtend 32) x0) 1) s0 = out from by
        simp +decide [upd, r11s0],
      show (upd (upd (upd (reg m11) a1 0) a0 ((0 : BitVec 8).zeroExtend 32)) a0
        (aluEval .add (upd (upd (reg m11) a1 0) a0 ((0 : BitVec 8).zeroExtend 32) x0) 1) a0).extractLsb' 0 8
          = 1 from by simp +decide [upd, aluEval],
      add_lit_zero] at u7
    have hcE := hcD.store8 (a := out) (v := 1)
      (by have := hOc.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this)
    have ld : ∀ c, c + 4 ≤ 32 → c ≥ 0x14 →
        memLoad32 (memStore8 (memStore8 (bytesMem (saves m.mem F (reg m ra) (reg m s0) (reg m s1))
          (F + 0x0C) self 4) (out + 1) 0) out 1) (F + BitVec.ofNat 32 c) =
        memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) (F + BitVec.ofNat 32 c) := by
      intro c h1 h2
      rw [memLoad32_store8_sep (by have := outF1 0 c (by omega) h1; rwa [add_ofNat_zero] at this),
        memLoad32_store8_sep (show Sep (out + 1) 1 _ 4 from outF1 1 c (by omega) h1),
        bytesMem_load (slotF c h1 h2) (selfF c h1)]
    obtain ⟨sl1, sl2, sl3⟩ := saves_slots m.mem F (reg m ra) (reg m s0) (reg m s1)
    obtain ⟨n8, c8, pc8, mem8, sp8, ra8, s08, s18, fr8⟩ := ra4_epilogue (r0 := reg m ra)
      (r8 := reg m s0) (r9 := reg m s1) hcE u7 (by simp +decide [upd, r11sp]) hF
      (by rw [show F + 0x1C = F + BitVec.ofNat 32 0x1C from rfl, ld 0x1C (by omega) (by omega)]; exact sl1)
      (by rw [show F + 0x18 = F + BitVec.ofNat 32 0x18 from rfl, ld 0x18 (by omega) (by omega)]; exact sl2)
      (by rw [show F + 0x14 = F + BitVec.ofNat 32 0x14 from rfl, ld 0x14 (by omega) (by omega)]; exact sl3)
      hret'
    refine ⟨n8, c9.trans (c11.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6
      (.cons d7 c8)))))))), by rw [pc8, hra], by rw [sp8, ← hspF], ?_, ?_⟩
    · intro r r0 r1 r2 r3 r4 r5
      by_cases hsp' : r = sp
      · subst hsp'; rw [sp8, ← hspF]
      by_cases hra' : r = ra
      · subst hra'; exact ra8
      by_cases hs0 : r = s0
      · subst hs0; exact s08
      by_cases hs1 : r = s1
      · subst hs1; exact s18
      rw [fr8 r hsp' hra' hs0 hs1]
      have hz' : r.val ≠ 0 ∨ r = 0 := by
        by_cases h : r.val = 0
        · exact Or.inr (Fin.ext h)
        · exact Or.inl h
      rcases hz' with hnz | rfl
      · simp [upd, hnz, r0, r1]
        exact q11 r r3 r4 r5 hra' hsp' hs0 r0 r2 hs1
      · simp; rfl
    · intro x hx
      rw [mem8]
      unfold array4Mem
      rw [hR]
      dsimp only
      apply memStore8_congr
      apply memStore8_congr
      rw [bytesMem_outside (show Sep (F + 0x0C) 8 x 1 from hx.sub (c := 0x0C) (l := 8) (by omega)),
        hR3]
      exact saves_outside hx
  · have hR3 : bytesResult (memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) self)
        (memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) (self + 4))
        (memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) (self + 8)) 4 = some (p, e) := by
      rw [hL0, hL4, hL8]; exact hR
    obtain ⟨sl0, sl4⟩ := bytesMem_some (out := F + 0x0C) hR3
    have hp : p ≠ 0 := by
      rw [bytesResult_eq] at hR
      split at hR
      · rename_i hle
        simp only [Option.some.injEq, Prod.mk.injEq] at hR
        obtain ⟨hp1, -⟩ := hR
        rw [← hp1]
        intro h0
        have h1 := congrArg BitVec.toNat h0
        rw [BitVec.toNat_add] at h1
        have hne : (memLoad32 m.mem self).toNat ≠ 0 := fun h =>
          hbuf.1 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        have h2 := hbuf.2
        rw [show (4 : Word).toNat = 4 from rfl] at hle
        have h3 : (0 : Word).toNat = 0 := rfl
        omega
      · cases hR
    obtain ⟨n1, d1, u1⟩ := t11.lw hcC ra4_at_18 (off' := 0x1A) (by decide)
      (by rw [r11sp]; exact aligned_add hF (k := 0x0C) (by decide))
    rw [r11sp, sl0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.notTaken hcC 0x1C ra4_at_1a (by decide)
      (by simp +decide [upd, branchTaken]; exact hp)
    obtain ⟨n3, d3, u3⟩ := u2.lw hcC ra4_at_1c (off' := 0x1E) (by decide)
      (by simp +decide only [upd, r11sp]; exact aligned_add hF (k := 0x10) (by decide))
    have sp2 : upd (reg m11) a1 p sp = F := by simp +decide [upd, r11sp]
    rw [sp2, show F + 0x10 = F + 0x0C + 4 from by rw [BitVec.add_assoc]; rfl, sl4] at u3
    obtain ⟨n4, d4, u4⟩ := u3.notTaken hcC 0x22 ra4_at_1e (by decide)
      (by simp +decide [upd, branchTaken, r11s1])
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hcC ra4_at_22 (off' := 0x24) (by decide)
    obtain ⟨n6, d6, u6⟩ := u5.sw hcC ra4_at_24 (off' := 0x26) (by decide)
      (by simp +decide only [upd, r11s0]; exact aligned_add hout (k := 4) (by decide))
    rw [show upd (upd (upd (reg m11) a1 p) a0 4) a0 (aluEval .add (upd (upd (reg m11) a1 p) a0 4 x0) 0)
        s0 = out from by simp +decide [upd, r11s0],
      show upd (upd (upd (reg m11) a1 p) a0 4) a0 (aluEval .add (upd (upd (reg m11) a1 p) a0 4 x0) 0)
        a1 = p from by simp +decide [upd]] at u6
    have hcD := hcC.store32 (a := out + 4) (v := p)
      (show Sep (out + 4) 4 base _ from hOc.sub (c := 4) (l := 4) (by omega))
    obtain ⟨n7, d7, u7⟩ := u6.jump hcD ra4_at_26 (off' := 0x38) (by decide)
      (by rw [u6.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x38 (by decide)))
    obtain ⟨n8, d8, u8⟩ := u7.sb hcD ra4_at_38 (off' := 0x3C) (by decide)
    rw [show upd (upd (upd (reg m11) a1 p) a0 4) a0 (aluEval .add (upd (upd (reg m11) a1 p) a0 4 x0) 0)
        s0 = out from by simp +decide [upd, r11s0],
      show (upd (upd (upd (reg m11) a1 p) a0 4) a0 (aluEval .add (upd (upd (reg m11) a1 p) a0 4 x0) 0)
        a0).extractLsb' 0 8 = 0 from by simp +decide [upd, aluEval],
      add_lit_zero] at u8
    have hcE := hcD.store8 (a := out) (v := 0)
      (by have := hOc.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this)
    have ld : ∀ c, c + 4 ≤ 32 → c ≥ 0x14 →
        memLoad32 (memStore8 (memStore32 (bytesMem (saves m.mem F (reg m ra) (reg m s0) (reg m s1))
          (F + 0x0C) self 4) (out + 4) p) out 0) (F + BitVec.ofNat 32 c) =
        memLoad32 (saves m.mem F (reg m ra) (reg m s0) (reg m s1)) (F + BitVec.ofNat 32 c) := by
      intro c h1 h2
      rw [memLoad32_store8_sep (by have := outF1 0 c (by omega) h1; rwa [add_ofNat_zero] at this),
        memLoad32_store32_sep (show Sep (out + 4) 4 _ 4 from outF 4 c (by omega) h1),
        bytesMem_load (slotF c h1 h2) (selfF c h1)]
    obtain ⟨sl1, sl2, sl3⟩ := saves_slots m.mem F (reg m ra) (reg m s0) (reg m s1)
    obtain ⟨n9, c9', pc9, mem9, sp9, ra9, s09, s19, fr9⟩ := ra4_epilogue (r0 := reg m ra)
      (r8 := reg m s0) (r9 := reg m s1) hcE u8 (by simp +decide [upd, r11sp]) hF
      (by rw [show F + 0x1C = F + BitVec.ofNat 32 0x1C from rfl, ld 0x1C (by omega) (by omega)]; exact sl1)
      (by rw [show F + 0x18 = F + BitVec.ofNat 32 0x18 from rfl, ld 0x18 (by omega) (by omega)]; exact sl2)
      (by rw [show F + 0x14 = F + BitVec.ofNat 32 0x14 from rfl, ld 0x14 (by omega) (by omega)]; exact sl3)
      hret'
    refine ⟨n9, c9.trans (c11.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6
      (.cons d7 (.cons d8 c9'))))))))), by rw [pc9, hra], by rw [sp9, ← hspF], ?_, ?_⟩
    · intro r r0 r1 r2 r3 r4 r5
      by_cases hsp' : r = sp
      · subst hsp'; rw [sp9, ← hspF]
      by_cases hra' : r = ra
      · subst hra'; exact ra9
      by_cases hs0 : r = s0
      · subst hs0; exact s09
      by_cases hs1 : r = s1
      · subst hs1; exact s19
      rw [fr9 r hsp' hra' hs0 hs1]
      have hz' : r.val ≠ 0 ∨ r = 0 := by
        by_cases h : r.val = 0
        · exact Or.inr (Fin.ext h)
        · exact Or.inl h
      rcases hz' with hnz | rfl
      · simp [upd, hnz, r0, r1]
        exact q11 r r3 r4 r5 hra' hsp' hs0 r0 r2 hs1
      · simp; rfl
    · intro x hx
      rw [mem9]
      unfold array4Mem
      rw [hR]
      dsimp only
      apply memStore8_congr
      apply memStore32_congr
      rw [bytesMem_outside (show Sep (F + 0x0C) 8 x 1 from hx.sub (c := 0x0C) (l := 8) (by omega)),
        hR3]
      exact memStore32_congr (saves_outside hx)

end C3.RV32
