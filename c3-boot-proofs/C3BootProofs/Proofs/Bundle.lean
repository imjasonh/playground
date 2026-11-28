import C3BootProofs.Proofs.ReaderU32Cur
import C3BootProofs.Proofs.ImageHelpers
import C3BootProofs.Proofs.SmallFns
import C3BootProofs.Proofs.ReaderArray

/-!
# `c3_verify::bundle::field`

`bundle::field(r, lo, hi)` reads a 4-byte length with `Reader::u32`, checks
it against `lo..=hi`, and takes that many bytes with `Reader::bytes`, as
`Result<&[u8], Error>`: a pointer, null for `Err`, and the length or the
error byte. A length outside the range is `OutOfRange` (5).
-/

namespace C3.RV32

open C3.Image

/-- Memory after `bundle::field` returns, outside the stack it uses. -/
def fieldMem (M : Word → BitVec 8) (out self lo hi : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 with
  | none => memStore8 (memStore32 M out 0) (out + 4) 0
  | some (p, e) =>
    if lo.toNat ≤ (memLoad32 M p).toNat ∧ (memLoad32 M p).toNat ≤ hi.toNat then
      bytesMem (memStore32 M (self + 8) e) out self (memLoad32 M p)
    else memStore8 (memStore32 (memStore32 M (self + 8) e) out 0) (out + 4) 5

theorem u32MemCur_none {M : Word → BitVec 8} {out self : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 = none) :
    Cur.u32Mem M out self out = 1 ∧ Cur.u32Mem M out self (out + 1) = 0 ∧
    ∀ x, x ≠ out → x ≠ out + 1 → Cur.u32Mem M out self x = M x := by
  have n10 : out + 1 ≠ out := by
    have := add_ofNat_ne out (c := 1) (d := 0) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  unfold Cur.u32Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, by rw [memStore8_ne n10, memStore8_same], fun x h1 h2 => ?_⟩
  rw [memStore8_ne h1, memStore8_ne h2]

theorem u32MemCur_some {M : Word → BitVec 8} {out self p e : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 = some (p, e)) :
    Cur.u32Mem M out self out = 0 ∧ memLoad32 (Cur.u32Mem M out self) (out + 4) = memLoad32 M p ∧
    ∀ x, x ≠ out → Sep (out + 4) 4 x 1 → Cur.u32Mem M out self x = memStore32 M (self + 8) e x := by
  unfold Cur.u32Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, ?_, fun x h1 h2 => ?_⟩
  · rw [memLoad32_store8_sep (by
      have := sep_offsets out (c := 0) (n := 1) (d := 4) (k := 4) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this), memLoad32_store32_same]
  · rw [memStore8_ne h1, memStore32_get_sep h2]

theorem bfl_at_0 : fetchRel bundleFieldCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem bfl_at_2 : fetchRel bundleFieldCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem bfl_at_4 : fetchRel bundleFieldCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem bfl_at_6 : fetchRel bundleFieldCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem bfl_at_8 : fetchRel bundleFieldCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem bfl_at_a : fetchRel bundleFieldCode 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem bfl_at_c : fetchRel bundleFieldCode 0xC = some (.alu .add (18 : Fin 32) x0 a3, 2) := by decide
theorem bfl_at_e : fetchRel bundleFieldCode 0xE = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem bfl_at_10 : fetchRel bundleFieldCode 0x10 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem bfl_at_12 : fetchRel bundleFieldCode 0x12 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem bfl_at_14 : fetchRel bundleFieldCode 0x14 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem bfl_at_16 : fetchRel bundleFieldCode 0x16 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem bfl_at_1a : fetchRel bundleFieldCode 0x1A = some (.jalr ra ra 0xFFFFFF9A, 4) := by decide
theorem bfl_at_1e : fetchRel bundleFieldCode 0x1E = some (.load .lbu a0 sp 0x4, 4) := by decide
theorem bfl_at_22 : fetchRel bundleFieldCode 0x22 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem bfl_at_24 : fetchRel bundleFieldCode 0x24 = some (.load .lbu a0 sp 0x5, 4) := by decide
theorem bfl_at_28 : fetchRel bundleFieldCode 0x28 = some (.jal x0 0x26, 2) := by decide
theorem bfl_at_2a : fetchRel bundleFieldCode 0x2A = some (.load .lw a2 sp 0x8, 2) := by decide
theorem bfl_at_2c : fetchRel bundleFieldCode 0x2C = some (.branch .bltu a2 (19 : Fin 32) 0x20, 4) := by decide
theorem bfl_at_30 : fetchRel bundleFieldCode 0x30 = some (.branch .bltu (18 : Fin 32) a2 0x1C, 4) := by decide
theorem bfl_at_34 : fetchRel bundleFieldCode 0x34 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem bfl_at_36 : fetchRel bundleFieldCode 0x36 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem bfl_at_38 : fetchRel bundleFieldCode 0x38 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem bfl_at_3a : fetchRel bundleFieldCode 0x3A = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem bfl_at_3c : fetchRel bundleFieldCode 0x3C = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem bfl_at_3e : fetchRel bundleFieldCode 0x3E = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem bfl_at_40 : fetchRel bundleFieldCode 0x40 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem bfl_at_42 : fetchRel bundleFieldCode 0x42 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem bfl_at_44 : fetchRel bundleFieldCode 0x44 = some (.auipc (6 : Fin 32) 0xFFFFD000, 4) := by decide
theorem bfl_at_48 : fetchRel bundleFieldCode 0x48 = some (.jalr x0 (6 : Fin 32) 0xFFFFFF46, 4) := by decide
theorem bfl_at_4c : fetchRel bundleFieldCode 0x4C = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem bfl_at_4e : fetchRel bundleFieldCode 0x4E = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem bfl_at_52 : fetchRel bundleFieldCode 0x52 = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem bfl_at_56 : fetchRel bundleFieldCode 0x56 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem bfl_at_58 : fetchRel bundleFieldCode 0x58 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem bfl_at_5a : fetchRel bundleFieldCode 0x5A = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem bfl_at_5c : fetchRel bundleFieldCode 0x5C = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem bfl_at_5e : fetchRel bundleFieldCode 0x5E = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem bfl_at_60 : fetchRel bundleFieldCode 0x60 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem bfl_at_62 : fetchRel bundleFieldCode 0x62 = some (.jalr x0 ra 0x0, 2) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`bundle::field`, as compiled**: with `Reader::u32`, `Reader::array::<4>`,
and `Reader::bytes` where the image puts them, a reader `self` over a slice
that is not null and doesn't wrap, a result address `out`, and 80 bytes of
stack below `sp`, all apart as the hypotheses list, it returns to `ra` with
the registers but `a0` through `a5` and `t1` restored, and memory outside its
stack as `fieldMem` says. -/
theorem bundleField_correct (m : Machine) {base retAddr out self lo hi : Word}
    (hc : CodeIn m.mem base bundleFieldCode) (hu : CodeIn m.mem (base + 0xFFFFCFB0) readerU32Code)
    (ha : CodeIn m.mem (base + 0xFFFFCFB0 + 0x50) readerArray4Code)
    (hb : CodeIn m.mem (base + 0xFFFFCF8A) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = self)
    (ha2 : reg m a2 = lo) (ha3 : reg m a3 = hi)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hself : self.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSc : Sep (reg m sp + 0xFFFFFFB0) 80 base bundleFieldCode.length)
    (hSu : Sep (reg m sp + 0xFFFFFFB0) 80 (base + 0xFFFFCFB0) readerU32Code.length)
    (hSa : Sep (reg m sp + 0xFFFFFFB0) 80 (base + 0xFFFFCFB0 + 0x50) readerArray4Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFB0) 80 (base + 0xFFFFCF8A) readerBytesCode.length)
    (hOc : Sep out 8 base bundleFieldCode.length) (hOb : Sep out 8 (base + 0xFFFFCF8A) readerBytesCode.length)
    (hEu : Sep (self + 8) 4 (base + 0xFFFFCFB0) readerU32Code.length)
    (hEa : Sep (self + 8) 4 (base + 0xFFFFCFB0 + 0x50) readerArray4Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xFFFFCF8A) readerBytesCode.length)
    (hEc : Sep (self + 8) 4 base bundleFieldCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFB0) 80) (hOS : Sep out 8 (reg m sp + 0xFFFFFFB0) 80)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFB0) 80)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 6 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFB0) 80 x 1 → m'.mem x = fieldMem m.mem out self lo hi x := by
  have hbu : base + 0xFFFFCFB0 + 0x50 + 0xFFFFFF8A = base + 0xFFFFCF8A := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨S, hSd⟩ : ∃ S, reg m sp + 0xFFFFFFB0 = S := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFFE0 = G := ⟨_, rfl⟩
  rw [hSd] at hSc hSu hSa hSb hRS hOS hBS ⊢
  obtain ⟨ptr, hptr⟩ : ∃ ptr, memLoad32 m.mem self = ptr := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, memLoad32 m.mem (self + 4) = len := ⟨_, rfl⟩
  rw [hptr, hlen] at hbuf hBS hBE
  have hGS : G = S + BitVec.ofNat 32 48 := by rw [← hGd, ← hSd, BitVec.add_assoc]; rfl
  have hSG : G + 0xFFFFFFD0 = S := by rw [← hGd, ← hSd, BitVec.add_assoc]; rfl
  have hspG : G + 0x20 = reg m sp := by rw [← hGd, BitVec.add_assoc]; exact BitVec.add_zero _
  have hGa : G.toNat % 4 = 0 := hGd ▸ aligned_add hsp (k := 0xFFFFFFE0) (by decide)
  have fr : ∀ c l, c + l ≤ 32 → ∀ (x : Word) (n : Nat), Sep S 80 x n → Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := 48 + c) (l := l) (by omega)
  have s48 : ∀ (x : Word) (n : Nat), Sep S 80 x n → Sep (G + 0xFFFFFFD0) 48 x n := fun x n hx => by
    rw [hSG]; have := hx.sub (c := 0) (l := 48) (by omega); rwa [add_ofNat_zero] at this
  have s48R : ∀ {a : Word} {n : Nat}, Sep a n S 80 → Sep a n (G + 0xFFFFFFD0) 48 := fun h => by
    rw [hSG]; have := h.subR (c := 0) (l := 48) (by omega); rwa [add_ofNat_zero] at this
  have inG : ∀ c, c < 32 → Sep (G + 0xFFFFFFD0) 48 (G + BitVec.ofNat 32 c) 1 := fun c hc' => by
    rw [hSG, hGS, add_ofNat_assoc]
    have := sep_offsets S (c := 0) (n := 48) (d := 48 + c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc bfl_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFE0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc bfl_at_2 (off' := 4) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x1C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (fr 0x1C 4 (by omega) _ _ hSc)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 bfl_at_4 (off' := 6) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x18) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (fr 0x18 4 (by omega) _ _ hSc)
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 bfl_at_6 (off' := 8) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x14) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  have hc4 := hc3.store32 (v := reg m 9) (fr 0x14 4 (by omega) _ _ hSc)
  obtain ⟨m5, e5, t5⟩ := t4.sw hc4 bfl_at_8 (off' := 0xA) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x10) (by decide))
  rw [u1sp, f1 18 (by decide)] at t5
  have hc5 := hc4.store32 (v := reg m 18) (fr 0x10 4 (by omega) _ _ hSc)
  obtain ⟨m6, e6, t6⟩ := t5.sw hc5 bfl_at_a (off' := 0xC) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [u1sp, f1 19 (by decide)] at t6
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 m.mem (G + 0x1C) (reg m ra))
      (G + 0x18) (reg m 8)) (G + 0x14) (reg m 9)) (G + 0x10) (reg m 18)) (G + 0xC) (reg m 19) = M5 := ⟨_, rfl⟩
  rw [hM5] at t6
  have M5out : ∀ x, Sep S 80 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5]
    exact (memStore32_get_sep (fr 0xC 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x10 4 (by omega) x 1 hx)).trans
      ((memStore32_get_sep (fr 0x14 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x18 4 (by omega) x 1 hx)).trans
      (memStore32_get_sep (fr 0x1C 4 (by omega) x 1 hx)))))
  have codeOut : ∀ {b : Word} {code : List Nat}, Sep S 80 b code.length → CodeIn m.mem b code → CodeIn M5 b code :=
    fun h hc' i hi => by rw [M5out _ (h.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have hc6 := codeOut hSc hc
  have ldS : ∀ c, c + 4 ≤ 12 → memLoad32 M5 (self + BitVec.ofNat 32 c) = memLoad32 m.mem (self + BitVec.ofNat 32 c) :=
    fun c hc' => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact M5out _ ((hRS.sub (c := c + j) (l := 1) (by omega)).symm)
  have l0 : memLoad32 M5 self = ptr := by have := ldS 0 (by omega); rwa [add_ofNat_zero, hptr] at this
  have l4 : memLoad32 M5 (self + 4) = len := (ldS 4 (by omega)).trans hlen
  have l8 : memLoad32 M5 (self + 8) = memLoad32 m.mem (self + 8) := ldS 8 (by omega)
  have fA : memLoad32 M5 (G + 0x1C) = reg m ra := by
    rw [← hM5]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fB : memLoad32 M5 (G + 0x18) = reg m 8 := by
    rw [← hM5]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fC : memLoad32 M5 (G + 0x14) = reg m 9 := by
    rw [← hM5]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fD : memLoad32 M5 (G + 0x10) = reg m 18 := by
    rw [← hM5]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x10) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fE : memLoad32 M5 (G + 0xC) = reg m 19 := by rw [← hM5]; exact memLoad32_store32_same _ _ _
  obtain ⟨m7, e7, t7⟩ := t6.alu hc6 bfl_at_c (off' := 0xE) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.alu hc6 bfl_at_e (off' := 0x10) (by decide)
  obtain ⟨m9, e9, t9⟩ := t8.alu hc6 bfl_at_10 (off' := 0x12) (by decide)
  obtain ⟨m10, e10, t10⟩ := t9.alu hc6 bfl_at_12 (off' := 0x14) (by decide)
  obtain ⟨m11, e11, t11⟩ := t10.aluImm hc6 bfl_at_14 (off' := 0x16) (by decide)
  obtain ⟨m12, c12, pc12, mem12, regs12⟩ := t11.callRa (cb := base + 0xFFFFCFB0) hc6 bfl_at_16 bfl_at_1a
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xFFFFCFB0 (by decide))
  have sp12 : reg m12 sp = G := by rw [regs12]; simp +decide [upd]
  have a012 : reg m12 a0 = G + 4 := by rw [regs12]; simp +decide [upd, aluEval]
  have a112 : reg m12 a1 = self := by rw [regs12]; simp +decide [upd, ha1]
  have s012 : reg m12 8 = out := by rw [regs12]; simp +decide [upd, aluEval, ha0]
  have s112 : reg m12 9 = self := by rw [regs12]; simp +decide [upd, aluEval, ha1]
  have s212 : reg m12 18 = hi := by rw [regs12]; simp +decide [upd, aluEval, ha3]
  have s312 : reg m12 19 = lo := by rw [regs12]; simp +decide [upd, aluEval, ha2]
  have ra12 : reg m12 ra = base + BitVec.ofNat 32 (0x16 + 8) := by rw [regs12]; simp +decide [upd]
  have keep12 : ∀ r, r ≠ a0 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → reg m12 r = reg m r :=
    fun r h0 h1 h2 h3 h4 h5 h6 => by
      rw [regs12]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1, h2, h3, h4, h5, h6]
  have hO8 : Sep (G + 4) 8 (G + 0xFFFFFFD0) 48 := by
    rw [hSG]; show Sep (G + BitVec.ofNat 32 4) 8 S 48; rw [hGS, add_ofNat_assoc]
    have := sep_offsets S (c := 48 + 4) (n := 8) (d := 0) (k := 48) (Or.inr (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  obtain ⟨m13, c13, pc13, sp13, k13, mem13⟩ := Cur.readerU32_correct m12 (base + 0xFFFFCFB0)
    (base + BitVec.ofNat 32 (0x16 + 8)) (G + 4) self
    (by show CodeIn m12.mem _ _; rw [mem12]; exact codeOut hSu hu)
    (by show CodeIn m12.mem _ _; rw [mem12]; exact codeOut hSa ha)
    (by show CodeIn m12.mem _ _; rw [mem12, hbu]; exact codeOut hSb hb)
    (even_at base hbase 0xFFFFCFB0 (by decide)) pc12 a012 a112 ra12
    (even_clear _ (even_at base hbase (0x16 + 8) (by decide)))
    (by rw [sp12]; exact hGa) (aligned_add hGa (k := 4) (by decide)) hself (by rw [mem12, l0, l4]; exact hbuf)
    (by rw [sp12]; exact s48 _ _ hSu) (by rw [sp12]; exact s48 _ _ hSa) (by rw [sp12, hbu]; exact s48 _ _ hSb)
    (fr 4 8 (by omega) _ _ hSu) hEu hEa (by rw [hbu]; exact hEb)
    (by rw [sp12]; exact s48R hRS) (by rw [sp12]; exact hO8) (by rw [mem12, l0, l4, sp12]; exact s48R hBS)
    (by rw [mem12, l0, l4]; exact hBE)
  rw [sp12, mem12] at mem13
  rw [sp12] at sp13
  have hR : bytesResult (memLoad32 M5 self) (memLoad32 M5 (self + 4)) (memLoad32 M5 (self + 8)) 4 =
      bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 := by rw [l0, l4, l8]
  have uOut : ∀ x, Sep (G + 4) 8 x 1 → Sep (self + 8) 4 x 1 → Cur.u32Mem M5 (G + 4) self x = M5 x := fun x h1 h2 => by
    have n0 : x ≠ G + 4 := fun e => h1 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
    have n1 : x ≠ G + 4 + 1 := fun e => h1 1 (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)
    have s4 : Sep (G + 4 + 4) 4 x 1 := h1.sub (c := 4) (l := 4) (by omega)
    rcases hb' : bytesResult (memLoad32 M5 self) (memLoad32 M5 (self + 4)) (memLoad32 M5 (self + 8)) 4 with _ | ⟨q, e'⟩
    · exact (u32MemCur_none hb').2.2 x n0 n1
    · exact ((u32MemCur_some hb').2.2 x n0 s4).trans (memStore32_get_sep h2)
  have frm8 : ∀ c, 0xC ≤ c → c + 1 ≤ 0x20 → Sep (G + 4) 8 (G + BitVec.ofNat 32 c) 1 := fun c h1 h2 => by
    show Sep (G + BitVec.ofNat 32 4) 8 _ 1
    exact sep_offsets G (c := 4) (n := 8) (d := c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
  have frE : ∀ c, 0xC ≤ c → c + 1 ≤ 0x20 → Sep (self + 8) 4 (G + BitVec.ofNat 32 c) 1 := fun c h1 h2 => by
    rw [hGS, add_ofNat_assoc]; exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 48 + c) (l := 1) (by omega)
  have fr13 : ∀ c, 0xC ≤ c → c + 4 ≤ 0x20 → memLoad32 m13.mem (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, mem13 _ (inG (c + j) (by omega))]
      exact uOut _ (frm8 (c + j) (by omega) (by omega)) (frE (c + j) (by omega) (by omega))
  have outX : ∀ x, Sep S 80 x 1 → Sep (G + 4) 8 x 1 := fun x hx => fr 4 8 (by omega) x 1 hx
  have m13x : ∀ x, Sep S 80 x 1 → m13.mem x =
      match bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 with
      | none => m.mem x
      | some (_, e) => memStore32 m.mem (self + 8) e x := fun x hx => by
    rw [mem13 x (s48 _ _ hx)]
    unfold Cur.u32Mem; rw [hR]
    have n0 : x ≠ G + 4 := fun e => outX x hx 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
    have n1 : x ≠ G + 4 + 1 := fun e => outX x hx 1 (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)
    have s4 : Sep (G + 4 + 4) 4 x 1 := (outX x hx).sub (c := 4) (l := 4) (by omega)
    cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 with
    | none => exact (memStore8_ne n0).trans ((memStore8_ne n1).trans (M5out x hx))
    | some pe => exact (memStore8_ne n0).trans ((memStore32_get_sep s4).trans (memStore32_congr (M5out x hx)))
  have rsvC : ∀ {b : Word} {code : List Nat}, Sep S 80 b code.length → Sep (self + 8) 4 b code.length →
      CodeIn m.mem b code → CodeIn m13.mem b code := fun h1 h2 hc' i hi => by
    rw [m13x _ (h1.subR (c := i) (l := 1) (by omega))]
    cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 with
    | none => exact hc' i hi
    | some pe => exact (memStore32_get_sep (h2.subR (c := i) (l := 1) (by omega))).trans (hc' i hi)
  have hc13 := rsvC hSc hEc hc
  have hb13 := rsvC hSb hEb hb
  have fA13 : memLoad32 m13.mem (G + 0x1C) = reg m ra := (fr13 0x1C (by omega) (by omega)).trans fA
  have fB13 : memLoad32 m13.mem (G + 0x18) = reg m 8 := (fr13 0x18 (by omega) (by omega)).trans fB
  have fC13 : memLoad32 m13.mem (G + 0x14) = reg m 9 := (fr13 0x14 (by omega) (by omega)).trans fC
  have fD13 : memLoad32 m13.mem (G + 0x10) = reg m 18 := (fr13 0x10 (by omega) (by omega)).trans fD
  have fE13 : memLoad32 m13.mem (G + 0xC) = reg m 19 := (fr13 0xC (by omega) (by omega)).trans fE
  have k13' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
      r ≠ 18 → r ≠ 19 → reg m13 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 =>
    (k13 r h0 h1 h2 h3 h4 h5).trans (keep12 r h0 h6 h7 h8 h9 h18 h19)
  have s013 : reg m13 8 = out := (k13 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans s012
  have s113 : reg m13 9 = self := (k13 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans s112
  have s213 : reg m13 18 = hi := (k13 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans s212
  have s313 : reg m13 19 = lo := (k13 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans s312
  have hO4 : Sep out 4 S 80 := by have := hOS.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have hcO : Sep out 4 base bundleFieldCode.length := by
    have := hOc.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have errLd : ∀ (v : BitVec 8) c, 0xC ≤ c → c + 4 ≤ 0x20 →
      memLoad32 (memStore8 (memStore32 m13.mem out 0) (out + 0x4) v) (G + BitVec.ofNat 32 c) =
        memLoad32 m13.mem (G + BitVec.ofNat 32 c) := fun v c h1 h2 =>
    (memLoad32_congr fun j hj => memStore8_ne (by
      rw [add_ofNat_assoc, hGS, add_ofNat_assoc]
      exact fun e => hOS 4 (by omega) (48 + (c + j)) (by omega) e.symm)).trans
    (memLoad32_store32_sep (by rw [hGS, add_ofNat_assoc]; exact hO4.subR (c := 48 + c) (l := 4) (by omega)))
  have eA : ∀ v, memLoad32 (memStore8 (memStore32 m13.mem out 0) (out + 0x4) v) (G + 0x1C) = reg m ra :=
    fun v => (errLd v 0x1C (by omega) (by omega)).trans fA13
  have eB : ∀ v, memLoad32 (memStore8 (memStore32 m13.mem out 0) (out + 0x4) v) (G + 0x18) = reg m 8 :=
    fun v => (errLd v 0x18 (by omega) (by omega)).trans fB13
  have eC : ∀ v, memLoad32 (memStore8 (memStore32 m13.mem out 0) (out + 0x4) v) (G + 0x14) = reg m 9 :=
    fun v => (errLd v 0x14 (by omega) (by omega)).trans fC13
  have eD : ∀ v, memLoad32 (memStore8 (memStore32 m13.mem out 0) (out + 0x4) v) (G + 0x10) = reg m 18 :=
    fun v => (errLd v 0x10 (by omega) (by omega)).trans fD13
  have eE : ∀ v, memLoad32 (memStore8 (memStore32 m13.mem out 0) (out + 0x4) v) (G + 0xC) = reg m 19 :=
    fun v => (errLd v 0xC (by omega) (by omega)).trans fE13
  have pre := fun {mx : Machine} (c : Steps m13 mx) =>
    Steps.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9 (.cons e10
      (.cons e11 (c12.trans (c13.trans c))))))))))))
  have err : ∀ (mx : Machine) (fx : Fin 32 → Word), Steps m13 mx → St m13.mem base mx 0x4E fx → fx 8 = out →
      fx sp = G → (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
        r ≠ 18 → r ≠ 19 → fx r = reg m r) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 6 → reg m' r = reg m r) ∧
        m'.mem = memStore8 (memStore32 m13.mem out 0) (out + 0x4) ((fx a0).extractLsb' 0 8) := by
    intro mx fx c s h8 hs hk
    have hzx := s.zero
    obtain ⟨n1, d1, u1⟩ := s.sw hc13 bfl_at_4e (off' := 0x52) (by decide)
      (by rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out]; exact hout)
    rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out, show fx x0 = 0 from hzx] at u1
    have hc1 := hc13.store32 (v := 0) (a := out) hcO
    obtain ⟨n2, d2, u2⟩ := u1.sb hc1 bfl_at_52 (off' := 0x56) (by decide)
    rw [h8] at u2
    have hc2 := hc1.store8 (v := (fx a0).extractLsb' 0 8) (a := out + 0x4) (hOc.sub (c := 4) (l := 1) (by omega))
    obtain ⟨n3, d3, u3⟩ := u2.lw hc2 bfl_at_56 (off' := 0x58) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0x1C) (by decide))
    rw [hs, eA] at u3
    obtain ⟨n4, d4, u4⟩ := u3.lw hc2 bfl_at_58 (off' := 0x5A) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x18) (by decide))
    rw [show upd fx ra (reg m ra) sp = G by simp +decide only [upd]; exact hs, eB] at u4
    obtain ⟨n5, d5, u5⟩ := u4.lw hc2 bfl_at_5a (off' := 0x5C) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x14) (by decide))
    rw [show upd (upd fx ra (reg m ra)) 8 (reg m 8) sp = G by simp +decide only [upd]; exact hs, eC] at u5
    obtain ⟨n6, d6, u6⟩ := u5.lw hc2 bfl_at_5c (off' := 0x5E) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x10) (by decide))
    rw [show upd (upd (upd fx ra (reg m ra)) 8 (reg m 8)) 9 (reg m 9) sp = G by simp +decide only [upd]; exact hs,
      eD] at u6
    obtain ⟨n7, d7, u7⟩ := u6.lw hc2 bfl_at_5e (off' := 0x60) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0xC) (by decide))
    rw [show upd (upd (upd (upd fx ra (reg m ra)) 8 (reg m 8)) 9 (reg m 9)) 18 (reg m 18) sp = G by
      simp +decide only [upd]; exact hs, eE] at u7
    obtain ⟨n8, d8, u8⟩ := u7.aluImm hc2 bfl_at_60 (off' := 0x62) (by decide)
    obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.jalr hc2 bfl_at_62
    refine ⟨n9, pre (c.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8
      (.single d9)))))))))), ?_, ?_, fun r h0 h1 h2 h3 h4 h5 _ => ?_, by rw [mem9]⟩
    · rw [pc9, add_lit_zero]; simp +decide only [upd, ite_true, ite_false]; rw [hra, hret]
    · rw [regs9]; simp +decide only [upd, ite_true, ite_false]; rw [hs, ← hspG]; rfl
    · rw [regs9]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      by_cases hsp' : r = sp
      · subst hsp'; simp +decide [upd]; rw [hs, ← hspG]; rfl
      by_cases hra' : r = ra
      · subst hra'; simp +decide [upd]
      by_cases h8' : r = 8
      · subst h8'; simp +decide [upd]
      by_cases h9' : r = 9
      · subst h9'; simp +decide [upd]
      by_cases h18 : r = 18
      · subst h18; simp +decide [upd]
      by_cases h19 : r = 19
      · subst h19; simp +decide [upd]
      simp [upd, hr, hsp', hra', h8', h9', h18, h19]
      exact hk r h0 h1 h2 h3 h4 h5 hra' hsp' h8' h9' h18 h19
  have t13 : St m13.mem base m13 0x1E (reg m13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
  have hz13 : reg m13 0 = 0 := t13.zero
  have us : ∀ (g : Fin 32 → Word) (r : Fin 32) (v : Word), r.val ≠ 0 → upd g r v r = v := fun g r v h => by
    simp only [upd, h, ↓reduceIte]
  obtain ⟨n14, e14, t14⟩ := t13.lbu hc13 bfl_at_1e (off' := 0x22) (by decide)
  rw [sp13] at t14
  have tag : m13.mem (G + 0x4) = Cur.u32Mem M5 (G + 4) self (G + 4) := mem13 _ (inG 4 (by omega))
  rcases hbr : bytesResult ptr len (memLoad32 m.mem (self + 8)) 4 with _ | ⟨p, e⟩
  · obtain ⟨u0, u1', -⟩ := u32MemCur_none (out := G + 4) (hR.trans hbr)
    rw [tag, u0] at t14
    obtain ⟨n15, e15, t15⟩ := t14.notTaken hc13 0x24 bfl_at_22 (by decide)
      (by rw [us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq ((1 : BitVec 8).zeroExtend 32) 0 = false))
    obtain ⟨n16, e16, t16⟩ := t15.lbu hc13 bfl_at_24 (off' := 0x28) (by decide)
    rw [updz hz13 (show sp ≠ a0 by decide), sp13, show G + (0x5 : Word) = G + 4 + 1 by rw [BitVec.add_assoc]; rfl,
      mem13 _ (by have := inG 5 (by omega); rwa [show G + BitVec.ofNat 32 5 = G + 4 + 1 by rw [BitVec.add_assoc]; rfl] at this),
      u1'] at t16
    obtain ⟨n17, e17, t17⟩ := t16.jump hc13 bfl_at_28 (off' := 0x4E) (by decide)
      (by rw [t16.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x4E (by decide)))
    obtain ⟨m', c', pc', sp', k', mem'⟩ := err _ _ (.cons e14 (.cons e15 (.cons e16 (.single e17)))) t17
      (by rw [updz t14.zero (by decide), updz hz13 (by decide)]; exact s013)
      (by rw [updz t14.zero (by decide), updz hz13 (by decide)]; exact sp13)
      (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => by
        rw [updz t14.zero h0, updz hz13 h0]; exact k13' r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
    refine ⟨m', c', pc', sp', k', fun x hx => ?_⟩
    have mx : m13.mem x = m.mem x := by rw [m13x x hx, hbr]
    rw [mem']; unfold fieldMem; rw [hptr, hlen, hbr]
    exact memStore8_congr (memStore32_congr mx)
  · obtain ⟨u0, uv, -⟩ := u32MemCur_some (out := G + 4) (hR.trans hbr)
    obtain ⟨hp1, hle⟩ : ptr + memLoad32 m.mem (self + 8) = p ∧ (memLoad32 m.mem (self + 8)).toNat + 4 ≤ len.toNat := by
      have hb2 := hbr
      rw [bytesResult_eq] at hb2
      split at hb2
      · next h => injection hb2 with h'; injection h' with h1 h2; exact ⟨h1, h⟩
      · cases hb2
    have hM5p : memLoad32 M5 p = memLoad32 m.mem p := memLoad32_congr fun j hj => by
      have addr : p + BitVec.ofNat 32 j = ptr + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + j) := by
        rw [← hp1, ← add_ofNat_assoc, Cur.ofNat_toNat_self]
      rw [addr]; exact M5out _ (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
    rw [tag, u0] at t14
    obtain ⟨n15, e15, t15⟩ := t14.taken hc13 0x2A bfl_at_22 (by decide)
      (by rw [us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq ((0 : BitVec 8).zeroExtend 32) 0 = true))
    obtain ⟨n16, e16, t16⟩ := t15.lw hc13 bfl_at_2a (off' := 0x2C) (by decide)
      (by rw [updz hz13 (show sp ≠ a0 by decide), sp13]; exact aligned_add hGa (k := 8) (by decide))
    have val : memLoad32 m13.mem (G + 0x8) = memLoad32 m.mem p := by
      rw [show G + (0x8 : Word) = G + 4 + 4 by rw [BitVec.add_assoc]; rfl, ← hM5p, ← uv]
      refine memLoad32_congr fun j hj => ?_
      rw [show G + 4 + 4 + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (8 + j) by
        rw [show (G + 4 + 4 : Word) = G + BitVec.ofNat 32 8 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]]
      exact mem13 _ (inG (8 + j) (by omega))
    rw [updz hz13 (show sp ≠ a0 by decide), sp13, val] at t16
    have g16 : ∀ r, r ≠ a0 → r ≠ a2 → upd (upd (reg m13) a0 ((0 : BitVec 8).zeroExtend 32)) a2 (memLoad32 m.mem p) r =
        reg m13 r := fun r h0 h2 => by rw [updz t14.zero h2, updz hz13 h0]
    have n2 : upd (upd (reg m13) a0 ((0 : BitVec 8).zeroExtend 32)) a2 (memLoad32 m.mem p) a2 = memLoad32 m.mem p :=
      us _ a2 _ (by decide)
    have k16 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
        r ≠ 18 → r ≠ 19 → upd (upd (reg m13) a0 ((0 : BitVec 8).zeroExtend 32)) a2 (memLoad32 m.mem p) r = reg m r :=
      fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => (g16 r h0 h2).trans (k13' r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
    have toErr : ∀ (mx : Machine), Steps m13 mx →
        St m13.mem base mx 0x4C (upd (upd (reg m13) a0 ((0 : BitVec 8).zeroExtend 32)) a2 (memLoad32 m.mem p)) →
        ¬ (lo.toNat ≤ (memLoad32 m.mem p).toNat ∧ (memLoad32 m.mem p).toNat ≤ hi.toNat) →
        ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
          (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 6 → reg m' r = reg m r) ∧
          ∀ x, Sep S 80 x 1 → m'.mem x = fieldMem m.mem out self lo hi x := by
      intro mx c s hn
      obtain ⟨n1, d1, u1⟩ := s.aluImm hc13 bfl_at_4c (off' := 0x4E) (by decide)
      obtain ⟨m', c', pc', sp', k', mem'⟩ := err _ _ (c.trans (.single d1)) u1
        (by rw [updz s.zero (by decide), g16 8 (by decide) (by decide)]; exact s013)
        (by rw [updz s.zero (by decide), g16 sp (by decide) (by decide)]; exact sp13)
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => by
          rw [updz s.zero h0]; exact k16 r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
      refine ⟨m', c', pc', sp', k', fun x hx => ?_⟩
      have mx : m13.mem x = memStore32 m.mem (self + 8) e x := by rw [m13x x hx, hbr]
      rw [mem']; unfold fieldMem; rw [hptr, hlen, hbr]; simp only [hn, ↓reduceIte]
      exact memStore8_congr (memStore32_congr mx)
    have pre16 : Steps m13 n16 := .cons e14 (.cons e15 (.single e16))
    by_cases hlo : (memLoad32 m.mem p).ult lo = true
    · obtain ⟨n17, e17, t17⟩ := t16.taken hc13 0x4C bfl_at_2c (by decide)
        (by rw [n2, g16 19 (by decide) (by decide), s313]; exact hlo)
      exact toErr n17 (pre16.trans (.single e17)) t17 fun h => by
        have : (memLoad32 m.mem p).toNat < lo.toNat := of_decide_eq_true hlo
        omega
    have hlo' : lo.toNat ≤ (memLoad32 m.mem p).toNat := by
      have : ¬ (memLoad32 m.mem p).toNat < lo.toNat := fun h => hlo (decide_eq_true h)
      omega
    obtain ⟨n17, e17, t17⟩ := t16.notTaken hc13 0x30 bfl_at_2c (by decide)
      (by
        rw [n2, g16 19 (by decide) (by decide), s313]
        show (memLoad32 m.mem p).ult lo = false
        cases h : (memLoad32 m.mem p).ult lo
        · rfl
        · exact absurd h hlo)
    by_cases hhi : hi.ult (memLoad32 m.mem p) = true
    · obtain ⟨n18, e18, t18⟩ := t17.taken hc13 0x4C bfl_at_30 (by decide)
        (by rw [n2, g16 18 (by decide) (by decide), s213]; exact hhi)
      exact toErr n18 (pre16.trans (.cons e17 (.single e18))) t18 fun h => by
        have : hi.toNat < (memLoad32 m.mem p).toNat := of_decide_eq_true hhi
        omega
    have hhi' : (memLoad32 m.mem p).toNat ≤ hi.toNat := by
      have : ¬ hi.toNat < (memLoad32 m.mem p).toNat := fun h => hhi (decide_eq_true h)
      omega
    obtain ⟨n18, e18, t18⟩ := t17.notTaken hc13 0x34 bfl_at_30 (by decide)
      (by
        rw [n2, g16 18 (by decide) (by decide), s213]
        show hi.ult (memLoad32 m.mem p) = false
        cases h : hi.ult (memLoad32 m.mem p)
        · rfl
        · exact absurd h hhi)
    obtain ⟨n19, e19, t19⟩ := t18.alu hc13 bfl_at_34 (off' := 0x36) (by decide)
    obtain ⟨n20, e20, t20⟩ := t19.alu hc13 bfl_at_36 (off' := 0x38) (by decide)
    have q20 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n20 r = reg m13 r := fun r h0 h1 h2 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; rw [t20.self.zero, hz13]
      rw [t20.regs]; simp only [upd, hr, h0, h1, h2, ↓reduceIte]
    have q20a0 : reg n20 a0 = out := by
      rw [t20.regs]; simp +decide only [upd, ite_true, ite_false]; rw [s013]; exact BitVec.zero_add out
    have q20a1 : reg n20 a1 = self := by
      rw [t20.regs]; simp +decide only [upd, ite_true, ite_false]; rw [s113]; exact BitVec.zero_add self
    have q20a2 : reg n20 a2 = memLoad32 m.mem p := by rw [t20.regs]; simp +decide only [upd, ite_true, ite_false]
    have q20sp : reg n20 sp = G := (q20 sp (by decide) (by decide) (by decide)).trans sp13
    have u20 := t20.self
    obtain ⟨n21, e21, t21⟩ := u20.lw hc13 bfl_at_38 (off' := 0x3A) (by decide)
      (by rw [q20sp]; exact aligned_add hGa (k := 0x1C) (by decide))
    rw [q20sp, fA13] at t21
    obtain ⟨n22, e22, t22⟩ := t21.lw hc13 bfl_at_3a (off' := 0x3C) (by decide)
      (by simp +decide only [upd]; rw [q20sp]; exact aligned_add hGa (k := 0x18) (by decide))
    rw [show upd (reg n20) ra (reg m ra) sp = G by simp +decide only [upd]; exact q20sp, fB13] at t22
    obtain ⟨n23, e23, t23⟩ := t22.lw hc13 bfl_at_3c (off' := 0x3E) (by decide)
      (by simp +decide only [upd]; rw [q20sp]; exact aligned_add hGa (k := 0x14) (by decide))
    rw [show upd (upd (reg n20) ra (reg m ra)) 8 (reg m 8) sp = G by simp +decide only [upd]; exact q20sp, fC13] at t23
    obtain ⟨n24, e24, t24⟩ := t23.lw hc13 bfl_at_3e (off' := 0x40) (by decide)
      (by simp +decide only [upd]; rw [q20sp]; exact aligned_add hGa (k := 0x10) (by decide))
    rw [show upd (upd (upd (reg n20) ra (reg m ra)) 8 (reg m 8)) 9 (reg m 9) sp = G by
      simp +decide only [upd]; exact q20sp, fD13] at t24
    obtain ⟨n25, e25, t25⟩ := t24.lw hc13 bfl_at_40 (off' := 0x42) (by decide)
      (by simp +decide only [upd]; rw [q20sp]; exact aligned_add hGa (k := 0xC) (by decide))
    rw [show upd (upd (upd (upd (reg n20) ra (reg m ra)) 8 (reg m 8)) 9 (reg m 9)) 18 (reg m 18) sp = G by
      simp +decide only [upd]; exact q20sp, fE13] at t25
    obtain ⟨n26, e26, t26⟩ := t25.aluImm hc13 bfl_at_42 (off' := 0x44) (by decide)
    obtain ⟨n27, e27, t27⟩ := t26.auipc hc13 bfl_at_44 (off' := 0x48) (by decide)
    obtain ⟨n28, e28, pc28, mem28, regs28⟩ := t27.jalr hc13 bfl_at_48
    have p28 : n28.pc = base + 0xFFFFCF8A := by
      rw [pc28]; simp +decide only [upd, ite_true, ite_false]
      rw [show base + BitVec.ofNat 32 0x44 + 0xFFFFD000 + 0xFFFFFF46 = base + 0xFFFFCF8A by
        rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
      exact even_clear _ (even_at base hbase 0xFFFFCF8A (by decide))
    have r28 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 6 → reg n28 r = reg m r :=
      fun r h0 h1 h2 h3 h4 h5 h6 => by
        rw [regs28]
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; simp [upd, hz]
        by_cases hsp' : r = sp
        · subst hsp'; simp +decide [upd]; rw [q20sp, ← hspG]; rfl
        by_cases hra' : r = ra
        · subst hra'; simp +decide [upd]
        by_cases h8' : r = 8
        · subst h8'; simp +decide [upd]
        by_cases h9' : r = 9
        · subst h9'; simp +decide [upd]
        by_cases h18 : r = 18
        · subst h18; simp +decide [upd]
        by_cases h19 : r = 19
        · subst h19; simp +decide [upd]
        simp [upd, hr, hsp', hra', h8', h9', h18, h19, h6]
        rw [q20 r h0 h1 h2]; exact k13' r h0 h1 h2 h3 h4 h5 hra' hsp' h8' h9' h18 h19
    obtain ⟨m', c', pc', mem', fr'⟩ := readerBytes_correct n28 (base + 0xFFFFCF8A) retAddr out self
      (memLoad32 m.mem p) (by show CodeIn n28.mem _ _; rw [mem28]; exact hb13) p28
      (by rw [regs28]; simp +decide only [upd, ite_false]; exact q20a0)
      (by rw [regs28]; simp +decide only [upd, ite_false]; exact q20a1)
      (by rw [regs28]; simp +decide only [upd, ite_false]; exact q20a2)
      (by rw [r28 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hra)
      hret hout hself hOb hEb
    refine ⟨m', pre (pre16.trans (.cons e17 (.cons e18 (.cons e19 (.cons e20 (.cons e21 (.cons e22 (.cons e23
      (.cons e24 (.cons e25 (.cons e26 (.cons e27 (.cons e28 c'))))))))))))), pc', ?_,
      fun r h0 h1 h2 h3 h4 h5 h6 => ?_, fun x hx => ?_⟩
    · rw [fr' sp (by decide) (by decide) (by decide)]
      exact r28 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [fr' r h3 h4 h5]; exact r28 r h0 h1 h2 h3 h4 h5 h6
    · have mx : ∀ y, Sep S 80 y 1 → m13.mem y = memStore32 m.mem (self + 8) e y := fun y hy => by rw [m13x y hy, hbr]
      rw [mem', mem28]; unfold fieldMem; rw [hptr, hlen, hbr]; simp only [hlo', hhi', and_self, ↓reduceIte]
      exact bytesMem_congr (mx x hx) fun j hj => mx _ ((hRS.sub (c := j) (l := 1) (by omega)).symm)

end C3.RV32

