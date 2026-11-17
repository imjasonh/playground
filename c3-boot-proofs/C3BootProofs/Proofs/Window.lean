import C3BootProofs.Proofs.ReaderU64
import C3BootProofs.Proofs.Bundle

/-!
# `c3_verify::trustroot::read_window`

`read_window(r)` reads a start and an end with `Reader::u64` and returns
them as `Result<(u64, u64), Error>`: a tag byte, the error byte at offset 1,
the start at offset 8, and the end at offset 16, low words first. An end
before the start is `OutOfRange` (5).
-/

namespace C3.RV32

open C3.Image

/-- Memory after `read_window` returns, outside the stack it uses. -/
def windowMem (M : Word → BitVec 8) (out self : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 8 with
  | none => memStore8 (memStore8 M (out + 1) 0) out 1
  | some (p, e) =>
    match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) e 8 with
    | none => memStore8 (memStore8 (memStore32 M (self + 8) e) (out + 1) 0) out 1
    | some (q, e') =>
      if (memLoad32 M (q + 4)).toNat * 2 ^ 32 + (memLoad32 M q).toNat <
          (memLoad32 M (p + 4)).toNat * 2 ^ 32 + (memLoad32 M p).toNat then
        memStore8 (memStore8 (memStore32 M (self + 8) e') (out + 1) 5) out 1
      else memStore8 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (self + 8) e') (out + 8)
        (memLoad32 M p)) (out + 0xC) (memLoad32 M (p + 4))) (out + 0x10) (memLoad32 M q)) (out + 0x14)
        (memLoad32 M (q + 4))) out 0

theorem u64Mem_none {M : Word → BitVec 8} {out self : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 8 = none) :
    u64Mem M out self out = 1 ∧ u64Mem M out self (out + 1) = 0 ∧
    ∀ x, x ≠ out → x ≠ out + 1 → u64Mem M out self x = M x := by
  have n10 : out + 1 ≠ out := by
    have := add_ofNat_ne out (c := 1) (d := 0) (by decide) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  unfold u64Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, by rw [memStore8_ne n10, memStore8_same], fun x h1 h2 => ?_⟩
  rw [memStore8_ne h1, memStore8_ne h2]

theorem u64Mem_some {M : Word → BitVec 8} {out self p e : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 8 = some (p, e)) :
    u64Mem M out self out = 0 ∧ memLoad32 (u64Mem M out self) (out + 8) = memLoad32 M p ∧
    memLoad32 (u64Mem M out self) (out + 0xC) = memLoad32 M (p + 4) ∧
    ∀ x, x ≠ out → Sep (out + 8) 8 x 1 → u64Mem M out self x = memStore32 M (self + 8) e x := by
  have s08 : Sep out 1 (out + 8) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 8) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s0C : Sep out 1 (out + 0xC) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 0xC) (k := 4) (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have sC8 : Sep (out + 0xC) 4 (out + 8) 4 :=
    sep_offsets out (c := 0xC) (n := 4) (d := 8) (k := 4) (by omega) (by omega) (by omega)
  unfold u64Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, ?_, ?_, fun x h1 h2 => ?_⟩
  · rw [memLoad32_store8_sep s08, memLoad32_store32_sep sC8, memLoad32_store32_same]
  · rw [memLoad32_store8_sep s0C, memLoad32_store32_same]
  · have hC : Sep (out + 0xC) 4 x 1 := by
      have := h2.sub (c := 4) (l := 4) (by omega)
      rwa [show out + 8 + BitVec.ofNat 32 4 = out + 0xC by rw [BitVec.add_assoc]; rfl] at this
    have h8 : Sep (out + 8) 4 x 1 := by have := h2.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
    rw [memStore8_ne h1, memStore32_get_sep hC, memStore32_get_sep h8]

theorem rwin_at_0 : fetchRel readWindowCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem rwin_at_2 : fetchRel readWindowCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem rwin_at_4 : fetchRel readWindowCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem rwin_at_6 : fetchRel readWindowCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem rwin_at_8 : fetchRel readWindowCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem rwin_at_a : fetchRel readWindowCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem rwin_at_c : fetchRel readWindowCode 0xC = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem rwin_at_e : fetchRel readWindowCode 0xE = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem rwin_at_10 : fetchRel readWindowCode 0x10 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem rwin_at_12 : fetchRel readWindowCode 0x12 = some (.auipc ra 0x0, 4) := by decide
theorem rwin_at_16 : fetchRel readWindowCode 0x16 = some (.jalr ra ra 0x66, 4) := by decide
theorem rwin_at_1a : fetchRel readWindowCode 0x1A = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem rwin_at_1e : fetchRel readWindowCode 0x1E = some (.branch .bne a0 x0 0x18, 2) := by decide
theorem rwin_at_20 : fetchRel readWindowCode 0x20 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem rwin_at_22 : fetchRel readWindowCode 0x22 = some (.load .lw (19 : Fin 32) sp 0x14, 2) := by decide
theorem rwin_at_24 : fetchRel readWindowCode 0x24 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem rwin_at_26 : fetchRel readWindowCode 0x26 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem rwin_at_28 : fetchRel readWindowCode 0x28 = some (.auipc ra 0x0, 4) := by decide
theorem rwin_at_2c : fetchRel readWindowCode 0x2C = some (.jalr ra ra 0x50, 4) := by decide
theorem rwin_at_30 : fetchRel readWindowCode 0x30 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem rwin_at_34 : fetchRel readWindowCode 0x34 = some (.branch .beq a0 x0 0x1E, 2) := by decide
theorem rwin_at_36 : fetchRel readWindowCode 0x36 = some (.load .lbu a0 sp 0x9, 4) := by decide
theorem rwin_at_3a : fetchRel readWindowCode 0x3A = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem rwin_at_3e : fetchRel readWindowCode 0x3E = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem rwin_at_40 : fetchRel readWindowCode 0x40 = some (.store .sb (8 : Fin 32) a1 0x0, 4) := by decide
theorem rwin_at_44 : fetchRel readWindowCode 0x44 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem rwin_at_46 : fetchRel readWindowCode 0x46 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem rwin_at_48 : fetchRel readWindowCode 0x48 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem rwin_at_4a : fetchRel readWindowCode 0x4A = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem rwin_at_4c : fetchRel readWindowCode 0x4C = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem rwin_at_4e : fetchRel readWindowCode 0x4E = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem rwin_at_50 : fetchRel readWindowCode 0x50 = some (.jalr x0 ra 0x0, 2) := by decide
theorem rwin_at_52 : fetchRel readWindowCode 0x52 = some (.load .lw a0 sp 0x14, 2) := by decide
theorem rwin_at_54 : fetchRel readWindowCode 0x54 = some (.load .lw a2 sp 0x10, 2) := by decide
theorem rwin_at_56 : fetchRel readWindowCode 0x56 = some (.branch .beq (19 : Fin 32) a0 0x18, 4) := by decide
theorem rwin_at_5a : fetchRel readWindowCode 0x5A = some (.alu .sltu a1 a0 (19 : Fin 32), 4) := by decide
theorem rwin_at_5e : fetchRel readWindowCode 0x5E = some (.branch .bne a1 x0 0x16, 2) := by decide
theorem rwin_at_60 : fetchRel readWindowCode 0x60 = some (.store .sw (8 : Fin 32) (18 : Fin 32) 0x8, 4) := by decide
theorem rwin_at_64 : fetchRel readWindowCode 0x64 = some (.store .sw (8 : Fin 32) (19 : Fin 32) 0xC, 4) := by decide
theorem rwin_at_68 : fetchRel readWindowCode 0x68 = some (.store .sw (8 : Fin 32) a2 0x10, 2) := by decide
theorem rwin_at_6a : fetchRel readWindowCode 0x6A = some (.store .sw (8 : Fin 32) a0 0x14, 2) := by decide
theorem rwin_at_6c : fetchRel readWindowCode 0x6C = some (.jal x0 0xFFFFFFD4, 2) := by decide
theorem rwin_at_6e : fetchRel readWindowCode 0x6E = some (.alu .sltu a1 a2 (18 : Fin 32), 4) := by decide
theorem rwin_at_72 : fetchRel readWindowCode 0x72 = some (.branch .beq a1 x0 0xFFFFFFEE, 2) := by decide
theorem rwin_at_74 : fetchRel readWindowCode 0x74 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem rwin_at_76 : fetchRel readWindowCode 0x76 = some (.jal x0 0xFFFFFFC4, 2) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`read_window`, as compiled**: with `Reader::u64` and `Reader::bytes`
where the image puts them, a reader `self` over a slice that is not null and
doesn't wrap, a result address `out`, and 80 bytes of stack below `sp`, all
apart as the hypotheses list, it returns to `ra` with the registers but `a0`
through `a7` restored, and memory outside its stack as `windowMem` says. -/
theorem readWindow_correct (m : Machine) {base retAddr out self : Word}
    (hc : CodeIn m.mem base readWindowCode) (hu : CodeIn m.mem (base + 0x78) readerU64Code)
    (hb : CodeIn m.mem (base + 0x78 + 0xFFFFC30A) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = self)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hself : self.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSc : Sep (reg m sp + 0xFFFFFFB0) 80 base readWindowCode.length)
    (hSu : Sep (reg m sp + 0xFFFFFFB0) 80 (base + 0x78) readerU64Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFB0) 80 (base + 0x78 + 0xFFFFC30A) readerBytesCode.length)
    (hOc : Sep out 0x18 base readWindowCode.length)
    (hEu : Sep (self + 8) 4 (base + 0x78) readerU64Code.length)
    (hEb : Sep (self + 8) 4 (base + 0x78 + 0xFFFFC30A) readerBytesCode.length)
    (hEc : Sep (self + 8) 4 base readWindowCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFB0) 80) (hOS : Sep out 0x18 (reg m sp + 0xFFFFFFB0) 80)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFB0) 80)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFB0) 80 x 1 → m'.mem x = windowMem m.mem out self x := by
  obtain ⟨S, hSd⟩ : ∃ S, reg m sp + 0xFFFFFFB0 = S := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFFD0 = G := ⟨_, rfl⟩
  rw [hSd] at hSc hSu hSb hRS hOS hBS ⊢
  obtain ⟨ptr, hptr⟩ : ∃ ptr, memLoad32 m.mem self = ptr := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, memLoad32 m.mem (self + 4) = len := ⟨_, rfl⟩
  rw [hptr, hlen] at hbuf hBS hBE
  have hGS : G = S + BitVec.ofNat 32 32 := by rw [← hGd, ← hSd, BitVec.add_assoc]; rfl
  have hSG : G + 0xFFFFFFE0 = S := by rw [← hGd, ← hSd, BitVec.add_assoc]; rfl
  have hspG : G + 0x30 = reg m sp := by rw [← hGd, BitVec.add_assoc]; exact BitVec.add_zero _
  have hGa : G.toNat % 4 = 0 := hGd ▸ aligned_add hsp (k := 0xFFFFFFD0) (by decide)
  have fr : ∀ c l, c + l ≤ 48 → ∀ (x : Word) (n : Nat), Sep S 80 x n → Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := 32 + c) (l := l) (by omega)
  have s32 : ∀ (x : Word) (n : Nat), Sep S 80 x n → Sep (G + 0xFFFFFFE0) 32 x n := fun x n hx => by
    rw [hSG]; have := hx.sub (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this
  have s32R : ∀ {a : Word} {n : Nat}, Sep a n S 80 → Sep a n (G + 0xFFFFFFE0) 32 := fun h => by
    rw [hSG]; have := h.subR (c := 0) (l := 32) (by omega); rwa [add_ofNat_zero] at this
  have inG : ∀ c, c < 48 → Sep (G + 0xFFFFFFE0) 32 (G + BitVec.ofNat 32 c) 1 := fun c hc' => by
    rw [hSG, hGS, add_ofNat_assoc]
    have := sep_offsets S (c := 0) (n := 32) (d := 32 + c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc rwin_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFD0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc rwin_at_2 (off' := 4) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x2C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (fr 0x2C 4 (by omega) _ _ hSc)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 rwin_at_4 (off' := 6) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x28) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (fr 0x28 4 (by omega) _ _ hSc)
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 rwin_at_6 (off' := 8) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x24) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  have hc4 := hc3.store32 (v := reg m 9) (fr 0x24 4 (by omega) _ _ hSc)
  obtain ⟨m5, e5, t5⟩ := t4.sw hc4 rwin_at_8 (off' := 0xA) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x20) (by decide))
  rw [u1sp, f1 18 (by decide)] at t5
  have hc5 := hc4.store32 (v := reg m 18) (fr 0x20 4 (by omega) _ _ hSc)
  obtain ⟨m6, e6, t6⟩ := t5.sw hc5 rwin_at_a (off' := 0xC) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x1C) (by decide))
  rw [u1sp, f1 19 (by decide)] at t6
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 m.mem (G + 0x2C) (reg m ra))
      (G + 0x28) (reg m 8)) (G + 0x24) (reg m 9)) (G + 0x20) (reg m 18)) (G + 0x1C) (reg m 19) = M5 := ⟨_, rfl⟩
  rw [hM5] at t6
  have M5out : ∀ x, Sep S 80 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5]
    exact (memStore32_get_sep (fr 0x1C 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x20 4 (by omega) x 1 hx)).trans
      ((memStore32_get_sep (fr 0x24 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x28 4 (by omega) x 1 hx)).trans
      (memStore32_get_sep (fr 0x2C 4 (by omega) x 1 hx)))))
  have codeOut : ∀ {b : Word} {code : List Nat}, Sep S 80 b code.length → CodeIn m.mem b code → CodeIn M5 b code :=
    fun h hc' i hi => by rw [M5out _ (h.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have hc6 := codeOut hSc hc
  have ldS : ∀ c, c + 4 ≤ 12 → memLoad32 M5 (self + BitVec.ofNat 32 c) = memLoad32 m.mem (self + BitVec.ofNat 32 c) :=
    fun c hc' => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact M5out _ ((hRS.sub (c := c + j) (l := 1) (by omega)).symm)
  have l0 : memLoad32 M5 self = ptr := by have := ldS 0 (by omega); rwa [add_ofNat_zero, hptr] at this
  have l4 : memLoad32 M5 (self + 4) = len := (ldS 4 (by omega)).trans hlen
  have l8 : memLoad32 M5 (self + 8) = memLoad32 m.mem (self + 8) := ldS 8 (by omega)
  have fA : memLoad32 M5 (G + 0x2C) = reg m ra := by
    rw [← hM5]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x28) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fB : memLoad32 M5 (G + 0x28) = reg m 8 := by
    rw [← hM5]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fC : memLoad32 M5 (G + 0x24) = reg m 9 := by
    rw [← hM5]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fD : memLoad32 M5 (G + 0x20) = reg m 18 := by
    rw [← hM5]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fE : memLoad32 M5 (G + 0x1C) = reg m 19 := by rw [← hM5]; exact memLoad32_store32_same _ _ _
  obtain ⟨m7, e7, t7⟩ := t6.alu hc6 rwin_at_c (off' := 0xE) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.alu hc6 rwin_at_e (off' := 0x10) (by decide)
  obtain ⟨m9, e9, t9⟩ := t8.aluImm hc6 rwin_at_10 (off' := 0x12) (by decide)
  obtain ⟨m10, c10, pc10, mem10, regs10⟩ := t9.callRa (cb := base + 0x78) hc6 rwin_at_12 rwin_at_16
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0x78 (by decide))
  have sp10 : reg m10 sp = G := by rw [regs10]; simp +decide [upd]
  have a010 : reg m10 a0 = G + 8 := by rw [regs10]; simp +decide [upd, aluEval]
  have a110 : reg m10 a1 = self := by rw [regs10]; simp +decide [upd, ha1]
  have s010 : reg m10 8 = out := by rw [regs10]; simp +decide [upd, aluEval, ha0]
  have s110 : reg m10 9 = self := by rw [regs10]; simp +decide [upd, aluEval, ha1]
  have ra10 : reg m10 ra = base + BitVec.ofNat 32 (0x12 + 8) := by rw [regs10]; simp +decide [upd]
  have keep10 : ∀ r, r ≠ a0 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 → reg m10 r = reg m r :=
    fun r h0 h1 h2 h3 h4 => by
      rw [regs10]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1, h2, h3, h4]
  have hO16 : Sep (G + 8) 16 (G + 0xFFFFFFE0) 32 := by
    rw [hSG]; show Sep (G + BitVec.ofNat 32 8) 16 S 32; rw [hGS, add_ofNat_assoc]
    have := sep_offsets S (c := 32 + 8) (n := 16) (d := 0) (k := 32) (Or.inr (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  obtain ⟨m11, c11, pc11, sp11, k11, mem11⟩ := readerU64_correct m10 (base := base + 0x78)
    (retAddr := base + BitVec.ofNat 32 (0x12 + 8)) (out := G + 8) (self := self)
    (by rw [mem10]; exact codeOut hSu hu) (by rw [mem10]; exact codeOut hSb hb)
    (even_at base hbase 0x78 (by decide)) pc10 a010 a110 ra10
    (even_clear _ (even_at base hbase (0x12 + 8) (by decide)))
    (by rw [sp10]; exact hGa) hself (aligned_add hGa (k := 8) (by decide)) (by rw [mem10, l0, l4]; exact hbuf)
    (by rw [sp10]; exact s32 _ _ hSu) (by rw [sp10]; exact s32 _ _ hSb)
    (fr 8 16 (by omega) _ _ hSu) hEb hEu
    (by rw [sp10]; exact s32R hRS) (by rw [sp10]; exact hO16) (by rw [mem10, l0, l4, sp10]; exact s32R hBS)
    (by rw [mem10, l0, l4]; exact hBE)
  rw [sp10, mem10] at mem11
  rw [sp10] at sp11
  have hR : bytesResult (memLoad32 M5 self) (memLoad32 M5 (self + 4)) (memLoad32 M5 (self + 8)) 8 =
      bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 := by rw [l0, l4, l8]
  have uOut : ∀ (Mx : Word → BitVec 8) x, Sep (G + 8) 16 x 1 → Sep (self + 8) 4 x 1 → u64Mem Mx (G + 8) self x = Mx x :=
    fun Mx x h1 h2 => by
      have n0 : x ≠ G + 8 := fun e => h1 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
      have n1 : x ≠ G + 8 + 1 := fun e => h1 1 (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)
      have s8 : Sep (G + 8 + 8) 8 x 1 := h1.sub (c := 8) (l := 8) (by omega)
      rcases hb' : bytesResult (memLoad32 Mx self) (memLoad32 Mx (self + 4)) (memLoad32 Mx (self + 8)) 8 with _ | ⟨q, e'⟩
      · exact (u64Mem_none hb').2.2 x n0 n1
      · exact ((u64Mem_some hb').2.2.2 x n0 s8).trans (memStore32_get_sep h2)
  have frm16 : ∀ c, 0x18 ≤ c → c + 1 ≤ 0x30 → Sep (G + 8) 16 (G + BitVec.ofNat 32 c) 1 := fun c h1 h2 => by
    show Sep (G + BitVec.ofNat 32 8) 16 _ 1
    exact sep_offsets G (c := 8) (n := 16) (d := c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
  have frE : ∀ c, 0x18 ≤ c → c + 1 ≤ 0x30 → Sep (self + 8) 4 (G + BitVec.ofNat 32 c) 1 := fun c h1 h2 => by
    rw [hGS, add_ofNat_assoc]; exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 32 + c) (l := 1) (by omega)
  have frU : ∀ (Mx Mx' : Word → BitVec 8), (∀ x, Sep (G + 0xFFFFFFE0) 32 x 1 → Mx' x = u64Mem Mx (G + 8) self x) →
      ∀ c, 0x1C ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx' (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) :=
    fun Mx Mx' h c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, h _ (inG (c + j) (by omega))]
      exact uOut Mx _ (frm16 (c + j) (by omega) (by omega)) (frE (c + j) (by omega) (by omega))
  have outX : ∀ x, Sep S 80 x 1 → Sep (G + 8) 16 x 1 := fun x hx => fr 8 16 (by omega) x 1 hx
  have uX : ∀ (Mx : Word → BitVec 8) x, Sep S 80 x 1 → u64Mem Mx (G + 8) self x =
      match bytesResult (memLoad32 Mx self) (memLoad32 Mx (self + 4)) (memLoad32 Mx (self + 8)) 8 with
      | none => Mx x
      | some (_, e) => memStore32 Mx (self + 8) e x := fun Mx x hx => by
    have n0 : x ≠ G + 8 := fun e => outX x hx 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
    have n1 : x ≠ G + 8 + 1 := fun e => outX x hx 1 (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)
    have s8 : Sep (G + 8 + 8) 8 x 1 := (outX x hx).sub (c := 8) (l := 8) (by omega)
    rcases hb' : bytesResult (memLoad32 Mx self) (memLoad32 Mx (self + 4)) (memLoad32 Mx (self + 8)) 8 with _ | ⟨q, e'⟩
    · exact (u64Mem_none hb').2.2 x n0 n1
    · exact (u64Mem_some hb').2.2.2 x n0 s8
  have m11x : ∀ x, Sep S 80 x 1 → m11.mem x =
      match bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 with
      | none => m.mem x
      | some (_, e) => memStore32 m.mem (self + 8) e x := fun x hx => by
    rw [mem11 x (s32 _ _ hx), uX M5 x hx, hR]
    cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 with
    | none => exact M5out x hx
    | some pe => exact memStore32_congr (M5out x hx)
  have rsvC : ∀ {b : Word} {code : List Nat}, Sep S 80 b code.length → Sep (self + 8) 4 b code.length →
      CodeIn m.mem b code → CodeIn m11.mem b code := fun h1 h2 hc' i hi => by
    rw [m11x _ (h1.subR (c := i) (l := 1) (by omega))]
    cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 with
    | none => exact hc' i hi
    | some pe => exact (memStore32_get_sep (h2.subR (c := i) (l := 1) (by omega))).trans (hc' i hi)
  have hc11 := rsvC hSc hEc hc
  have hu11 := rsvC hSu hEu hu
  have hb11 := rsvC hSb hEb hb
  have fr11 := frU M5 m11.mem mem11
  have k11' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra → r ≠ sp →
      r ≠ 8 → r ≠ 9 → reg m11 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 =>
    (k11 r h0 h1 h2 h3 h4 h5 h6 h7).trans (keep10 r h0 hra' hsp' h8 h9)
  have s011 : reg m11 8 = out :=
    (k11 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans s010
  have s111 : reg m11 9 = self :=
    (k11 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans s110
  have ldO8 : ∀ (Mx : Word → BitVec 8) (a : Word) (v : BitVec 8) (k : Nat), k < 0x18 → a = out + BitVec.ofNat 32 k →
      ∀ c, 0x1C ≤ c → c + 4 ≤ 0x30 → memLoad32 (memStore8 Mx a v) (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) :=
    fun Mx a v k hk ha c h1 h2 => memLoad32_congr fun j hj => memStore8_ne (by
      rw [add_ofNat_assoc, hGS, add_ofNat_assoc, ha]; exact fun e => hOS k hk (32 + (c + j)) (by omega) e.symm)
  have ldO32 : ∀ (Mx : Word → BitVec 8) (v : Word) (k : Nat), k + 4 ≤ 0x18 →
      ∀ c, 0x1C ≤ c → c + 4 ≤ 0x30 → memLoad32 (memStore32 Mx (out + BitVec.ofNat 32 k) v) (G + BitVec.ofNat 32 c) =
        memLoad32 Mx (G + BitVec.ofNat 32 c) :=
    fun Mx v k hk c h1 h2 => memLoad32_store32_sep (by
      rw [hGS, add_ofNat_assoc]; exact (hOS.sub (c := k) (l := 4) hk).subR (c := 32 + c) (l := 4) (by omega))
  have tail40 : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx base mx 0x40 fx →
      CodeIn Mx base readWindowCode → fx 8 = out → fx sp = G →
      (∀ c, 0x1C ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c)) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra → r ≠ sp → r ≠ 8 →
        r ≠ 9 → r ≠ 18 → r ≠ 19 → fx r = reg m r) →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → reg m' r = reg m r) ∧
        m'.mem = memStore8 Mx out ((fx a1).extractLsb' 0 8) := by
    intro Mx mx fx s hcx h8 hs hF hk
    obtain ⟨n1, d1, u1⟩ := s.sb hcx rwin_at_40 (off' := 0x44) (by decide)
    rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out] at u1
    have hc1 := hcx.store8 (v := (fx a1).extractLsb' 0 8) (a := out)
      (by have := hOc.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this)
    have ld : ∀ c, 0x1C ≤ c → c + 4 ≤ 0x30 → memLoad32 (memStore8 Mx out ((fx a1).extractLsb' 0 8)) (G + BitVec.ofNat 32 c) =
        memLoad32 M5 (G + BitVec.ofNat 32 c) := fun c h1 h2 =>
      (ldO8 Mx out _ 0 (by omega) (add_ofNat_zero out).symm c h1 h2).trans (hF c h1 h2)
    have lA : memLoad32 (memStore8 Mx out ((fx a1).extractLsb' 0 8)) (G + 0x2C) = reg m ra := (ld 0x2C (by omega) (by omega)).trans fA
    have lB : memLoad32 (memStore8 Mx out ((fx a1).extractLsb' 0 8)) (G + 0x28) = reg m 8 := (ld 0x28 (by omega) (by omega)).trans fB
    have lC : memLoad32 (memStore8 Mx out ((fx a1).extractLsb' 0 8)) (G + 0x24) = reg m 9 := (ld 0x24 (by omega) (by omega)).trans fC
    have lD : memLoad32 (memStore8 Mx out ((fx a1).extractLsb' 0 8)) (G + 0x20) = reg m 18 := (ld 0x20 (by omega) (by omega)).trans fD
    have lE : memLoad32 (memStore8 Mx out ((fx a1).extractLsb' 0 8)) (G + 0x1C) = reg m 19 := (ld 0x1C (by omega) (by omega)).trans fE
    obtain ⟨n2, d2, u2⟩ := u1.lw hc1 rwin_at_44 (off' := 0x46) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0x2C) (by decide))
    rw [hs, lA] at u2
    obtain ⟨n3, d3, u3⟩ := u2.lw hc1 rwin_at_46 (off' := 0x48) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x28) (by decide))
    rw [show upd fx ra (reg m ra) sp = G by simp +decide only [upd]; exact hs, lB] at u3
    obtain ⟨n4, d4, u4⟩ := u3.lw hc1 rwin_at_48 (off' := 0x4A) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x24) (by decide))
    rw [show upd (upd fx ra (reg m ra)) 8 (reg m 8) sp = G by simp +decide only [upd]; exact hs, lC] at u4
    obtain ⟨n5, d5, u5⟩ := u4.lw hc1 rwin_at_4a (off' := 0x4C) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x20) (by decide))
    rw [show upd (upd (upd fx ra (reg m ra)) 8 (reg m 8)) 9 (reg m 9) sp = G by simp +decide only [upd]; exact hs,
      lD] at u5
    obtain ⟨n6, d6, u6⟩ := u5.lw hc1 rwin_at_4c (off' := 0x4E) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x1C) (by decide))
    rw [show upd (upd (upd (upd fx ra (reg m ra)) 8 (reg m 8)) 9 (reg m 9)) 18 (reg m 18) sp = G by
      simp +decide only [upd]; exact hs, lE] at u6
    obtain ⟨n7, d7, u7⟩ := u6.aluImm hc1 rwin_at_4e (off' := 0x50) (by decide)
    obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc1 rwin_at_50
    refine ⟨n8, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.single d8))))))), ?_, ?_,
      fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_, by rw [mem8]⟩
    · rw [pc8, add_lit_zero]; simp +decide only [upd, ite_true, ite_false]; rw [hra, hret]
    · rw [regs8]; simp +decide only [upd, ite_true, ite_false]; rw [hs, ← hspG]; rfl
    · rw [regs8]
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
      exact hk r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8' h9' h18 h19
  have us : ∀ (g : Fin 32 → Word) (r : Fin 32) (v : Word), r.val ≠ 0 → upd g r v r = v := fun g r v h => by
    simp only [upd, h, ↓reduceIte]
  have tail3A : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx base mx 0x3A fx →
      CodeIn Mx base readWindowCode → fx 8 = out → fx sp = G →
      (∀ c, 0x1C ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c)) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra → r ≠ sp → r ≠ 8 →
        r ≠ 9 → r ≠ 18 → r ≠ 19 → fx r = reg m r) →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → reg m' r = reg m r) ∧
        m'.mem = memStore8 (memStore8 Mx (out + 0x1) ((fx a0).extractLsb' 0 8)) out 1 := by
    intro Mx mx fx s hcx h8 hs hF hk
    have hzx := s.zero
    obtain ⟨n1, d1, u1⟩ := s.sb hcx rwin_at_3a (off' := 0x3E) (by decide)
    rw [h8] at u1
    have hc1 := hcx.store8 (v := (fx a0).extractLsb' 0 8) (a := out + 0x1) (hOc.sub (c := 1) (l := 1) (by omega))
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc1 rwin_at_3e (off' := 0x40) (by decide)
    obtain ⟨m', c', pc', sp', k', mem'⟩ := tail40 _ _ _ u2 hc1 (by rw [updz hzx (by decide)]; exact h8)
      (by rw [updz hzx (by decide)]; exact hs)
      (fun c h1 h2 => (ldO8 Mx _ _ 1 (by omega) rfl c h1 h2).trans (hF c h1 h2))
      (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8' h9 h18 h19 => by
        rw [updz hzx h1]; exact hk r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8' h9 h18 h19)
    refine ⟨m', .cons d1 (.cons d2 c'), pc', sp', k', ?_⟩
    rw [mem', us _ a1 _ (by decide), show fx x0 = 0 from hzx]; rfl
  have t11 : St m11.mem base m11 0x1A (reg m11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
  have hz11 : reg m11 0 = 0 := t11.zero
  have tag : m11.mem (G + 0x8) = u64Mem M5 (G + 8) self (G + 8) := mem11 _ (inG 8 (by omega))
  have pre := fun {mx : Machine} (c : Steps m11 mx) =>
    Steps.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9
      (c10.trans (c11.trans c))))))))))
  obtain ⟨n12, e12, t12⟩ := t11.lbu hc11 rwin_at_1a (off' := 0x1E) (by decide)
  rw [sp11, tag] at t12
  have frM11 : ∀ c, 0x1C ≤ c → c + 4 ≤ 0x30 → memLoad32 m11.mem (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c) :=
    fr11
  rcases hbr1 : bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 with _ | ⟨p, e⟩
  · obtain ⟨u0, u1', -⟩ := u64Mem_none (out := G + 8) (hR.trans hbr1)
    rw [u0] at t12
    obtain ⟨n13, e13, t13⟩ := t12.taken hc11 0x36 rwin_at_1e (by decide)
      (by rw [us _ a0 _ (by decide)]; exact (by decide : branchTaken .bne ((1 : BitVec 8).zeroExtend 32) 0 = true))
    obtain ⟨n14, e14, t14⟩ := t13.lbu hc11 rwin_at_36 (off' := 0x3A) (by decide)
    rw [updz hz11 (show sp ≠ a0 by decide), sp11, show G + (0x9 : Word) = G + 8 + 1 by rw [BitVec.add_assoc]; rfl,
      mem11 _ (by have := inG 9 (by omega); rwa [show G + BitVec.ofNat 32 9 = G + 8 + 1 by rw [BitVec.add_assoc]; rfl] at this),
      u1'] at t14
    obtain ⟨m', c', pc', sp', k', mem'⟩ := tail3A _ _ _ t14 hc11
      (by rw [updz t12.zero (by decide), updz hz11 (by decide)]; exact s011)
      (by rw [updz t12.zero (by decide), updz hz11 (by decide)]; exact sp11) frM11
      (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 _ _ => by
        rw [updz t12.zero h0, updz hz11 h0]; exact k11' r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9)
    refine ⟨m', pre (.cons e12 (.cons e13 (.cons e14 c'))), pc', sp', k', fun x hx => ?_⟩
    have mx : m11.mem x = m.mem x := by rw [m11x x hx, hbr1]
    rw [mem']; unfold windowMem; rw [hptr, hlen, hbr1]
    exact memStore8_congr (memStore8_congr mx)
  · obtain ⟨u0, uv0, uv4, -⟩ := u64Mem_some (out := G + 8) (hR.trans hbr1)
    obtain ⟨hp1, hle⟩ : ptr + memLoad32 m.mem (self + 8) = p ∧ (memLoad32 m.mem (self + 8)).toNat + 8 ≤ len.toNat := by
      have hb2 := hbr1
      rw [bytesResult_eq] at hb2
      split at hb2
      · next h => injection hb2 with h'; injection h' with h1 h2; exact ⟨h1, h⟩
      · cases hb2
    have pS : ∀ j, j < 8 → Sep S 80 (p + BitVec.ofNat 32 j) 1 := fun j hj => by
      rw [← hp1]
      have := (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
      rwa [← add_ofNat_assoc, Cur.ofNat_toNat_self] at this
    have hMp0 : memLoad32 M5 p = memLoad32 m.mem p := memLoad32_congr fun j hj => M5out _ (pS j (by omega))
    have hMp4 : memLoad32 M5 (p + 4) = memLoad32 m.mem (p + 4) := memLoad32_congr fun j hj => by
      rw [show p + 4 + BitVec.ofNat 32 j = p + BitVec.ofNat 32 (4 + j) by
        rw [show (p + 4 : Word) = p + BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
      exact M5out _ (pS (4 + j) (by omega))
    rw [u0] at t12
    obtain ⟨n13, e13, t13⟩ := t12.notTaken hc11 0x20 rwin_at_1e (by decide)
      (by rw [us _ a0 _ (by decide)]; exact (by decide : branchTaken .bne ((0 : BitVec 8).zeroExtend 32) 0 = false))
    have ld10 : memLoad32 m11.mem (G + 0x10) = memLoad32 m.mem p := by
      rw [show G + (0x10 : Word) = G + 8 + 8 by rw [BitVec.add_assoc]; rfl, ← hMp0, ← uv0]
      refine memLoad32_congr fun j hj => ?_
      rw [show G + 8 + 8 + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (16 + j) by
        rw [show (G + 8 + 8 : Word) = G + BitVec.ofNat 32 16 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]]
      exact mem11 _ (inG (16 + j) (by omega))
    have ld14 : memLoad32 m11.mem (G + 0x14) = memLoad32 m.mem (p + 4) := by
      rw [show G + (0x14 : Word) = G + 8 + 0xC by rw [BitVec.add_assoc]; rfl, ← hMp4, ← uv4]
      refine memLoad32_congr fun j hj => ?_
      rw [show G + 8 + 0xC + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (20 + j) by
        rw [show (G + 8 + 0xC : Word) = G + BitVec.ofNat 32 20 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]]
      exact mem11 _ (inG (20 + j) (by omega))
    obtain ⟨n14, e14, t14⟩ := t13.lw hc11 rwin_at_20 (off' := 0x22) (by decide)
      (by rw [updz hz11 (show sp ≠ a0 by decide), sp11]; exact aligned_add hGa (k := 0x10) (by decide))
    rw [updz hz11 (show sp ≠ a0 by decide), sp11, ld10] at t14
    obtain ⟨n15, e15, t15⟩ := t14.lw hc11 rwin_at_22 (off' := 0x24) (by decide)
      (by rw [updz t12.zero (show sp ≠ 18 by decide), updz hz11 (show sp ≠ a0 by decide), sp11]
          exact aligned_add hGa (k := 0x14) (by decide))
    rw [updz t12.zero (show sp ≠ 18 by decide), updz hz11 (show sp ≠ a0 by decide), sp11, ld14] at t15
    obtain ⟨n16, e16, t16⟩ := t15.aluImm hc11 rwin_at_24 (off' := 0x26) (by decide)
    obtain ⟨n17, e17, t17⟩ := t16.alu hc11 rwin_at_26 (off' := 0x28) (by decide)
    obtain ⟨m18, c18, pc18, mem18, regs18⟩ := t17.callRa (cb := base + 0x78) hc11 rwin_at_28 rwin_at_2c
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0x78 (by decide))
    have sp18 : reg m18 sp = G := by rw [regs18]; simp +decide only [upd, ite_true, ite_false]; exact sp11
    have a018 : reg m18 a0 = G + 8 := by rw [regs18]; simp +decide only [upd, ite_true, ite_false]; rw [sp11]; rfl
    have a118 : reg m18 a1 = self := by
      rw [regs18]; simp +decide only [upd, ite_true, ite_false]; rw [s111]; exact BitVec.zero_add self
    have ra18 : reg m18 ra = base + BitVec.ofNat 32 (0x28 + 8) := by rw [regs18]; simp +decide only [upd, ite_true, ite_false]
    have k18 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ ra → r ≠ 18 → r ≠ 19 → reg m18 r = reg m11 r := fun r h0 h1 h2 h3 h4 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; rw [regs18]; simp [upd, hz11]
      rw [regs18]; simp only [upd, hr, h0, h1, h2, h3, h4, ↓reduceIte]
    have s218 : reg m18 18 = memLoad32 m.mem p := by rw [regs18]; simp +decide only [upd, ite_true, ite_false]
    have s318 : reg m18 19 = memLoad32 m.mem (p + 4) := by rw [regs18]; simp +decide only [upd, ite_true, ite_false]
    have selfE : ∀ j, j < 12 → Sep S 80 (self + BitVec.ofNat 32 j) 1 := fun j hj => (hRS.sub (c := j) (l := 1) hj).symm
    have m11e : ∀ y, Sep S 80 y 1 → m11.mem y = memStore32 m.mem (self + 8) e y := fun y hy => by rw [m11x y hy, hbr1]
    have hl0 : memLoad32 m11.mem self = ptr := by
      rw [← hptr]; refine memLoad32_congr fun j hj => ?_
      rw [m11e _ (selfE j (by omega))]
      exact memStore32_get_sep (sep_offsets self (c := 8) (n := 4) (d := j) (k := 1) (Or.inr (by omega)) (by omega) (by omega))
    have hl4 : memLoad32 m11.mem (self + 4) = len := by
      rw [← hlen]; refine memLoad32_congr fun j hj => ?_
      rw [show self + 4 + BitVec.ofNat 32 j = self + BitVec.ofNat 32 (4 + j) by
        rw [show (self + 4 : Word) = self + BitVec.ofNat 32 4 from rfl, add_ofNat_assoc], m11e _ (selfE (4 + j) (by omega))]
      exact memStore32_get_sep (sep_offsets self (c := 8) (n := 4) (d := 4 + j) (k := 1) (Or.inr (by omega)) (by omega) (by omega))
    have hl8 : memLoad32 m11.mem (self + 8) = e := by
      rw [show memLoad32 m11.mem (self + 8) = memLoad32 (memStore32 m.mem (self + 8) e) (self + 8) from
        memLoad32_congr fun j hj => by
          rw [show self + 8 + BitVec.ofNat 32 j = self + BitVec.ofNat 32 (8 + j) by
            rw [show (self + 8 : Word) = self + BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]]
          exact m11e _ (selfE (8 + j) (by omega))]
      exact memLoad32_store32_same _ _ _
    obtain ⟨m19, c19, pc19, sp19, k19, mem19⟩ := readerU64_correct m18 (base := base + 0x78)
      (retAddr := base + BitVec.ofNat 32 (0x28 + 8)) (out := G + 8) (self := self)
      (by rw [mem18]; exact hu11) (by rw [mem18]; exact hb11)
      (even_at base hbase 0x78 (by decide)) pc18 a018 a118 ra18
      (even_clear _ (even_at base hbase (0x28 + 8) (by decide)))
      (by rw [sp18]; exact hGa) hself (aligned_add hGa (k := 8) (by decide)) (by rw [mem18, hl0, hl4]; exact hbuf)
      (by rw [sp18]; exact s32 _ _ hSu) (by rw [sp18]; exact s32 _ _ hSb)
      (fr 8 16 (by omega) _ _ hSu) hEb hEu
      (by rw [sp18]; exact s32R hRS) (by rw [sp18]; exact hO16) (by rw [mem18, hl0, hl4, sp18]; exact s32R hBS)
      (by rw [mem18, hl0, hl4]; exact hBE)
    rw [sp18, mem18] at mem19
    rw [sp18] at sp19
    have hR2 : bytesResult (memLoad32 m11.mem self) (memLoad32 m11.mem (self + 4)) (memLoad32 m11.mem (self + 8)) 8 =
        bytesResult ptr len e 8 := by rw [hl0, hl4, hl8]
    have frM19 : ∀ c, 0x1C ≤ c → c + 4 ≤ 0x30 → memLoad32 m19.mem (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => (frU m11.mem m19.mem mem19 c h1 h2).trans (fr11 c h1 h2)
    have m19x : ∀ x, Sep S 80 x 1 → m19.mem x =
        match bytesResult ptr len e 8 with
        | none => m11.mem x
        | some (_, e') => memStore32 m11.mem (self + 8) e' x := fun x hx => by
      rw [mem19 x (s32 _ _ hx), uX m11.mem x hx, hR2]
    have rsv19 : ∀ {b : Word} {code : List Nat}, Sep S 80 b code.length → Sep (self + 8) 4 b code.length →
        CodeIn m11.mem b code → CodeIn m19.mem b code := fun h1 h2 hc' i hi => by
      rw [m19x _ (h1.subR (c := i) (l := 1) (by omega))]
      cases bytesResult ptr len e 8 with
      | none => exact hc' i hi
      | some pe => exact (memStore32_get_sep (h2.subR (c := i) (l := 1) (by omega))).trans (hc' i hi)
    have hc19 := rsv19 hSc hEc hc11
    have k19' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → reg m19 r = reg m18 r := k19
    have s019 : reg m19 8 = out :=
      (k19' 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((k18 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s011)
    have s219 : reg m19 18 = memLoad32 m.mem p :=
      (k19' 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans s218
    have s319 : reg m19 19 = memLoad32 m.mem (p + 4) :=
      (k19' 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans s318
    have kk19 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra → r ≠ sp →
        r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → reg m19 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19 =>
      (k19' r h0 h1 h2 h3 h4 h5 h6 h7).trans ((k18 r h0 h1 hra' h18 h19).trans (k11' r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9))
    have t19 : St m19.mem base m19 0x30 (reg m19) := ⟨by rw [pc19], rfl, fun _ => rfl⟩
    have hz19 : reg m19 0 = 0 := t19.zero
    have tag2 : m19.mem (G + 0x8) = u64Mem m11.mem (G + 8) self (G + 8) := mem19 _ (inG 8 (by omega))
    obtain ⟨n20, e20, t20⟩ := t19.lbu hc19 rwin_at_30 (off' := 0x34) (by decide)
    rw [sp19, tag2] at t20
    have pre19 : Steps m11 m19 := .cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17 (c18.trans c19))))))
    rcases hbr2 : bytesResult ptr len e 8 with _ | ⟨q, e'⟩
    · obtain ⟨w0, w1, -⟩ := u64Mem_none (out := G + 8) (hR2.trans hbr2)
      rw [w0] at t20
      obtain ⟨n21, e21, t21⟩ := t20.notTaken hc19 0x36 rwin_at_34 (by decide)
        (by rw [us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq ((1 : BitVec 8).zeroExtend 32) 0 = false))
      obtain ⟨n22, e22, t22⟩ := t21.lbu hc19 rwin_at_36 (off' := 0x3A) (by decide)
      rw [updz hz19 (show sp ≠ a0 by decide), sp19, show G + (0x9 : Word) = G + 8 + 1 by rw [BitVec.add_assoc]; rfl,
        mem19 _ (by have := inG 9 (by omega); rwa [show G + BitVec.ofNat 32 9 = G + 8 + 1 by rw [BitVec.add_assoc]; rfl] at this),
        w1] at t22
      obtain ⟨m', c', pc', sp', k', mem'⟩ := tail3A _ _ _ t22 hc19
        (by rw [updz t20.zero (by decide), updz hz19 (by decide)]; exact s019)
        (by rw [updz t20.zero (by decide), updz hz19 (by decide)]; exact sp19) frM19
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19 => by
          rw [updz t20.zero h0, updz hz19 h0]; exact kk19 r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19)
      refine ⟨m', pre (pre19.trans (.cons e20 (.cons e21 (.cons e22 c')))), pc', sp', k', fun x hx => ?_⟩
      have mx : m19.mem x = memStore32 m.mem (self + 8) e x := by rw [m19x x hx, hbr2]; exact m11e x hx
      rw [mem']; unfold windowMem; rw [hptr, hlen, hbr1]; dsimp only; rw [hbr2]
      exact memStore8_congr (memStore8_congr mx)
    · obtain ⟨w0, wv0, wv4, -⟩ := u64Mem_some (out := G + 8) (hR2.trans hbr2)
      obtain ⟨hq1, hle2⟩ : ptr + e = q ∧ e.toNat + 8 ≤ len.toNat := by
        have hb2 := hbr2
        rw [bytesResult_eq] at hb2
        split at hb2
        · next h => injection hb2 with h'; injection h' with h1 h2; exact ⟨h1, h⟩
        · cases hb2
      have qS : ∀ j, j < 8 → Sep S 80 (q + BitVec.ofNat 32 j) 1 := fun j hj => by
        rw [← hq1]
        have := (hBS.sub (c := e.toNat + j) (l := 1) (by omega)).symm
        rwa [← add_ofNat_assoc, Cur.ofNat_toNat_self] at this
      have qE : ∀ j, j < 8 → Sep (self + 8) 4 (q + BitVec.ofNat 32 j) 1 := fun j hj => by
        rw [← hq1]
        have := (hBE.sub (c := e.toNat + j) (l := 1) (by omega)).symm
        rwa [← add_ofNat_assoc, Cur.ofNat_toNat_self] at this
      have hMq0 : memLoad32 m11.mem q = memLoad32 m.mem q := memLoad32_congr fun j hj =>
        (m11e _ (qS j (by omega))).trans (memStore32_get_sep (qE j (by omega)))
      have hMq4 : memLoad32 m11.mem (q + 4) = memLoad32 m.mem (q + 4) := memLoad32_congr fun j hj => by
        rw [show q + 4 + BitVec.ofNat 32 j = q + BitVec.ofNat 32 (4 + j) by
          rw [show (q + 4 : Word) = q + BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]]
        exact (m11e _ (qS (4 + j) (by omega))).trans (memStore32_get_sep (qE (4 + j) (by omega)))
      have ld10' : memLoad32 m19.mem (G + 0x10) = memLoad32 m.mem q := by
        rw [show G + (0x10 : Word) = G + 8 + 8 by rw [BitVec.add_assoc]; rfl, ← hMq0, ← wv0]
        refine memLoad32_congr fun j hj => ?_
        rw [show G + 8 + 8 + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (16 + j) by
          rw [show (G + 8 + 8 : Word) = G + BitVec.ofNat 32 16 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]]
        exact mem19 _ (inG (16 + j) (by omega))
      have ld14' : memLoad32 m19.mem (G + 0x14) = memLoad32 m.mem (q + 4) := by
        rw [show G + (0x14 : Word) = G + 8 + 0xC by rw [BitVec.add_assoc]; rfl, ← hMq4, ← wv4]
        refine memLoad32_congr fun j hj => ?_
        rw [show G + 8 + 0xC + BitVec.ofNat 32 j = G + BitVec.ofNat 32 (20 + j) by
          rw [show (G + 8 + 0xC : Word) = G + BitVec.ofNat 32 20 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]]
        exact mem19 _ (inG (20 + j) (by omega))
      have m19e : ∀ x, Sep S 80 x 1 → m19.mem x = memStore32 m.mem (self + 8) e' x := fun x hx => by
        rw [m19x x hx, hbr2]; dsimp only
        exact (memStore32_congr (m11e x hx)).trans (memStore32_overwrite _ _ _ _ _)
      rw [w0] at t20
      obtain ⟨n21, e21, t21⟩ := t20.taken hc19 0x52 rwin_at_34 (by decide)
        (by rw [us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq ((0 : BitVec 8).zeroExtend 32) 0 = true))
      obtain ⟨n22, e22, t22⟩ := t21.lw hc19 rwin_at_52 (off' := 0x54) (by decide)
        (by rw [updz hz19 (show sp ≠ a0 by decide), sp19]; exact aligned_add hGa (k := 0x14) (by decide))
      rw [updz hz19 (show sp ≠ a0 by decide), sp19, ld14'] at t22
      obtain ⟨n23, e23, t23⟩ := t22.lw hc19 rwin_at_54 (off' := 0x56) (by decide)
        (by rw [updz t20.zero (show sp ≠ a0 by decide), updz hz19 (show sp ≠ a0 by decide), sp19]
            exact aligned_add hGa (k := 0x10) (by decide))
      rw [updz t20.zero (show sp ≠ a0 by decide), updz hz19 (show sp ≠ a0 by decide), sp19, ld10'] at t23
      have va0 : reg n23 a0 = memLoad32 m.mem (q + 4) := by rw [t23.regs]; simp +decide only [upd, ite_true, ite_false]
      have va2 : reg n23 a2 = memLoad32 m.mem q := by rw [t23.regs]; simp +decide only [upd, ite_true, ite_false]
      have v18 : reg n23 18 = memLoad32 m.mem p := by rw [t23.regs]; simp +decide only [upd, ite_false]; exact s219
      have v19 : reg n23 19 = memLoad32 m.mem (p + 4) := by
        rw [t23.regs]; simp +decide only [upd, ite_false]; exact s319
      have v8 : reg n23 8 = out := by rw [t23.regs]; simp +decide only [upd, ite_false]; exact s019
      have vsp : reg n23 sp = G := by rw [t23.regs]; simp +decide only [upd, ite_false]; exact sp19
      have vk : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra → r ≠ sp →
          r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → reg n23 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19 => by
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; rw [t23.self.zero, hz]
        rw [t23.regs]; simp only [upd, hr, h0, h2, ↓reduceIte]
        exact kk19 r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19
      have u23 := t23.self
      have pre23 : Steps m11 n23 := pre19.trans (.cons e20 (.cons e21 (.cons e22 (.single e23))))
      have err74 : ∀ (mx : Machine) (fx : Fin 32 → Word), Steps n23 mx → St m19.mem base mx 0x74 fx → fx 8 = out →
          fx sp = G → (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra →
            r ≠ sp → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → fx r = reg m r) →
          (memLoad32 m.mem (q + 4)).toNat * 2 ^ 32 + (memLoad32 m.mem q).toNat <
            (memLoad32 m.mem (p + 4)).toNat * 2 ^ 32 + (memLoad32 m.mem p).toNat →
          ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
            (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → reg m' r = reg m r) ∧
            ∀ x, Sep S 80 x 1 → m'.mem x = windowMem m.mem out self x := by
        intro mx fx c s h8 hs hk hcond
        obtain ⟨n1, d1, u1⟩ := s.aluImm hc19 rwin_at_74 (off' := 0x76) (by decide)
        obtain ⟨n2, d2, u2⟩ := u1.jump hc19 rwin_at_76 (off' := 0x3A) (by decide)
          (by rw [u1.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x3A (by decide)))
        obtain ⟨m', c', pc', sp', k', mem'⟩ := tail3A _ _ _ u2 hc19 (by rw [updz s.zero (by decide)]; exact h8)
          (by rw [updz s.zero (by decide)]; exact hs) frM19
          (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8' h9 h18 h19 => by
            rw [updz s.zero h0]; exact hk r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8' h9 h18 h19)
        refine ⟨m', pre (pre23.trans (c.trans (.cons d1 (.cons d2 c')))), pc', sp', k', fun x hx => ?_⟩
        rw [mem', us _ a0 _ (by decide), show fx x0 = 0 from s.zero]
        unfold windowMem; rw [hptr, hlen, hbr1]; dsimp only; rw [hbr2]; dsimp only; simp only [hcond, ↓reduceIte]
        exact memStore8_congr (memStore8_congr (m19e x hx))
      have store60 : ∀ (mx : Machine) (fx : Fin 32 → Word), Steps n23 mx → St m19.mem base mx 0x60 fx → fx 8 = out →
          fx sp = G → fx 18 = memLoad32 m.mem p → fx 19 = memLoad32 m.mem (p + 4) → fx a2 = memLoad32 m.mem q →
          fx a0 = memLoad32 m.mem (q + 4) → (fx a1).extractLsb' 0 8 = 0 →
          (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra →
            r ≠ sp → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → fx r = reg m r) →
          ¬ ((memLoad32 m.mem (q + 4)).toNat * 2 ^ 32 + (memLoad32 m.mem q).toNat <
            (memLoad32 m.mem (p + 4)).toNat * 2 ^ 32 + (memLoad32 m.mem p).toNat) →
          ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
            (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → reg m' r = reg m r) ∧
            ∀ x, Sep S 80 x 1 → m'.mem x = windowMem m.mem out self x := by
        intro mx fx c s h8 hs h18 h19 ha2 ha0' ha1' hk hcond
        obtain ⟨n1, d1, u1⟩ := s.sw hc19 rwin_at_60 (off' := 0x64) (by decide)
          (by rw [h8]; exact aligned_add hout (k := 8) (by decide))
        rw [h8, h18] at u1
        have hc1 := hc19.store32 (v := memLoad32 m.mem p) (a := out + 0x8) (hOc.sub (c := 8) (l := 4) (by omega))
        obtain ⟨n2, d2, u2⟩ := u1.sw hc1 rwin_at_64 (off' := 0x68) (by decide)
          (by rw [h8]; exact aligned_add hout (k := 0xC) (by decide))
        rw [h8, h19] at u2
        have hc2 := hc1.store32 (v := memLoad32 m.mem (p + 4)) (a := out + 0xC) (hOc.sub (c := 0xC) (l := 4) (by omega))
        obtain ⟨n3, d3, u3⟩ := u2.sw hc2 rwin_at_68 (off' := 0x6A) (by decide)
          (by rw [h8]; exact aligned_add hout (k := 0x10) (by decide))
        rw [h8, ha2] at u3
        have hc3 := hc2.store32 (v := memLoad32 m.mem q) (a := out + 0x10) (hOc.sub (c := 0x10) (l := 4) (by omega))
        obtain ⟨n4, d4, u4⟩ := u3.sw hc3 rwin_at_6a (off' := 0x6C) (by decide)
          (by rw [h8]; exact aligned_add hout (k := 0x14) (by decide))
        rw [h8, ha0'] at u4
        have hc4 := hc3.store32 (v := memLoad32 m.mem (q + 4)) (a := out + 0x14) (hOc.sub (c := 0x14) (l := 4) (by omega))
        obtain ⟨n5, d5, u5⟩ := u4.jump hc4 rwin_at_6c (off' := 0x40) (by decide)
          (by rw [u4.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x40 (by decide)))
        obtain ⟨m', c', pc', sp', k', mem'⟩ := tail40 _ _ _ u5 hc4 h8 hs
          (fun c h1 h2 => (ldO32 _ _ 0x14 (by omega) c h1 h2).trans ((ldO32 _ _ 0x10 (by omega) c h1 h2).trans
            ((ldO32 _ _ 0xC (by omega) c h1 h2).trans ((ldO32 _ _ 8 (by omega) c h1 h2).trans (frM19 c h1 h2))))) hk
        refine ⟨m', pre (pre23.trans (c.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c'))))))), pc', sp', k',
          fun x hx => ?_⟩
        rw [mem', ha1']
        unfold windowMem; rw [hptr, hlen, hbr1]; dsimp only; rw [hbr2]; dsimp only; simp only [hcond, ↓reduceIte]
        exact memStore8_congr (memStore32_congr (memStore32_congr (memStore32_congr (memStore32_congr (m19e x hx)))))
      have hlt0 := (memLoad32 m.mem q).isLt
      have hlt1 := (memLoad32 m.mem p).isLt
      by_cases heq : memLoad32 m.mem (p + 4) = memLoad32 m.mem (q + 4)
      · have heqn := congrArg BitVec.toNat heq
        obtain ⟨n24, e24, t24⟩ := u23.taken hc19 0x6E rwin_at_56 (by decide)
          (by rw [v19, va0, heq]; exact bt_beq_self _)
        obtain ⟨n25, e25, t25⟩ := t24.alu hc19 rwin_at_6e (off' := 0x72) (by decide)
        rw [va2, v18] at t25
        by_cases hl : (memLoad32 m.mem q).ult (memLoad32 m.mem p) = true
        · obtain ⟨n26, e26, t26⟩ := t25.notTaken hc19 0x74 rwin_at_72 (by decide)
            (by
              rw [us _ a1 _ (by decide)]
              show ((if (memLoad32 m.mem q).ult (memLoad32 m.mem p) = true then (1 : Word) else 0) == 0) = false
              simp only [hl, ↓reduceIte]; decide)
          have hl' : (memLoad32 m.mem q).toNat < (memLoad32 m.mem p).toNat := of_decide_eq_true hl
          exact err74 n26 _ (.cons e24 (.cons e25 (.single e26))) t26
            (by rw [updz u23.zero (by decide)]; exact v8) (by rw [updz u23.zero (by decide)]; exact vsp)
            (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19 => by
              rw [updz u23.zero h1]; exact vk r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19)
            (by omega)
        · obtain ⟨n26, e26, t26⟩ := t25.taken hc19 0x60 rwin_at_72 (by decide)
            (by
              rw [us _ a1 _ (by decide)]
              show ((if (memLoad32 m.mem q).ult (memLoad32 m.mem p) = true then (1 : Word) else 0) == 0) = true
              simp only [hl]; decide)
          have hl' : ¬ (memLoad32 m.mem q).toNat < (memLoad32 m.mem p).toNat := fun h => hl (decide_eq_true h)
          exact store60 n26 _ (.cons e24 (.cons e25 (.single e26))) t26
            (by rw [updz u23.zero (by decide)]; exact v8) (by rw [updz u23.zero (by decide)]; exact vsp)
            (by rw [updz u23.zero (by decide)]; exact v18) (by rw [updz u23.zero (by decide)]; exact v19)
            (by rw [updz u23.zero (by decide)]; exact va2) (by rw [updz u23.zero (by decide)]; exact va0)
            (by
              rw [us _ a1 _ (by decide)]
              show (if (memLoad32 m.mem q).ult (memLoad32 m.mem p) = true then (1 : Word) else 0).extractLsb' 0 8 = 0
              simp only [hl]; rfl)
            (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19 => by
              rw [updz u23.zero h1]; exact vk r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19)
            (by omega)
      · obtain ⟨n24, e24, t24⟩ := u23.notTaken hc19 0x5A rwin_at_56 (by decide)
          (by rw [v19, va0]; exact beq_eq_false_iff_ne.mpr heq)
        obtain ⟨n25, e25, t25⟩ := t24.alu hc19 rwin_at_5a (off' := 0x5E) (by decide)
        rw [va0, v19] at t25
        by_cases hl : (memLoad32 m.mem (q + 4)).ult (memLoad32 m.mem (p + 4)) = true
        · obtain ⟨n26, e26, t26⟩ := t25.taken hc19 0x74 rwin_at_5e (by decide)
            (by
              rw [us _ a1 _ (by decide)]
              show ((if (memLoad32 m.mem (q + 4)).ult (memLoad32 m.mem (p + 4)) = true then (1 : Word) else 0) != 0) = true
              simp only [hl, ↓reduceIte]; decide)
          have hl' : (memLoad32 m.mem (q + 4)).toNat < (memLoad32 m.mem (p + 4)).toNat := of_decide_eq_true hl
          exact err74 n26 _ (.cons e24 (.cons e25 (.single e26))) t26
            (by rw [updz u23.zero (by decide)]; exact v8) (by rw [updz u23.zero (by decide)]; exact vsp)
            (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19 => by
              rw [updz u23.zero h1]; exact vk r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19)
            (by omega)
        · obtain ⟨n26, e26, t26⟩ := t25.notTaken hc19 0x60 rwin_at_5e (by decide)
            (by
              rw [us _ a1 _ (by decide)]
              show ((if (memLoad32 m.mem (q + 4)).ult (memLoad32 m.mem (p + 4)) = true then (1 : Word) else 0) != 0) = false
              simp only [hl]; decide)
          have hl' : ¬ (memLoad32 m.mem (q + 4)).toNat < (memLoad32 m.mem (p + 4)).toNat := fun h => hl (decide_eq_true h)
          have hne' : (memLoad32 m.mem (p + 4)).toNat ≠ (memLoad32 m.mem (q + 4)).toNat := fun h =>
            heq (BitVec.eq_of_toNat_eq h)
          exact store60 n26 _ (.cons e24 (.cons e25 (.single e26))) t26
            (by rw [updz u23.zero (by decide)]; exact v8) (by rw [updz u23.zero (by decide)]; exact vsp)
            (by rw [updz u23.zero (by decide)]; exact v18) (by rw [updz u23.zero (by decide)]; exact v19)
            (by rw [updz u23.zero (by decide)]; exact va2) (by rw [updz u23.zero (by decide)]; exact va0)
            (by
              rw [us _ a1 _ (by decide)]
              show (if (memLoad32 m.mem (q + 4)).ult (memLoad32 m.mem (p + 4)) = true then (1 : Word) else 0).extractLsb' 0 8 = 0
              simp only [hl]; rfl)
            (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19 => by
              rw [updz u23.zero h1]; exact vk r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 h18 h19)
            (by omega)

end C3.RV32

