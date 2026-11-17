import C3BootProofs.Proofs.ImageHelpers
import C3BootProofs.Proofs.SmallFns
import C3BootProofs.Proofs.ReaderArray

/-!
# Small functions of the key-set reader

`keys::read_signatures(r)` reads a signature count with `Reader::u8` and
takes that many 65-byte signatures with `Reader::bytes`, as
`Result<&[u8], Error>`: a pointer, null for `Err`, and the length or the
error byte. The count must be 2, 3, or 4; another count is `OutOfRange` (5).
-/

namespace C3.RV32

open C3.Image

/-- Memory after `read_signatures` returns, outside the stack it uses. -/
def readSigsMem (M : Word → BitVec 8) (out self : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 1 with
  | none => memStore8 (memStore32 M out 0) (out + 4) 0
  | some (p, e) =>
    if 2 ≤ (M p).toNat ∧ (M p).toNat ≤ 4 then
      bytesMem (memStore32 M (self + 8) e) out self ((M p).zeroExtend 32 * 65)
    else memStore8 (memStore32 (memStore32 M (self + 8) e) out 0) (out + 4) 5

theorem rsg_at_0 : fetchRel readSignaturesCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem rsg_at_2 : fetchRel readSignaturesCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem rsg_at_4 : fetchRel readSignaturesCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem rsg_at_6 : fetchRel readSignaturesCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem rsg_at_8 : fetchRel readSignaturesCode 0x8 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem rsg_at_a : fetchRel readSignaturesCode 0xA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem rsg_at_c : fetchRel readSignaturesCode 0xC = some (.alu .add a0 x0 a1, 2) := by decide
theorem rsg_at_e : fetchRel readSignaturesCode 0xE = some (.auipc ra 0x0, 4) := by decide
theorem rsg_at_12 : fetchRel readSignaturesCode 0x12 = some (.jalr ra ra 0xFFFFFF80, 4) := by decide
theorem rsg_at_16 : fetchRel readSignaturesCode 0x16 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem rsg_at_18 : fetchRel readSignaturesCode 0x18 = some (.branch .beq a0 x0 0xC, 2) := by decide
theorem rsg_at_1a : fetchRel readSignaturesCode 0x1A = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem rsg_at_1e : fetchRel readSignaturesCode 0x1E = some (.store .sb (8 : Fin 32) a1 0x4, 4) := by decide
theorem rsg_at_22 : fetchRel readSignaturesCode 0x22 = some (.jal x0 0x38, 2) := by decide
theorem rsg_at_24 : fetchRel readSignaturesCode 0x24 = some (.aluImm .add a0 a1 0xFFFFFFFE, 4) := by decide
theorem rsg_at_28 : fetchRel readSignaturesCode 0x28 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem rsg_at_2c : fetchRel readSignaturesCode 0x2C = some (.aluImm .add a2 x0 0x3, 2) := by decide
theorem rsg_at_2e : fetchRel readSignaturesCode 0x2E = some (.branch .bgeu a0 a2 0x22, 4) := by decide
theorem rsg_at_32 : fetchRel readSignaturesCode 0x32 = some (.aluImm .and a2 a1 0xFF, 4) := by decide
theorem rsg_at_36 : fetchRel readSignaturesCode 0x36 = some (.aluImm .sll a0 a2 0x6, 4) := by decide
theorem rsg_at_3a : fetchRel readSignaturesCode 0x3A = some (.alu .add a2 a2 a0, 2) := by decide
theorem rsg_at_3c : fetchRel readSignaturesCode 0x3C = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem rsg_at_3e : fetchRel readSignaturesCode 0x3E = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem rsg_at_40 : fetchRel readSignaturesCode 0x40 = some (.load .lw ra sp 0xC, 2) := by decide
theorem rsg_at_42 : fetchRel readSignaturesCode 0x42 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem rsg_at_44 : fetchRel readSignaturesCode 0x44 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem rsg_at_46 : fetchRel readSignaturesCode 0x46 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem rsg_at_48 : fetchRel readSignaturesCode 0x48 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem rsg_at_4c : fetchRel readSignaturesCode 0x4C = some (.jalr x0 (6 : Fin 32) 0x1C, 4) := by decide
theorem rsg_at_50 : fetchRel readSignaturesCode 0x50 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem rsg_at_52 : fetchRel readSignaturesCode 0x52 = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem rsg_at_56 : fetchRel readSignaturesCode 0x56 = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem rsg_at_5a : fetchRel readSignaturesCode 0x5A = some (.load .lw ra sp 0xC, 2) := by decide
theorem rsg_at_5c : fetchRel readSignaturesCode 0x5C = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem rsg_at_5e : fetchRel readSignaturesCode 0x5E = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem rsg_at_60 : fetchRel readSignaturesCode 0x60 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem rsg_at_62 : fetchRel readSignaturesCode 0x62 = some (.jalr x0 ra 0x0, 2) := by decide

theorem sig_range : ∀ b : BitVec 8,
    (aluEval .and (aluEval .add (b.zeroExtend 32) 0xFFFFFFFE) 0xFF).ult 3 = decide (2 ≤ b.toNat ∧ b.toNat ≤ 4) := by
  decide

theorem sig_len : ∀ b : BitVec 8,
    aluEval .add (b.zeroExtend 32) (aluEval .sll (b.zeroExtend 32) 6) = b.zeroExtend 32 * 65 := by decide

theorem upd_x0 (g : Fin 32 → Word) (r : Fin 32) (v : Word) : upd g r v x0 = 0 := rfl

/-- `Reader::bytes`'s memory at `x` depends only on `x` and the reader. -/
theorem bytesMem_congr {M M' : Word → BitVec 8} {out self n x : Word} (hx : M x = M' x)
    (hs : ∀ j, j < 12 → M (self + BitVec.ofNat 32 j) = M' (self + BitVec.ofNat 32 j)) :
    bytesMem M out self n x = bytesMem M' out self n x := by
  have ld : ∀ c, c + 4 ≤ 12 → memLoad32 M (self + BitVec.ofNat 32 c) = memLoad32 M' (self + BitVec.ofNat 32 c) :=
    fun c hc => (memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact (hs (c + j) (by omega)).symm).symm
  have l0 : memLoad32 M self = memLoad32 M' self := by have := ld 0 (by omega); rwa [add_ofNat_zero] at this
  have l4 : memLoad32 M (self + 4) = memLoad32 M' (self + 4) := ld 4 (by omega)
  have l8 : memLoad32 M (self + 8) = memLoad32 M' (self + 8) := ld 8 (by omega)
  unfold bytesMem; rw [l0, l4, l8]
  cases bytesResult (memLoad32 M' self) (memLoad32 M' (self + 4)) (memLoad32 M' (self + 8)) n with
  | none => exact memStore8_congr (memStore32_congr hx)
  | some pe => exact memStore32_congr (memStore32_congr (memStore32_congr hx))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`keys::read_signatures`, as compiled**: with `Reader::u8` and
`Reader::bytes` where the image puts them, a reader `self` over a slice that
is not null and doesn't wrap, a result address `out`, and 32 bytes of stack
below `sp`, all apart as the hypotheses list, it returns to `ra` with the
registers but `a0` through `a5` and `t1` restored, and memory outside its
stack as `readSigsMem` says. -/
theorem readSignatures_correct (m : Machine) {base retAddr out self : Word}
    (hc : CodeIn m.mem base readSignaturesCode) (hu : CodeIn m.mem (base + 0xFFFFFF8E) readerU8Code)
    (hb : CodeIn m.mem (base + 0x64) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = self)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hself : self.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSc : Sep (reg m sp + 0xFFFFFFE0) 32 base readSignaturesCode.length)
    (hSu : Sep (reg m sp + 0xFFFFFFE0) 32 (base + 0xFFFFFF8E) readerU8Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFE0) 32 (base + 0x64) readerBytesCode.length)
    (hOc : Sep out 8 base readSignaturesCode.length) (hOb : Sep out 8 (base + 0x64) readerBytesCode.length)
    (hEu : Sep (self + 8) 4 (base + 0xFFFFFF8E) readerU8Code.length)
    (hEb : Sep (self + 8) 4 (base + 0x64) readerBytesCode.length)
    (hEc : Sep (self + 8) 4 base readSignaturesCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFE0) 32) (hOS : Sep out 8 (reg m sp + 0xFFFFFFE0) 32)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFE0) 32)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 6 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFE0) 32 x 1 → m'.mem x = readSigsMem m.mem out self x := by
  obtain ⟨S, hSd⟩ : ∃ S, reg m sp + 0xFFFFFFE0 = S := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hSd] at hSc hSu hSb hRS hOS hBS ⊢
  have hGS : G = S + BitVec.ofNat 32 16 := by rw [← hGd, ← hSd, BitVec.add_assoc]; rfl
  have hSG : G + 0xFFFFFFF0 = S := by rw [← hGd, ← hSd, BitVec.add_assoc]; rfl
  have hspG : G + 0x10 = reg m sp := by rw [← hGd, BitVec.add_assoc]; exact BitVec.add_zero _
  have hGa : G.toNat % 4 = 0 := hGd ▸ aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  have fr : ∀ c l, c + l ≤ 16 → ∀ (x : Word) (n : Nat), Sep S 32 x n → Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := 16 + c) (l := l) (by omega)
  have s16 : ∀ (x : Word) (n : Nat), Sep S 32 x n → Sep (G + 0xFFFFFFF0) 16 x n := fun x n hx => by
    rw [hSG]; have := hx.sub (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at this
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the frame
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc rsg_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc rsg_at_2 (off' := 4) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (fr 0xC 4 (by omega) _ _ hSc)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 rsg_at_4 (off' := 6) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (fr 8 4 (by omega) _ _ hSc)
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 rsg_at_6 (off' := 8) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 4) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 (memStore32 m.mem (G + 0xC) (reg m ra)) (G + 8) (reg m 8)) (G + 4)
      (reg m 9) = M3 := ⟨_, rfl⟩
  rw [hM3] at t4
  have M3out : ∀ x, Sep S 32 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3]
    exact (memStore32_get_sep (fr 4 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 8 4 (by omega) x 1 hx)).trans
      (memStore32_get_sep (fr 0xC 4 (by omega) x 1 hx)))
  have codeOut : ∀ {b : Word} {code : List Nat}, Sep S 32 b code.length → CodeIn m.mem b code → CodeIn M3 b code :=
    fun h hc' i hi => by rw [M3out _ (h.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have hc4 := codeOut hSc hc
  have ldS : ∀ c, c + 4 ≤ 12 → memLoad32 M3 (self + BitVec.ofNat 32 c) = memLoad32 m.mem (self + BitVec.ofNat 32 c) :=
    fun c hc' => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact M3out _ ((hRS.sub (c := c + j) (l := 1) (by omega)).symm)
  have l0 : memLoad32 M3 self = memLoad32 m.mem self := by have := ldS 0 (by omega); rwa [add_ofNat_zero] at this
  have l4 : memLoad32 M3 (self + 4) = memLoad32 m.mem (self + 4) := ldS 4 (by omega)
  have l8 : memLoad32 M3 (self + 8) = memLoad32 m.mem (self + 8) := ldS 8 (by omega)
  have inG : ∀ c, c < 16 → Sep (G + 0xFFFFFFF0) 16 (G + BitVec.ofNat 32 c) 1 := fun c hc' => by
    rw [hSG, hGS, add_ofNat_assoc]
    have := sep_offsets S (c := 0) (n := 16) (d := 16 + c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have sR16 : ∀ {a : Word} {n : Nat}, Sep a n S 32 → Sep a n S 16 := fun h => by
    have := h.subR (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at this
  obtain ⟨m5, e5, t5⟩ := t4.alu hc4 rsg_at_8 (off' := 0xA) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.alu hc4 rsg_at_a (off' := 0xC) (by decide)
  obtain ⟨m7, e7, t7⟩ := t6.alu hc4 rsg_at_c (off' := 0xE) (by decide)
  obtain ⟨m8, c8, pc8, mem8, regs8⟩ := t7.callRa (cb := base + 0xFFFFFF8E) hc4 rsg_at_e rsg_at_12
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xFFFFFF8E (by decide))
  have sp8 : reg m8 sp = G := by rw [regs8]; simp +decide [upd]
  have a08 : reg m8 a0 = self := by rw [regs8]; simp +decide [upd, aluEval, ha1]
  have s08 : reg m8 8 = out := by rw [regs8]; simp +decide [upd, aluEval, ha0]
  have s18 : reg m8 9 = self := by rw [regs8]; simp +decide [upd, aluEval, ha1]
  have ra8 : reg m8 ra = base + 0x16 := by rw [regs8]; simp +decide [upd]
  have keep8 : ∀ r, r ≠ a0 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 → reg m8 r = reg m r := fun r h0 h1 h2 h3 h4 => by
    rw [regs8]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h0, h1, h2, h3, h4]
  obtain ⟨m9, c9, pc9, sp9, a09, a19, k9, mem9⟩ := readerU8_correct m8 (base + 0xFFFFFF8E) (base + 0x16) self
    (by show CodeIn m8.mem _ _; rw [mem8]; exact codeOut hSu hu)
    (by show CodeIn m8.mem _ _; rw [mem8, show base + 0xFFFFFF8E + 0xD6 = base + 0x64 by rw [BitVec.add_assoc]; rfl]; exact codeOut hSb hb)
    (even_at base hbase 0xFFFFFF8E (by decide)) pc8 a08 ra8 (even_clear _ (even_at base hbase 0x16 (by decide)))
    (by rw [sp8]; exact hGa) hself (by rw [mem8, l0, l4]; exact hbuf)
    (by rw [sp8]; exact s16 _ _ hSu) (by rw [sp8, show base + 0xFFFFFF8E + 0xD6 = base + 0x64 by rw [BitVec.add_assoc]; rfl]; exact s16 _ _ hSb) hEu (by rw [show base + 0xFFFFFF8E + 0xD6 = base + 0x64 by rw [BitVec.add_assoc]; rfl]; exact hEb)
    (by rw [sp8, hSG]; exact sR16 hRS) (by rw [mem8, l0, l4, sp8, hSG]; exact sR16 hBS)
    (by rw [mem8, l0, l4]; exact hBE)
  rw [sp8, mem8] at mem9
  rw [sp8] at sp9
  have res9 : ∀ x, Sep S 32 x 1 → m9.mem x = reservedMem m.mem self 1 x := fun x hx => by
    rw [mem9 x (s16 _ _ hx)]; unfold reservedMem; rw [l0, l4, l8]
    cases bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 1 with
    | none => exact M3out x hx
    | some pe => exact memStore32_congr (M3out x hx)
  have fr9 : ∀ c, 4 ≤ c → c + 4 ≤ 16 → memLoad32 m9.mem (G + BitVec.ofNat 32 c) = memLoad32 M3 (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, mem9 _ (inG (c + j) (by omega))]; unfold reservedMem; rw [l0, l4, l8]
      cases bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 1 with
      | none => rfl
      | some pe => exact memStore32_get_sep (by
          rw [hGS, add_ofNat_assoc]; exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 16 + (c + j)) (l := 1) (by omega))
  rw [mem8] at a09 a19
  have s09 : reg m9 8 = out := by rw [k9 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s08
  have s19 : reg m9 9 = self := by rw [k9 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s18
  have k9m : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
      reg m9 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => (k9 r h0 h1 h2 h3 h4 h5).trans (keep8 r h0 h6 h7 h8 h9)
  have rsv : ∀ x, Sep (self + 8) 4 x 1 → reservedMem m.mem self 1 x = m.mem x := fun x hx => by
    unfold reservedMem
    cases bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 1 with
    | none => rfl
    | some pe => exact memStore32_get_sep hx
  have hc9 : CodeIn m9.mem base readSignaturesCode := fun i hi => by
    rw [res9 _ (hSc.subR (c := i) (l := 1) (by omega)), rsv _ (hEc.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hb9 : CodeIn m9.mem (base + 0x64) readerBytesCode := fun i hi => by
    rw [res9 _ (hSb.subR (c := i) (l := 1) (by omega)), rsv _ (hEb.subR (c := i) (l := 1) (by omega))]; exact hb i hi
  have t9 : St m9.mem base m9 0x16 (reg m9) := ⟨by rw [pc9]; rfl, rfl, fun _ => rfl⟩
  have hz9 : reg m9 0 = 0 := t9.zero
  have fA : memLoad32 M3 (G + 0xC) = reg m ra := by
    rw [← hM3]
    exact (memLoad32_store32_sep (sep_offsets G (c := 4) (n := 4) (d := 12) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
      ((memLoad32_store32_sep (sep_offsets G (c := 8) (n := 4) (d := 12) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
        (memLoad32_store32_same _ _ _))
  have fB : memLoad32 M3 (G + 8) = reg m 8 := by
    rw [← hM3]
    exact (memLoad32_store32_sep (sep_offsets G (c := 4) (n := 4) (d := 8) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
      (memLoad32_store32_same _ _ _)
  have fC : memLoad32 M3 (G + 4) = reg m 9 := by rw [← hM3]; exact memLoad32_store32_same _ _ _
  have fA9 : memLoad32 m9.mem (G + 0xC) = reg m ra := (fr9 12 (by omega) (by omega)).trans fA
  have fB9 : memLoad32 m9.mem (G + 8) = reg m 8 := (fr9 8 (by omega) (by omega)).trans fB
  have fC9 : memLoad32 m9.mem (G + 4) = reg m 9 := (fr9 4 (by omega) (by omega)).trans fC
  have hO4 : Sep out 4 S 32 := by have := hOS.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have errLd : ∀ (v : BitVec 8) c, 4 ≤ c → c + 4 ≤ 16 →
      memLoad32 (memStore8 (memStore32 m9.mem out 0) (out + 0x4) v) (G + BitVec.ofNat 32 c) =
        memLoad32 m9.mem (G + BitVec.ofNat 32 c) := fun v c h1 h2 =>
    (memLoad32_congr fun j hj => memStore8_ne (by
      rw [add_ofNat_assoc, hGS, add_ofNat_assoc]
      exact fun e => hOS 4 (by omega) (16 + (c + j)) (by omega) e.symm)).trans
    (memLoad32_store32_sep (by rw [hGS, add_ofNat_assoc]; exact hO4.subR (c := 16 + c) (l := 4) (by omega)))
  have epi : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx base mx 0x5A fx →
      CodeIn Mx base readSignaturesCode → fx sp = G →
      memLoad32 Mx (G + 0xC) = reg m ra → memLoad32 Mx (G + 8) = reg m 8 → memLoad32 Mx (G + 4) = reg m 9 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 → fx r = reg m r) →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 6 → reg m' r = reg m r) ∧ m'.mem = Mx := by
    intro Mx mx fx s hcx hs hA hB hC hk
    obtain ⟨n2, d2, u2⟩ := s.lw hcx rsg_at_5a (off' := 0x5C) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0xC) (by decide))
    rw [hs, hA] at u2
    obtain ⟨n3, d3, u3⟩ := u2.lw hcx rsg_at_5c (off' := 0x5E) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 8) (by decide))
    rw [show upd fx ra (reg m ra) sp = G by simp +decide only [upd]; exact hs, hB] at u3
    obtain ⟨n4, d4, u4⟩ := u3.lw hcx rsg_at_5e (off' := 0x60) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 4) (by decide))
    rw [show upd (upd fx ra (reg m ra)) 8 (reg m 8) sp = G by simp +decide only [upd]; exact hs, hC] at u4
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hcx rsg_at_60 (off' := 0x62) (by decide)
    obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hcx rsg_at_62
    refine ⟨n6, .cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6)))), ?_, ?_,
      fun r h0 h1 h2 h3 h4 h5 _ => ?_, by rw [mem6]⟩
    · rw [pc6, add_lit_zero]; simp +decide only [upd, ite_true, ite_false]; rw [hra, hret]
    · rw [regs6]; simp +decide only [upd, ite_true, ite_false]; rw [hs, ← hspG]; rfl
    · rw [regs6]
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
      simp [upd, hr, hsp', hra', h8', h9']
      exact hk r h0 h1 h2 h3 h4 h5 hra' hsp' h8' h9'
  have us : ∀ (g : Fin 32 → Word) (r : Fin 32) (v : Word), r.val ≠ 0 → upd g r v r = v := fun g r v h => by
    simp only [upd, h, ↓reduceIte]
  have pre := fun {mx : Machine} (c : Steps m9 mx) =>
    Steps.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (c8.trans (c9.trans c))))))))
  have hcO : Sep out 4 base readSignaturesCode.length := by
    have := hOc.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  rcases hbr : bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 1 with _ | ⟨p, e⟩
  · have ha0' : reg m9 a0 = 1 := by rw [a09]; unfold u8Result; rw [l0, l4, l8, hbr]
    have ha1' : reg m9 a1 = 0 := by rw [a19]; unfold u8Result; rw [l0, l4, l8, hbr]
    obtain ⟨n10, e10, t10⟩ := t9.aluImm hc9 rsg_at_16 (off' := 0x18) (by decide)
    obtain ⟨n11, e11, t11⟩ := t10.notTaken hc9 0x1A rsg_at_18 (by decide)
      (by rw [ha0', us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq (aluEval .and 1 1) 0 = false))
    obtain ⟨n12, e12, t12⟩ := t11.sw hc9 rsg_at_1a (off' := 0x1E) (by decide)
      (by rw [updz hz9 (show (8 : Fin 32) ≠ a0 by decide), s09, show out + (0x0 : Word) = out from BitVec.add_zero out]; exact hout)
    rw [updz hz9 (show (8 : Fin 32) ≠ a0 by decide), s09, upd_x0, show out + (0x0 : Word) = out from BitVec.add_zero out] at t12
    have hc12 := hc9.store32 (v := 0) (a := out) hcO
    obtain ⟨n13, e13, t13⟩ := t12.sb hc12 rsg_at_1e (off' := 0x22) (by decide)
    rw [updz hz9 (show (8 : Fin 32) ≠ a0 by decide), s09, updz hz9 (show a1 ≠ a0 by decide), ha1'] at t13
    have hc13 := hc12.store8 (v := (0 : Word).extractLsb' 0 8) (a := out + 0x4) (hOc.sub (c := 4) (l := 1) (by omega))
    obtain ⟨n14, e14, t14⟩ := t13.jump hc13 rsg_at_22 (off' := 0x5A) (by decide)
      (by rw [t13.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x5A (by decide)))
    obtain ⟨m', c', pc', sp', k', mem'⟩ := epi _ _ _ t14 hc13 (by rw [updz hz9 (by decide)]; exact sp9)
      ((errLd _ 12 (by omega) (by omega)).trans fA9) ((errLd _ 8 (by omega) (by omega)).trans fB9)
      ((errLd _ 4 (by omega) (by omega)).trans fC9)
      (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by rw [updz hz9 h0]; exact k9m r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
    refine ⟨m', pre (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 c'))))), pc', sp', k', fun x hx => ?_⟩
    have mx : m9.mem x = m.mem x := by rw [res9 x hx]; unfold reservedMem; rw [hbr]
    rw [mem']; unfold readSigsMem; rw [hbr]
    exact memStore8_congr (memStore32_congr mx)
  · obtain ⟨hp, hpos⟩ : memLoad32 m.mem self + memLoad32 m.mem (self + 8) = p ∧
        (memLoad32 m.mem (self + 8)).toNat + 1 ≤ (memLoad32 m.mem (self + 4)).toNat := by
      have hb2 := hbr
      rw [bytesResult_eq] at hb2
      split at hb2
      · next hle =>
        injection hb2 with h; injection h with h1 h2; exact ⟨h1, hle⟩
      · cases hb2
    have hpo : BitVec.ofNat 32 (memLoad32 m.mem (self + 8)).toNat = memLoad32 m.mem (self + 8) :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (BitVec.isLt _))
    have hMp : M3 p = m.mem p := M3out p (by
      rw [← hp, ← hpo]; exact (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat) (l := 1) (by omega)).symm)
    have ha0' : reg m9 a0 = 0 := by rw [a09]; unfold u8Result; rw [l0, l4, l8, hbr]
    have ha1' : reg m9 a1 = (m.mem p).zeroExtend 32 := by
      rw [a19]; unfold u8Result; rw [l0, l4, l8, hbr]; show (M3 p).zeroExtend 32 = _; rw [hMp]
    have hres : ∀ x, Sep S 32 x 1 → m9.mem x = memStore32 m.mem (self + 8) e x := fun x hx =>
      (res9 x hx).trans (by unfold reservedMem; rw [hbr])
    obtain ⟨n10, e10, t10⟩ := t9.aluImm hc9 rsg_at_16 (off' := 0x18) (by decide)
    obtain ⟨n11, e11, t11⟩ := t10.taken hc9 0x24 rsg_at_18 (by decide)
      (by rw [ha0', us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq (aluEval .and 0 1) 0 = true))
    obtain ⟨n12, e12, t12⟩ := t11.aluImm hc9 rsg_at_24 (off' := 0x28) (by decide)
    rw [updz hz9 (show a1 ≠ a0 by decide), ha1'] at t12
    obtain ⟨n13, e13, t13⟩ := t12.aluImm hc9 rsg_at_28 (off' := 0x2C) (by decide)
    rw [us _ a0 _ (by decide)] at t13
    obtain ⟨n14, e14, t14⟩ := t13.aluImm hc9 rsg_at_2c (off' := 0x2E) (by decide)
    have q14a0 : reg n14 a0 = aluEval .and (aluEval .add ((m.mem p).zeroExtend 32) 0xFFFFFFFE) 0xFF := by
      rw [t14.regs]; simp +decide only [upd, ite_true, ite_false]
    have q14a1 : reg n14 a1 = (m.mem p).zeroExtend 32 := by
      rw [t14.regs]; simp +decide only [upd, ite_true, ite_false]; exact ha1'
    have q148 : reg n14 8 = out := by rw [t14.regs]; simp +decide only [upd, ite_true, ite_false]; exact s09
    have q149 : reg n14 9 = self := by rw [t14.regs]; simp +decide only [upd, ite_true, ite_false]; exact s19
    have q14sp : reg n14 sp = G := by rw [t14.regs]; simp +decide only [upd, ite_true, ite_false]; exact sp9
    have q14k : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
        reg n14 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; rw [t14.self.zero, hz]
      rw [t14.regs]; simp only [upd, hr, h0, h2, ↓reduceIte]; exact k9m r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    have q14a2 : reg n14 a2 = 3 := by rw [t14.regs]; simp +decide only [upd, ite_true, ite_false]
    have hz14 : reg n14 x0 = 0 := t14.self.zero
    have u14 := t14.self
    by_cases hr : 2 ≤ (m.mem p).toNat ∧ (m.mem p).toNat ≤ 4
    · obtain ⟨n15, e15, t15⟩ := u14.notTaken hc9 0x32 rsg_at_2e (by decide)
        (by
          rw [q14a0, q14a2]
          show (!((aluEval .and (aluEval .add ((m.mem p).zeroExtend 32) 0xFFFFFFFE) 0xFF).ult 3)) = false
          rw [sig_range, decide_eq_true hr]; rfl)
      obtain ⟨n16, e16, t16⟩ := t15.aluImm hc9 rsg_at_32 (off' := 0x36) (by decide)
      rw [q14a1, zext_and_ff] at t16
      obtain ⟨n17, e17, t17⟩ := t16.aluImm hc9 rsg_at_36 (off' := 0x3A) (by decide)
      rw [us _ a2 _ (by decide)] at t17
      obtain ⟨n18, e18, t18⟩ := t17.alu hc9 rsg_at_3a (off' := 0x3C) (by decide)
      rw [updz t16.zero (show a2 ≠ a0 by decide), us _ a2 _ (by decide), us _ a0 _ (by decide), sig_len] at t18
      obtain ⟨n19, e19, t19⟩ := t18.alu hc9 rsg_at_3c (off' := 0x3E) (by decide)
      obtain ⟨n20, e20, t20⟩ := t19.alu hc9 rsg_at_3e (off' := 0x40) (by decide)
      have q20a0 : reg n20 a0 = out := by
        rw [t20.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q148]; exact BitVec.zero_add out
      have q20a1 : reg n20 a1 = self := by
        rw [t20.regs]; simp +decide only [upd, ite_true, ite_false]; rw [q149]; exact BitVec.zero_add self
      have q20a2 : reg n20 a2 = (m.mem p).zeroExtend 32 * 65 := by
        rw [t20.regs]; simp +decide only [upd, ite_true, ite_false]
      have q20sp : reg n20 sp = G := by rw [t20.regs]; simp +decide only [upd, ite_true, ite_false]; exact q14sp
      have q20k : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n20 r = reg n14 r := fun r h0 h1 h2 => by
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; rw [t20.self.zero, hz14]
        rw [t20.regs]; simp only [upd, hr, h0, h1, h2, ↓reduceIte]
      have u20 := t20.self
      obtain ⟨n21, e21, t21⟩ := u20.lw hc9 rsg_at_40 (off' := 0x42) (by decide)
        (by rw [q20sp]; exact aligned_add hGa (k := 0xC) (by decide))
      rw [q20sp, fA9] at t21
      obtain ⟨n22, e22, t22⟩ := t21.lw hc9 rsg_at_42 (off' := 0x44) (by decide)
        (by rw [updz u20.zero (show sp ≠ ra by decide), q20sp]; exact aligned_add hGa (k := 8) (by decide))
      rw [updz u20.zero (show sp ≠ ra by decide), q20sp, fB9] at t22
      obtain ⟨n23, e23, t23⟩ := t22.lw hc9 rsg_at_44 (off' := 0x46) (by decide)
        (by simp +decide only [upd]; rw [q20sp]; exact aligned_add hGa (k := 4) (by decide))
      rw [show upd (upd (reg n20) ra (reg m ra)) 8 (reg m 8) sp = G by simp +decide only [upd]; exact q20sp, fC9] at t23
      obtain ⟨n24, e24, t24⟩ := t23.aluImm hc9 rsg_at_46 (off' := 0x48) (by decide)
      obtain ⟨n25, e25, t25⟩ := t24.auipc hc9 rsg_at_48 (off' := 0x4C) (by decide)
      obtain ⟨n26, e26, pc26, mem26, regs26⟩ := t25.jalr hc9 rsg_at_4c
      have p26 : n26.pc = base + 0x64 := by
        rw [pc26]; simp +decide only [upd, ite_true, ite_false]
        rw [show base + BitVec.ofNat 32 0x48 + 0x0 + 0x1C = base + 0x64 by
          rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
        exact even_clear _ (even_at base hbase 0x64 (by decide))
      have r26 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 6 → reg n26 r = reg m r :=
        fun r h0 h1 h2 h3 h4 h5 h6 => by
          rw [regs26]
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
          simp [upd, hr, hsp', hra', h8', h9', h6]
          rw [q20k r h0 h1 h2]; exact q14k r h0 h1 h2 h3 h4 h5 hra' hsp' h8' h9'
      obtain ⟨m', c', pc', mem', fr'⟩ := readerBytes_correct n26 (base + 0x64) retAddr out self
        ((m.mem p).zeroExtend 32 * 65) (by show CodeIn n26.mem _ _; rw [mem26]; exact hb9) p26
        (by rw [regs26]; simp +decide only [upd, ite_false]; exact q20a0)
        (by rw [regs26]; simp +decide only [upd, ite_false]; exact q20a1)
        (by rw [regs26]; simp +decide only [upd, ite_false]; exact q20a2)
        (by rw [r26 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hra)
        hret hout hself hOb hEb
      refine ⟨m', pre (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17 (.cons e18
        (.cons e19 (.cons e20 (.cons e21 (.cons e22 (.cons e23 (.cons e24 (.cons e25 (.cons e26 c'))))))))))))))))),
        pc', ?_, fun r h0 h1 h2 h3 h4 h5 h6 => ?_, fun x hx => ?_⟩
      · rw [fr' sp (by decide) (by decide) (by decide)]
        exact r26 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · rw [fr' r h3 h4 h5]; exact r26 r h0 h1 h2 h3 h4 h5 h6
      · rw [mem', mem26]; unfold readSigsMem; rw [hbr]; simp only [hr, and_self, ↓reduceIte]
        exact bytesMem_congr (hres x hx) fun j hj => hres _ ((hRS.sub (c := j) (l := 1) (by omega)).symm)
    · have hf : (aluEval .and (aluEval .add ((m.mem p).zeroExtend 32) 0xFFFFFFFE) 0xFF).ult 3 = false := by
        rw [sig_range]; exact decide_eq_false hr
      obtain ⟨n15, e15, t15⟩ := u14.taken hc9 0x50 rsg_at_2e (by decide)
        (by
          rw [q14a0, q14a2]
          show (!((aluEval .and (aluEval .add ((m.mem p).zeroExtend 32) 0xFFFFFFFE) 0xFF).ult 3)) = true
          rw [hf]; rfl)
      obtain ⟨n16, e16, t16⟩ := t15.aluImm hc9 rsg_at_50 (off' := 0x52) (by decide)
      rw [hz14] at t16
      obtain ⟨n17, e17, t17⟩ := t16.sw hc9 rsg_at_52 (off' := 0x56) (by decide)
        (by rw [updz u14.zero (show (8 : Fin 32) ≠ a0 by decide), q148, show out + (0x0 : Word) = out from BitVec.add_zero out]; exact hout)
      rw [updz u14.zero (show (8 : Fin 32) ≠ a0 by decide), q148, upd_x0, show out + (0x0 : Word) = out from BitVec.add_zero out] at t17
      have hc17 := hc9.store32 (v := 0) (a := out) hcO
      obtain ⟨n18, e18, t18⟩ := t17.sb hc17 rsg_at_56 (off' := 0x5A) (by decide)
      rw [updz u14.zero (show (8 : Fin 32) ≠ a0 by decide), q148, us _ a0 _ (by decide)] at t18
      have hc18 := hc17.store8 (v := (aluEval .add 0 5).extractLsb' 0 8) (a := out + 0x4) (hOc.sub (c := 4) (l := 1) (by omega))
      obtain ⟨m', c', pc', sp', k', mem'⟩ := epi _ _ _ t18 hc18 (by rw [updz u14.zero (by decide)]; exact q14sp)
        ((errLd _ 12 (by omega) (by omega)).trans fA9) ((errLd _ 8 (by omega) (by omega)).trans fB9)
        ((errLd _ 4 (by omega) (by omega)).trans fC9)
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by rw [updz u14.zero h0]; exact q14k r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
      refine ⟨m', pre (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17
        (.cons e18 c'))))))))), pc', sp', k', fun x hx => ?_⟩
      rw [mem']; unfold readSigsMem; rw [hbr]; simp only [hr, ↓reduceIte]
      exact memStore8_congr (memStore32_congr (hres x hx))

end C3.RV32




