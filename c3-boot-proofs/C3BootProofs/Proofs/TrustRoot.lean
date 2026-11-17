import C3BootProofs.Proofs.ImageHelpers
import C3BootProofs.Proofs.SmallFns
import C3BootProofs.Proofs.ReaderArray

/-!
# Small functions of the trust-root reader

`trustroot::read_count(r, max)` reads a count byte with `Reader::u8` and
returns `Result<usize, Error>` through `a0`: tag 0 and the count at offset
4 when `1 ≤ count ≤ max`, tag 1 and `Truncated` (0) when no byte is left,
and tag 1 and `OutOfRange` (5) otherwise.
-/

namespace C3.RV32

open C3.Image

/-- Memory after `read_count` returns, outside the stack it uses. -/
def readCountMem (M : Word → BitVec 8) (out self max : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 1 with
  | none => memStore8 (memStore8 M (out + 1) 0) out 1
  | some (p, e) =>
    if ((M p).zeroExtend 32 + 0xFFFFFFFF).ult max then
      memStore8 (memStore32 (memStore32 M (self + 8) e) (out + 4) ((M p).zeroExtend 32)) out 0
    else memStore8 (memStore8 (memStore32 M (self + 8) e) (out + 1) 5) out 1

theorem rc_at_0 : fetchRel readCountCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem rc_at_2 : fetchRel readCountCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem rc_at_4 : fetchRel readCountCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem rc_at_6 : fetchRel readCountCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem rc_at_8 : fetchRel readCountCode 0x8 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem rc_at_a : fetchRel readCountCode 0xA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem rc_at_c : fetchRel readCountCode 0xC = some (.alu .add a0 x0 a1, 2) := by decide
theorem rc_at_e : fetchRel readCountCode 0xE = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem rc_at_12 : fetchRel readCountCode 0x12 = some (.jalr ra ra 0x45C, 4) := by decide
theorem rc_at_16 : fetchRel readCountCode 0x16 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem rc_at_18 : fetchRel readCountCode 0x18 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem rc_at_1a : fetchRel readCountCode 0x1A = some (.store .sb (8 : Fin 32) a1 0x1, 4) := by decide
theorem rc_at_1e : fetchRel readCountCode 0x1E = some (.jal x0 0x1A, 2) := by decide
theorem rc_at_20 : fetchRel readCountCode 0x20 = some (.aluImm .and a1 a1 0xFF, 4) := by decide
theorem rc_at_24 : fetchRel readCountCode 0x24 = some (.aluImm .add a0 a1 0xFFFFFFFF, 4) := by decide
theorem rc_at_28 : fetchRel readCountCode 0x28 = some (.branch .bgeu a0 (9 : Fin 32) 0xA, 4) := by decide
theorem rc_at_2c : fetchRel readCountCode 0x2C = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem rc_at_2e : fetchRel readCountCode 0x2E = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem rc_at_30 : fetchRel readCountCode 0x30 = some (.jal x0 0xA, 2) := by decide
theorem rc_at_32 : fetchRel readCountCode 0x32 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem rc_at_34 : fetchRel readCountCode 0x34 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem rc_at_38 : fetchRel readCountCode 0x38 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem rc_at_3a : fetchRel readCountCode 0x3A = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem rc_at_3e : fetchRel readCountCode 0x3E = some (.load .lw ra sp 0xC, 2) := by decide
theorem rc_at_40 : fetchRel readCountCode 0x40 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem rc_at_42 : fetchRel readCountCode 0x42 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem rc_at_44 : fetchRel readCountCode 0x44 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem rc_at_46 : fetchRel readCountCode 0x46 = some (.jalr x0 ra 0x0, 2) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`trustroot::read_count`, as compiled**: with `Reader::u8` and
`Reader::bytes` where the image puts them, a reader `self` over a slice that
is not null and doesn't wrap, a result address `out`, and 32 bytes of stack
below `sp`, all apart as the hypotheses list, it returns to `ra` with `sp`,
`s0`, `s1`, and `ra` restored and memory outside its stack as
`readCountMem` says. -/
theorem readCount_correct (m : Machine) {base retAddr out self max : Word}
    (hc : CodeIn m.mem base readCountCode) (hu : CodeIn m.mem (base + 0xFFFFC46A) readerU8Code)
    (hb : CodeIn m.mem (base + 0xFFFFC46A + 0xD6) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = self)
    (ha2 : reg m a2 = max) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hself : self.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSc : Sep (reg m sp + 0xFFFFFFE0) 32 base readCountCode.length)
    (hSu : Sep (reg m sp + 0xFFFFFFE0) 32 (base + 0xFFFFC46A) readerU8Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFE0) 32 (base + 0xFFFFC46A + 0xD6) readerBytesCode.length)
    (hOc : Sep out 8 base readCountCode.length)
    (hEu : Sep (self + 8) 4 (base + 0xFFFFC46A) readerU8Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xFFFFC46A + 0xD6) readerBytesCode.length)
    (hEc : Sep (self + 8) 4 base readCountCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFE0) 32) (hOS : Sep out 8 (reg m sp + 0xFFFFFFE0) 32)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFE0) 32)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFE0) 32 x 1 → m'.mem x = readCountMem m.mem out self max x := by
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
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc rc_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc rc_at_2 (off' := 4) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (fr 0xC 4 (by omega) _ _ hSc)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 rc_at_4 (off' := 6) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (fr 8 4 (by omega) _ _ hSc)
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 rc_at_6 (off' := 8) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 4) (by decide))
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
  obtain ⟨m5, e5, t5⟩ := t4.alu hc4 rc_at_8 (off' := 0xA) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.alu hc4 rc_at_a (off' := 0xC) (by decide)
  obtain ⟨m7, e7, t7⟩ := t6.alu hc4 rc_at_c (off' := 0xE) (by decide)
  obtain ⟨m8, c8, pc8, mem8, regs8⟩ := t7.callRa (cb := base + 0xFFFFC46A) hc4 rc_at_e rc_at_12
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xFFFFC46A (by decide))
  have sp8 : reg m8 sp = G := by rw [regs8]; simp +decide [upd]
  have a08 : reg m8 a0 = self := by rw [regs8]; simp +decide [upd, aluEval, ha1]
  have s08 : reg m8 8 = out := by rw [regs8]; simp +decide [upd, aluEval, ha0]
  have s18 : reg m8 9 = max := by rw [regs8]; simp +decide [upd, aluEval, ha2]
  have ra8 : reg m8 ra = base + 0x16 := by rw [regs8]; simp +decide [upd]
  have keep8 : ∀ r, r ≠ a0 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 → reg m8 r = reg m r := fun r h0 h1 h2 h3 h4 => by
    rw [regs8]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h0, h1, h2, h3, h4]
  obtain ⟨m9, c9, pc9, sp9, a09, a19, k9, mem9⟩ := readerU8_correct m8 (base + 0xFFFFC46A) (base + 0x16) self
    (by show CodeIn m8.mem _ _; rw [mem8]; exact codeOut hSu hu)
    (by show CodeIn m8.mem _ _; rw [mem8]; exact codeOut hSb hb)
    (even_at base hbase 0xFFFFC46A (by decide)) pc8 a08 ra8 (even_clear _ (even_at base hbase 0x16 (by decide)))
    (by rw [sp8]; exact hGa) hself (by rw [mem8, l0, l4]; exact hbuf)
    (by rw [sp8]; exact s16 _ _ hSu) (by rw [sp8]; exact s16 _ _ hSb) hEu hEb
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
  have s19 : reg m9 9 = max := by rw [k9 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s18
  have k9m : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
      reg m9 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => (k9 r h0 h1 h2 h3 h4 h5).trans (keep8 r h0 h6 h7 h8 h9)
  have rsv : ∀ x, Sep (self + 8) 4 x 1 → reservedMem m.mem self 1 x = m.mem x := fun x hx => by
    unfold reservedMem
    cases bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 1 with
    | none => rfl
    | some pe => exact memStore32_get_sep hx
  have hc9 : CodeIn m9.mem base readCountCode := fun i hi => by
    rw [res9 _ (hSc.subR (c := i) (l := 1) (by omega)), rsv _ (hEc.subR (c := i) (l := 1) (by omega))]; exact hc i hi
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
  have st8 : ∀ (Mx : Word → BitVec 8) (a : Word) (v : BitVec 8) (k : Nat), k < 8 → a = out + BitVec.ofNat 32 k →
      ∀ c, 4 ≤ c → c + 4 ≤ 16 → memLoad32 (memStore8 Mx a v) (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) :=
    fun Mx a v k hk ha c h1 h2 => memLoad32_congr fun j hj => memStore8_ne (by
      rw [add_ofNat_assoc, hGS, add_ofNat_assoc, ha]; exact fun e => hOS k hk (16 + (c + j)) (by omega) e.symm)
  have st32 : ∀ (Mx : Word → BitVec 8) (v : Word) c, 4 ≤ c → c + 4 ≤ 16 →
      memLoad32 (memStore32 Mx (out + 0x4) v) (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) :=
    fun Mx v c h1 h2 => memLoad32_store32_sep (by
      rw [hGS, add_ofNat_assoc]; exact (hOS.sub (c := 4) (l := 4) (by omega)).subR (c := 16 + c) (l := 4) (by omega))
  have frm : ∀ (Mx : Word → BitVec 8),
      (∀ c, 4 ≤ c → c + 4 ≤ 16 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 m9.mem (G + BitVec.ofNat 32 c)) →
      ∀ v, memLoad32 (memStore8 Mx out v) (G + 0xC) = reg m ra ∧ memLoad32 (memStore8 Mx out v) (G + 8) = reg m 8 ∧
        memLoad32 (memStore8 Mx out v) (G + 4) = reg m 9 := fun Mx h v =>
    ⟨(st8 Mx out v 0 (by omega) (add_ofNat_zero out).symm 12 (by omega) (by omega)).trans
        ((h 12 (by omega) (by omega)).trans ((fr9 12 (by omega) (by omega)).trans fA)),
      (st8 Mx out v 0 (by omega) (add_ofNat_zero out).symm 8 (by omega) (by omega)).trans
        ((h 8 (by omega) (by omega)).trans ((fr9 8 (by omega) (by omega)).trans fB)),
      (st8 Mx out v 0 (by omega) (add_ofNat_zero out).symm 4 (by omega) (by omega)).trans
        ((h 4 (by omega) (by omega)).trans ((fr9 4 (by omega) (by omega)).trans fC))⟩
  have tail : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx base mx 0x3A fx →
      CodeIn Mx base readCountCode → fx sp = G → fx 8 = out →
      memLoad32 (memStore8 Mx out ((fx a0).extractLsb' 0 8)) (G + 0xC) = reg m ra ∧
        memLoad32 (memStore8 Mx out ((fx a0).extractLsb' 0 8)) (G + 8) = reg m 8 ∧
        memLoad32 (memStore8 Mx out ((fx a0).extractLsb' 0 8)) (G + 4) = reg m 9 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 → fx r = reg m r) →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
        m'.mem = memStore8 Mx out ((fx a0).extractLsb' 0 8) := by
    intro Mx mx fx s hcx hs h8 ⟨hA, hB, hC⟩ hk
    have hzx := s.zero
    obtain ⟨n1, d1, u1⟩ := s.sb hcx rc_at_3a (off' := 0x3E) (by decide)
    rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out] at u1
    have hc1 := hcx.store8 (v := (fx a0).extractLsb' 0 8) (a := out)
      (by have := hOc.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this)
    obtain ⟨n2, d2, u2⟩ := u1.lw hc1 rc_at_3e (off' := 0x40) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0xC) (by decide))
    rw [hs, hA] at u2
    obtain ⟨n3, d3, u3⟩ := u2.lw hc1 rc_at_40 (off' := 0x42) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 8) (by decide))
    rw [show upd fx ra (reg m ra) sp = G by simp +decide only [upd]; exact hs, hB] at u3
    obtain ⟨n4, d4, u4⟩ := u3.lw hc1 rc_at_42 (off' := 0x44) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 4) (by decide))
    rw [show upd (upd fx ra (reg m ra)) 8 (reg m 8) sp = G by simp +decide only [upd]; exact hs, hC] at u4
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hc1 rc_at_44 (off' := 0x46) (by decide)
    obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc1 rc_at_46
    refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), ?_, ?_,
      fun r h0 h1 h2 h3 h4 h5 => ?_, by rw [mem6]⟩
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
  rcases hbr : bytesResult (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)) (memLoad32 m.mem (self + 8)) 1 with _ | ⟨p, e⟩
  · have ha0' : reg m9 a0 = 1 := by rw [a09]; unfold u8Result; rw [l0, l4, l8, hbr]
    have ha1' : reg m9 a1 = 0 := by rw [a19]; unfold u8Result; rw [l0, l4, l8, hbr]
    obtain ⟨n10, e10, t10⟩ := t9.aluImm hc9 rc_at_16 (off' := 0x18) (by decide)
    obtain ⟨n11, e11, t11⟩ := t10.notTaken hc9 0x1A rc_at_18 (by decide) (by rw [ha0', us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq (aluEval .and 1 1) 0 = false))
    obtain ⟨n12, e12, t12⟩ := t11.sb hc9 rc_at_1a (off' := 0x1E) (by decide)
    rw [updz hz9 (show (8 : Fin 32) ≠ a0 by decide), s09, updz hz9 (show a1 ≠ a0 by decide), ha1'] at t12
    have hc12 := hc9.store8 (v := (0 : Word).extractLsb' 0 8) (a := out + 0x1) (hOc.sub (c := 1) (l := 1) (by omega))
    obtain ⟨n13, e13, t13⟩ := t12.jump hc12 rc_at_1e (off' := 0x38) (by decide)
      (by rw [t12.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x38 (by decide)))
    obtain ⟨n14, e14, t14⟩ := t13.aluImm hc12 rc_at_38 (off' := 0x3A) (by decide)
    obtain ⟨m', c', pc', sp', k', mem'⟩ := tail _ _ _ t14 hc12
      (by simp +decide only [upd]; exact sp9) (by simp +decide only [upd]; exact s09)
      (frm _ (fun c h1 h2 => st8 _ _ _ 1 (by omega) rfl c h1 h2) _)
      (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
        rw [updz t13.zero h0, updz hz9 h0]; exact k9m r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
    refine ⟨m', pre (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 c'))))), pc', sp', k', fun x hx => ?_⟩
    rw [mem']; unfold readCountMem; rw [hbr]
    exact memStore8_congr (memStore8_congr ((res9 x hx).trans (by unfold reservedMem; rw [hbr])))
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
    obtain ⟨n10, e10, t10⟩ := t9.aluImm hc9 rc_at_16 (off' := 0x18) (by decide)
    obtain ⟨n11, e11, t11⟩ := t10.taken hc9 0x20 rc_at_18 (by decide)
      (by rw [ha0', us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq (aluEval .and 0 1) 0 = true))
    obtain ⟨n12, e12, t12⟩ := t11.aluImm hc9 rc_at_20 (off' := 0x24) (by decide)
    rw [updz hz9 (show a1 ≠ a0 by decide), ha1', zext_and_ff] at t12
    obtain ⟨n13, e13, t13⟩ := t12.aluImm hc9 rc_at_24 (off' := 0x28) (by decide)
    rw [us _ a1 _ (by decide)] at t13
    have f9 : ∀ (g : Fin 32 → Word), g = upd (upd (upd (reg m9) a0 (aluEval .and (reg m9 a0) 1)) a1
        ((m.mem p).zeroExtend 32)) a0 (aluEval .add ((m.mem p).zeroExtend 32) 0xFFFFFFFF) →
        ∀ r, r ≠ a0 → r ≠ a1 → g r = reg m9 r := fun g hg r h0 h1 => by
      subst hg; rw [updz t12.zero h0, updz t10.zero h1, updz hz9 h0]
    have g9 := f9 _ rfl 9 (by decide) (by decide)
    have g8 := f9 _ rfl 8 (by decide) (by decide)
    by_cases hlt : ((m.mem p).zeroExtend 32 + 0xFFFFFFFF).ult max = true
    · obtain ⟨n14, e14, t14⟩ := t13.notTaken hc9 0x2C rc_at_28 (by decide)
        (by rw [us _ a0 _ (by decide), g9, s19]; show (!((m.mem p).zeroExtend 32 + 0xFFFFFFFF).ult max) = false; rw [hlt]; rfl)
      obtain ⟨n15, e15, t15⟩ := t14.aluImm hc9 rc_at_2c (off' := 0x2E) (by decide)
      obtain ⟨n16, e16, t16⟩ := t15.sw hc9 rc_at_2e (off' := 0x30) (by decide)
        (by rw [updz t13.zero (show (8 : Fin 32) ≠ a0 by decide), g8, s09]; exact aligned_add hout (k := 4) (by decide))
      rw [updz t13.zero (show (8 : Fin 32) ≠ a0 by decide), g8, s09, updz t13.zero (show a1 ≠ a0 by decide),
        updz t12.zero (show a1 ≠ a0 by decide), us _ a1 _ (by decide)] at t16
      have hc16 := hc9.store32 (v := (m.mem p).zeroExtend 32) (a := out + 0x4) (hOc.sub (c := 4) (l := 4) (by omega))
      obtain ⟨n17, e17, t17⟩ := t16.jump hc16 rc_at_30 (off' := 0x3A) (by decide)
        (by rw [t16.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x3A (by decide)))
      obtain ⟨m', c', pc', sp', k', mem'⟩ := tail _ _ _ t17 hc16
        (by rw [updz t13.zero (by decide), f9 _ rfl sp (by decide) (by decide)]; exact sp9)
        (by rw [updz t13.zero (by decide), g8]; exact s09)
        (frm _ (fun c h1 h2 => st32 _ _ c h1 h2) _)
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
          rw [updz t13.zero h0, f9 _ rfl r h0 h1]; exact k9m r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
      refine ⟨m', pre (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17 c')))))))),
        pc', sp', k', fun x hx => ?_⟩
      rw [mem']; unfold readCountMem; rw [hbr]; simp only [hlt, ↓reduceIte]
      exact memStore8_congr (memStore32_congr (hres x hx))
    · have hf : ((m.mem p).zeroExtend 32 + 0xFFFFFFFF).ult max = false := by
        cases h : ((m.mem p).zeroExtend 32 + 0xFFFFFFFF).ult max
        · rfl
        · exact absurd h hlt
      obtain ⟨n14, e14, t14⟩ := t13.taken hc9 0x32 rc_at_28 (by decide)
        (by rw [us _ a0 _ (by decide), g9, s19]; show (!((m.mem p).zeroExtend 32 + 0xFFFFFFFF).ult max) = true; rw [hf]; rfl)
      obtain ⟨n15, e15, t15⟩ := t14.aluImm hc9 rc_at_32 (off' := 0x34) (by decide)
      obtain ⟨n16, e16, t16⟩ := t15.sb hc9 rc_at_34 (off' := 0x38) (by decide)
      rw [updz t13.zero (show (8 : Fin 32) ≠ a0 by decide), g8, s09, us _ a0 _ (by decide)] at t16
      rw [show ∀ (g : Fin 32 → Word) (v : Word), aluEval .add (upd g a0 v x0) 5 = 5 from fun _ _ => rfl] at t16
      have hc16 := hc9.store8 (v := (5 : Word).extractLsb' 0 8) (a := out + 0x1) (hOc.sub (c := 1) (l := 1) (by omega))
      obtain ⟨n17, e17, t17⟩ := t16.aluImm hc16 rc_at_38 (off' := 0x3A) (by decide)
      obtain ⟨m', c', pc', sp', k', mem'⟩ := tail _ _ _ t17 hc16
        (by rw [updz t16.zero (by decide), updz t13.zero (by decide), f9 _ rfl sp (by decide) (by decide)]; exact sp9)
        (by rw [updz t16.zero (by decide), updz t13.zero (by decide), g8]; exact s09)
        (frm _ (fun c h1 h2 => st8 _ _ _ 1 (by omega) rfl c h1 h2) _)
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
          rw [updz t16.zero h0, updz t13.zero h0, f9 _ rfl r h0 h1]; exact k9m r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
      refine ⟨m', pre (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17 c')))))))),
        pc', sp', k', fun x hx => ?_⟩
      rw [mem']; unfold readCountMem; rw [hbr]; simp only [hf, Bool.false_eq_true, ↓reduceIte]
      exact memStore8_congr (memStore8_congr (hres x hx))

end C3.RV32









