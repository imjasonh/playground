import C3BootProofs.Proofs.ReaderU32Cur
import C3BootProofs.Proofs.U16
import C3BootProofs.Proofs.SmallFns

/-!
# `c3_verify::reader::Reader::u64`, as compiled

`Reader::u64` takes 8 bytes with `Reader::bytes` and returns them as a
little-endian `Result<u64, Error>`: a tag byte (0 for `Ok`, 1 for `Err`), the
error byte at offset 1, and the value at offset 8, low word first. Its
32-byte frame holds `Reader::bytes`'s result at offset 12.
-/

namespace C3.RV32

open C3.Image

/-- Memory after `Reader::u64` returns, outside the stack it uses. -/
def u64Mem (M : Word → BitVec 8) (out self : Word) : Word → BitVec 8 :=
  match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 8 with
  | none => memStore8 (memStore8 M (out + 1) 0) out 1
  | some (p, e) => memStore8 (memStore32 (memStore32 (memStore32 M (self + 8) e) (out + 8) (memLoad32 M p))
      (out + 0xC) (memLoad32 M (p + 4))) out 0

set_option maxRecDepth 10000

theorem u64_at_0 : fetchRel readerU64Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem u64_at_2 : fetchRel readerU64Code 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem u64_at_4 : fetchRel readerU64Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem u64_at_6 : fetchRel readerU64Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem u64_at_8 : fetchRel readerU64Code 0x8 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem u64_at_a : fetchRel readerU64Code 0xA = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem u64_at_c : fetchRel readerU64Code 0xC = some (.aluImm .add a2 x0 0x8, 2) := by decide
theorem u64_at_e : fetchRel readerU64Code 0xE = some (.aluImm .add (9 : Fin 32) x0 0x8, 2) := by decide
theorem u64_at_10 : fetchRel readerU64Code 0x10 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem u64_at_14 : fetchRel readerU64Code 0x14 = some (.jalr ra ra 0x2FA, 4) := by decide
theorem u64_at_18 : fetchRel readerU64Code 0x18 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem u64_at_1a : fetchRel readerU64Code 0x1A = some (.branch .beq a1 x0 0x4C, 2) := by decide
theorem u64_at_1c : fetchRel readerU64Code 0x1C = some (.load .lw a0 sp 0x10, 2) := by decide
theorem u64_at_1e : fetchRel readerU64Code 0x1E = some (.branch .bne a0 (9 : Fin 32) 0x4E, 4) := by decide
theorem u64_at_22 : fetchRel readerU64Code 0x22 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem u64_at_24 : fetchRel readerU64Code 0x24 = some (.load .lbu a2 a1 0x1, 4) := by decide
theorem u64_at_28 : fetchRel readerU64Code 0x28 = some (.load .lbu a6 a1 0x0, 4) := by decide
theorem u64_at_2c : fetchRel readerU64Code 0x2C = some (.load .lbu (17 : Fin 32) a1 0x2, 4) := by decide
theorem u64_at_30 : fetchRel readerU64Code 0x30 = some (.load .lbu a5 a1 0x3, 4) := by decide
theorem u64_at_34 : fetchRel readerU64Code 0x34 = some (.aluImm .sll a2 a2 0x8, 2) := by decide
theorem u64_at_36 : fetchRel readerU64Code 0x36 = some (.load .lbu (9 : Fin 32) a1 0x5, 4) := by decide
theorem u64_at_3a : fetchRel readerU64Code 0x3A = some (.load .lbu a3 a1 0x6, 4) := by decide
theorem u64_at_3e : fetchRel readerU64Code 0x3E = some (.load .lbu a4 a1 0x7, 4) := by decide
theorem u64_at_42 : fetchRel readerU64Code 0x42 = some (.load .lbu a1 a1 0x4, 4) := by decide
theorem u64_at_46 : fetchRel readerU64Code 0x46 = some (.alu .or a2 a2 a6, 4) := by decide
theorem u64_at_4a : fetchRel readerU64Code 0x4A = some (.aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x10, 2) := by decide
theorem u64_at_4c : fetchRel readerU64Code 0x4C = some (.aluImm .sll a5 a5 0x18, 2) := by decide
theorem u64_at_4e : fetchRel readerU64Code 0x4E = some (.alu .or a5 a5 (17 : Fin 32), 4) := by decide
theorem u64_at_52 : fetchRel readerU64Code 0x52 = some (.aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x8, 2) := by decide
theorem u64_at_54 : fetchRel readerU64Code 0x54 = some (.aluImm .sll a3 a3 0x10, 2) := by decide
theorem u64_at_56 : fetchRel readerU64Code 0x56 = some (.aluImm .sll a4 a4 0x18, 2) := by decide
theorem u64_at_58 : fetchRel readerU64Code 0x58 = some (.alu .or a1 a1 (9 : Fin 32), 2) := by decide
theorem u64_at_5a : fetchRel readerU64Code 0x5A = some (.alu .or a3 a3 a4, 2) := by decide
theorem u64_at_5c : fetchRel readerU64Code 0x5C = some (.alu .or a2 a2 a5, 2) := by decide
theorem u64_at_5e : fetchRel readerU64Code 0x5E = some (.alu .or a1 a1 a3, 2) := by decide
theorem u64_at_60 : fetchRel readerU64Code 0x60 = some (.store .sw (8 : Fin 32) a2 0x8, 2) := by decide
theorem u64_at_62 : fetchRel readerU64Code 0x62 = some (.store .sw (8 : Fin 32) a1 0xC, 2) := by decide
theorem u64_at_64 : fetchRel readerU64Code 0x64 = some (.jal x0 0x10, 2) := by decide
theorem u64_at_66 : fetchRel readerU64Code 0x66 = some (.load .lbu a0 sp 0x10, 4) := by decide
theorem u64_at_6a : fetchRel readerU64Code 0x6A = some (.jal x0 0x4, 2) := by decide
theorem u64_at_6c : fetchRel readerU64Code 0x6C = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem u64_at_6e : fetchRel readerU64Code 0x6E = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem u64_at_72 : fetchRel readerU64Code 0x72 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem u64_at_74 : fetchRel readerU64Code 0x74 = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem u64_at_78 : fetchRel readerU64Code 0x78 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem u64_at_7a : fetchRel readerU64Code 0x7A = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem u64_at_7c : fetchRel readerU64Code 0x7C = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem u64_at_7e : fetchRel readerU64Code 0x7E = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem u64_at_80 : fetchRel readerU64Code 0x80 = some (.jalr x0 ra 0x0, 2) := by decide

theorem or_assemble' (b0 b1 b2 b3 : BitVec 8) :
    ((b1.zeroExtend 32 <<< 8 ||| b0.zeroExtend 32) ||| (b3.zeroExtend 32 <<< 24 ||| b2.zeroExtend 32 <<< 16))
      = b3 ++ b2 ++ b1 ++ b0 := by
  rw [BitVec.or_comm (b1.zeroExtend 32 <<< 8), BitVec.or_comm (b3.zeroExtend 32 <<< 24)]
  exact Cur.or_assemble _ _ _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`Reader::u64`, as compiled**: with `Reader::bytes` where the image puts
it, a reader `self` over a slice that is not null and doesn't wrap, a result
address `out`, and 32 bytes of stack below `sp`, all apart as the hypotheses
list, it returns to `ra` with `sp`, `s0`, `s1`, and `ra` restored, and memory
outside its stack as `u64Mem` says. -/
theorem readerU64_correct (m : Machine) {base retAddr out self : Word}
    (hc : CodeIn m.mem base readerU64Code) (hb : CodeIn m.mem (base + 0xFFFFC30A) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = self)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hself : self.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSc : Sep (reg m sp + 0xFFFFFFE0) 32 base readerU64Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFE0) 32 (base + 0xFFFFC30A) readerBytesCode.length)
    (hOc : Sep out 16 base readerU64Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xFFFFC30A) readerBytesCode.length)
    (hEc : Sep (self + 8) 4 base readerU64Code.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFE0) 32) (hOS : Sep out 16 (reg m sp + 0xFFFFFFE0) 32)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFE0) 32)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFE0) 32 x 1 → m'.mem x = u64Mem m.mem out self x := by
  obtain ⟨S, hSd⟩ : ∃ S, reg m sp + 0xFFFFFFE0 = S := ⟨_, rfl⟩
  rw [hSd] at hSc hSb hRS hOS hBS ⊢
  obtain ⟨ptr, hptr⟩ : ∃ ptr, memLoad32 m.mem self = ptr := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, memLoad32 m.mem (self + 4) = len := ⟨_, rfl⟩
  rw [hptr, hlen] at hbuf hBS hBE
  have hspS : S + 0x20 = reg m sp := by rw [← hSd, BitVec.add_assoc]; exact BitVec.add_zero _
  have hSa : S.toNat % 4 = 0 := hSd ▸ aligned_add hsp (k := 0xFFFFFFE0) (by decide)
  have fr : ∀ c l, c + l ≤ 32 → ∀ (x : Word) (n : Nat), Sep S 32 x n → Sep (S + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => hx.sub (c := c) (l := l) h
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc u64_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFE0 = S from hSd] at t1
  have u1sp : upd (reg m) sp S sp = S := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp S r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc u64_at_2 (off' := 4) (by decide) (by rw [u1sp]; exact aligned_add hSa (k := 0x1C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (fr 0x1C 4 (by omega) _ _ hSc)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 u64_at_4 (off' := 6) (by decide) (by rw [u1sp]; exact aligned_add hSa (k := 0x18) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (fr 0x18 4 (by omega) _ _ hSc)
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 u64_at_6 (off' := 8) (by decide) (by rw [u1sp]; exact aligned_add hSa (k := 0x14) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 (memStore32 m.mem (S + 0x1C) (reg m ra)) (S + 0x18) (reg m 8))
      (S + 0x14) (reg m 9) = M3 := ⟨_, rfl⟩
  rw [hM3] at t4
  have M3out : ∀ x, Sep S 32 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3]
    exact (memStore32_get_sep (fr 0x14 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x18 4 (by omega) x 1 hx)).trans
      (memStore32_get_sep (fr 0x1C 4 (by omega) x 1 hx)))
  have codeOut : ∀ {b : Word} {code : List Nat}, Sep S 32 b code.length → CodeIn m.mem b code → CodeIn M3 b code :=
    fun h hc' i hi => by rw [M3out _ (h.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have hc4 := codeOut hSc hc
  have ldS : ∀ c, c + 4 ≤ 12 → memLoad32 M3 (self + BitVec.ofNat 32 c) = memLoad32 m.mem (self + BitVec.ofNat 32 c) :=
    fun c hc' => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact M3out _ ((hRS.sub (c := c + j) (l := 1) (by omega)).symm)
  have l0 : memLoad32 M3 self = ptr := by have := ldS 0 (by omega); rwa [add_ofNat_zero, hptr] at this
  have l4 : memLoad32 M3 (self + 4) = len := (ldS 4 (by omega)).trans hlen
  have l8 : memLoad32 M3 (self + 8) = memLoad32 m.mem (self + 8) := ldS 8 (by omega)
  have fA : memLoad32 M3 (S + 0x1C) = reg m ra := by
    rw [← hM3]
    exact (memLoad32_store32_sep (sep_offsets S (c := 0x14) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
      ((memLoad32_store32_sep (sep_offsets S (c := 0x18) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
        (memLoad32_store32_same _ _ _))
  have fB : memLoad32 M3 (S + 0x18) = reg m 8 := by
    rw [← hM3]
    exact (memLoad32_store32_sep (sep_offsets S (c := 0x14) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans
      (memLoad32_store32_same _ _ _)
  have fC : memLoad32 M3 (S + 0x14) = reg m 9 := by rw [← hM3]; exact memLoad32_store32_same _ _ _
  obtain ⟨m5, e5, t5⟩ := t4.alu hc4 u64_at_8 (off' := 0xA) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.aluImm hc4 u64_at_a (off' := 0xC) (by decide)
  obtain ⟨m7, e7, t7⟩ := t6.aluImm hc4 u64_at_c (off' := 0xE) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.aluImm hc4 u64_at_e (off' := 0x10) (by decide)
  obtain ⟨m9, c9, pc9, mem9, regs9⟩ := t8.callRa (cb := base + 0xFFFFC30A) hc4 u64_at_10 u64_at_14
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xFFFFC30A (by decide))
  have sp9 : reg m9 sp = S := by rw [regs9]; simp +decide [upd]
  have a09 : reg m9 a0 = S + 0xC := by rw [regs9]; simp +decide [upd, aluEval]
  have a19 : reg m9 a1 = self := by rw [regs9]; simp +decide [upd, ha1]
  have a29 : reg m9 a2 = 8 := by rw [regs9]; simp +decide [upd, aluEval]
  have s09 : reg m9 8 = out := by rw [regs9]; simp +decide [upd, aluEval, ha0]
  have s19 : reg m9 9 = 8 := by rw [regs9]; simp +decide [upd, aluEval]
  have ra9 : reg m9 ra = base + BitVec.ofNat 32 0x18 := by rw [regs9]; simp +decide [upd]
  have keep9 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 → reg m9 r = reg m r :=
    fun r h0 h2 h1 h3 h4 h5 => by
      rw [regs9]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1, h2, h3, h4, h5]
  obtain ⟨m10, c10, pc10, mem10, fr10⟩ := readerBytes_correct m9 (base + 0xFFFFC30A) (base + BitVec.ofNat 32 0x18)
    (S + 0xC) self 8 (by show CodeIn m9.mem _ _; rw [mem9]; exact codeOut hSb hb) pc9 a09 a19 a29 ra9
    (even_clear _ (even_at base hbase 0x18 (by decide))) (aligned_add hSa (k := 0xC) (by decide)) hself
    (hSb.sub (c := 0xC) (l := 8) (by omega)) hEb
  rw [mem9] at mem10
  have hR : bytesResult (memLoad32 M3 self) (memLoad32 M3 (self + 4)) (memLoad32 M3 (self + 8)) 8 =
      bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 := by rw [l0, l4, l8]
  have sp10 : reg m10 sp = S := (fr10 sp (by decide) (by decide) (by decide)).trans sp9
  have s010 : reg m10 8 = out := (fr10 8 (by decide) (by decide) (by decide)).trans s09
  have s110 : reg m10 9 = 8 := (fr10 9 (by decide) (by decide) (by decide)).trans s19
  have hz10 : reg m10 0 = 0 := (fr10 0 (by decide) (by decide) (by decide)).trans (by rw [regs9]; rfl)
  have k10 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
      reg m10 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    (fr10 r h3 h4 h5).trans (keep9 r h0 h2 h6 h7 h8 h9)
  have outS : ∀ x, Sep S 32 x 1 → Sep (S + 0xC) 8 x 1 := fun x hx => hx.sub (c := 0xC) (l := 8) (by omega)
  have mOut : ∀ x, Sep S 32 x 1 → m10.mem x = match bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 with
      | none => m.mem x
      | some (_, e) => memStore32 m.mem (self + 8) e x := fun x hx => by
    rw [mem10, bytesMem_outside (outS x hx), hR]
    cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 with
    | none => exact M3out x hx
    | some pe => exact memStore32_congr (M3out x hx)
  have hc10 : CodeIn m10.mem base readerU64Code := fun i hi => by
    rw [mOut _ (hSc.subR (c := i) (l := 1) (by omega))]
    cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 with
    | none => exact hc i hi
    | some pe => exact (memStore32_get_sep (hEc.subR (c := i) (l := 1) (by omega))).trans (hc i hi)
  have frS : ∀ c, 0x14 ≤ c → c + 4 ≤ 32 → memLoad32 m10.mem (S + BitVec.ofNat 32 c) = memLoad32 M3 (S + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      rw [mem10]
      exact bytesMem_load (sep_offsets S (c := 0xC) (n := 8) (d := c) (k := 4) (Or.inl (by omega)) (by omega) (by omega))
        ((hRS.sub (c := 8) (l := 4) (by omega)).subR (c := c) (l := 4) (by omega))
  have st8 : ∀ (Mx : Word → BitVec 8) (a : Word) (v : BitVec 8) (k : Nat), k < 16 → a = out + BitVec.ofNat 32 k →
      ∀ c, 0x14 ≤ c → c + 4 ≤ 32 → memLoad32 (memStore8 Mx a v) (S + BitVec.ofNat 32 c) = memLoad32 Mx (S + BitVec.ofNat 32 c) :=
    fun Mx a v k hk ha c h1 h2 => memLoad32_congr fun j hj => memStore8_ne (by
      rw [add_ofNat_assoc, ha]; exact fun e => hOS k hk (c + j) (by omega) e.symm)
  have st32 : ∀ (Mx : Word → BitVec 8) (v : Word) (k : Nat), k + 4 ≤ 16 →
      ∀ c, 0x14 ≤ c → c + 4 ≤ 32 → memLoad32 (memStore32 Mx (out + BitVec.ofNat 32 k) v) (S + BitVec.ofNat 32 c) =
        memLoad32 Mx (S + BitVec.ofNat 32 c) :=
    fun Mx v k hk c h1 h2 => memLoad32_store32_sep ((hOS.sub (c := k) (l := 4) hk).subR (c := c) (l := 4) (by omega))
  have frm : ∀ (Mx : Word → BitVec 8),
      (∀ c, 0x14 ≤ c → c + 4 ≤ 32 → memLoad32 Mx (S + BitVec.ofNat 32 c) = memLoad32 m10.mem (S + BitVec.ofNat 32 c)) →
      ∀ v, memLoad32 (memStore8 Mx out v) (S + 0x1C) = reg m ra ∧ memLoad32 (memStore8 Mx out v) (S + 0x18) = reg m 8 ∧
        memLoad32 (memStore8 Mx out v) (S + 0x14) = reg m 9 := fun Mx h v =>
    ⟨(st8 Mx out v 0 (by omega) (add_ofNat_zero out).symm 0x1C (by omega) (by omega)).trans
        ((h 0x1C (by omega) (by omega)).trans ((frS 0x1C (by omega) (by omega)).trans fA)),
      (st8 Mx out v 0 (by omega) (add_ofNat_zero out).symm 0x18 (by omega) (by omega)).trans
        ((h 0x18 (by omega) (by omega)).trans ((frS 0x18 (by omega) (by omega)).trans fB)),
      (st8 Mx out v 0 (by omega) (add_ofNat_zero out).symm 0x14 (by omega) (by omega)).trans
        ((h 0x14 (by omega) (by omega)).trans ((frS 0x14 (by omega) (by omega)).trans fC))⟩
  have tail : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx base mx 0x74 fx →
      CodeIn Mx base readerU64Code → fx sp = S → fx 8 = out →
      memLoad32 (memStore8 Mx out ((fx a0).extractLsb' 0 8)) (S + 0x1C) = reg m ra ∧
        memLoad32 (memStore8 Mx out ((fx a0).extractLsb' 0 8)) (S + 0x18) = reg m 8 ∧
        memLoad32 (memStore8 Mx out ((fx a0).extractLsb' 0 8)) (S + 0x14) = reg m 9 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra → r ≠ sp → r ≠ 8 →
        r ≠ 9 → fx r = reg m r) →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → reg m' r = reg m r) ∧
        m'.mem = memStore8 Mx out ((fx a0).extractLsb' 0 8) := by
    intro Mx mx fx s hcx hs h8 ⟨hA, hB, hC⟩ hk
    obtain ⟨n1, d1, u1⟩ := s.sb hcx u64_at_74 (off' := 0x78) (by decide)
    rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out] at u1
    have hc1 := hcx.store8 (v := (fx a0).extractLsb' 0 8) (a := out)
      (by have := hOc.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this)
    obtain ⟨n2, d2, u2⟩ := u1.lw hc1 u64_at_78 (off' := 0x7A) (by decide)
      (by rw [hs]; exact aligned_add hSa (k := 0x1C) (by decide))
    rw [hs, hA] at u2
    obtain ⟨n3, d3, u3⟩ := u2.lw hc1 u64_at_7a (off' := 0x7C) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hSa (k := 0x18) (by decide))
    rw [show upd fx ra (reg m ra) sp = S by simp +decide only [upd]; exact hs, hB] at u3
    obtain ⟨n4, d4, u4⟩ := u3.lw hc1 u64_at_7c (off' := 0x7E) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hSa (k := 0x14) (by decide))
    rw [show upd (upd fx ra (reg m ra)) 8 (reg m 8) sp = S by simp +decide only [upd]; exact hs, hC] at u4
    obtain ⟨n5, d5, u5⟩ := u4.aluImm hc1 u64_at_7e (off' := 0x80) (by decide)
    obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc1 u64_at_80
    refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), ?_, ?_,
      fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_, by rw [mem6]⟩
    · rw [pc6, add_lit_zero]; simp +decide only [upd, ite_true, ite_false]; rw [hra, hret]
    · rw [regs6]; simp +decide only [upd, ite_true, ite_false]; rw [hs, ← hspS]; rfl
    · rw [regs6]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      by_cases hsp' : r = sp
      · subst hsp'; simp +decide [upd]; rw [hs, ← hspS]; rfl
      by_cases hra' : r = ra
      · subst hra'; simp +decide [upd]
      by_cases h8' : r = 8
      · subst h8'; simp +decide [upd]
      by_cases h9' : r = 9
      · subst h9'; simp +decide [upd]
      simp [upd, hr, hsp', hra', h8', h9']
      exact hk r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8' h9'
  have us : ∀ (g : Fin 32 → Word) (r : Fin 32) (v : Word), r.val ≠ 0 → upd g r v r = v := fun g r v h => by
    simp only [upd, h, ↓reduceIte]
  have pre : Steps m m10 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
    (c9.trans c10))))))))
  have t10 : St m10.mem base m10 0x18 (reg m10) := ⟨by rw [pc10], rfl, fun _ => rfl⟩
  obtain ⟨n11, e11, t11⟩ := t10.lw hc10 u64_at_18 (off' := 0x1A) (by decide)
    (by rw [sp10]; exact aligned_add hSa (k := 0xC) (by decide))
  rw [sp10] at t11
  rcases hR1 : bytesResult ptr len (memLoad32 m.mem (self + 8)) 8 with _ | ⟨p, e⟩
  · obtain ⟨b0, b4⟩ := bytesMem_none (out := S + 0xC) (hR.trans hR1)
    rw [← mem10] at b0 b4
    rw [b0] at t11
    obtain ⟨n12, e12, t12⟩ := t11.taken hc10 0x66 u64_at_1a (by decide)
      (by rw [us _ a1 _ (by decide)]; exact (by decide : branchTaken .beq 0 0 = true))
    obtain ⟨n13, e13, t13⟩ := t12.lbu hc10 u64_at_66 (off' := 0x6A) (by decide)
    rw [updz hz10 (show sp ≠ a1 by decide), sp10, show S + (0x10 : Word) = S + 0xC + 4 by rw [BitVec.add_assoc]; rfl,
      b4] at t13
    obtain ⟨n14, e14, t14⟩ := t13.jump hc10 u64_at_6a (off' := 0x6E) (by decide)
      (by rw [t13.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x6E (by decide)))
    obtain ⟨n15, e15, t15⟩ := t14.sb hc10 u64_at_6e (off' := 0x72) (by decide)
    rw [updz t11.zero (show (8 : Fin 32) ≠ a0 by decide), updz hz10 (show (8 : Fin 32) ≠ a1 by decide), s010,
      us _ a0 _ (by decide)] at t15
    have hc15 := hc10.store8 (v := ((0 : BitVec 8).zeroExtend 32).extractLsb' 0 8) (a := out + 0x1)
      (hOc.sub (c := 1) (l := 1) (by omega))
    obtain ⟨n16, e16, t16⟩ := t15.aluImm hc15 u64_at_72 (off' := 0x74) (by decide)
    obtain ⟨m', c', pc', sp', k', mem'⟩ := tail _ _ _ t16 hc15
      (by rw [updz t15.zero (by decide), updz t11.zero (by decide), updz hz10 (by decide), sp10])
      (by rw [updz t15.zero (by decide), updz t11.zero (by decide), updz hz10 (by decide), s010])
      (frm _ (fun c h1 h2 => st8 _ _ _ 1 (by omega) rfl c h1 h2) _)
      (fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 => by
        rw [updz t15.zero h0, updz t11.zero h0, updz hz10 h1]; exact k10 r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9)
    refine ⟨m', pre.trans (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 c')))))), pc', sp', k',
      fun x hx => ?_⟩
    have mx : m10.mem x = m.mem x := by rw [mOut x hx, hR1]
    rw [mem']; unfold u64Mem; rw [hptr, hlen, hR1]
    exact memStore8_congr (memStore8_congr mx)
  · obtain ⟨b0, b4⟩ := bytesMem_some (out := S + 0xC) (hR.trans hR1)
    rw [← mem10] at b0 b4
    rw [b0] at t11
    have hp0 : p ≠ 0 := bytesResult_ne_zero hbuf.1 hbuf.2 (by decide) hR1
    obtain ⟨hp1, hle⟩ : ptr + memLoad32 m.mem (self + 8) = p ∧ (memLoad32 m.mem (self + 8)).toNat + 8 ≤ len.toNat := by
      have hb2 := hR1
      rw [bytesResult_eq] at hb2
      split at hb2
      · next h => injection hb2 with h'; injection h' with h1 h2; exact ⟨h1, h⟩
      · cases hb2
    have bt : ∀ i, i < 8 → m10.mem (p + BitVec.ofNat 32 i) = m.mem (p + BitVec.ofNat 32 i) := fun i hi => by
      have addr : p + BitVec.ofNat 32 i = ptr + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + i) := by
        rw [← hp1, ← add_ofNat_assoc, Cur.ofNat_toNat_self]
      have sS : Sep S 32 (p + BitVec.ofNat 32 i) 1 := by
        rw [addr]; exact (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + i) (l := 1) (by omega)).symm
      have sE : Sep (self + 8) 4 (p + BitVec.ofNat 32 i) 1 := by
        rw [addr]; exact (hBE.sub (c := (memLoad32 m.mem (self + 8)).toNat + i) (l := 1) (by omega)).symm
      rw [mOut _ sS, hR1]; exact memStore32_get_sep sE
    have bt0 : m10.mem p = m.mem p := by have := bt 0 (by omega); rwa [add_ofNat_zero] at this
    obtain ⟨n12, e12, t12⟩ := t11.notTaken hc10 0x1C u64_at_1a (by decide)
      (by rw [us _ a1 _ (by decide)]; show (p == 0) = false; exact beq_eq_false_iff_ne.mpr hp0)
    obtain ⟨n13, e13, t13⟩ := t12.lw hc10 u64_at_1c (off' := 0x1E) (by decide)
      (by rw [updz hz10 (show sp ≠ a1 by decide), sp10]; exact aligned_add hSa (k := 0x10) (by decide))
    rw [updz hz10 (show sp ≠ a1 by decide), sp10, show S + (0x10 : Word) = S + 0xC + 4 by rw [BitVec.add_assoc]; rfl,
      b4] at t13
    obtain ⟨n14, e14, t14⟩ := t13.notTaken hc10 0x22 u64_at_1e (by decide)
      (by rw [us _ a0 _ (by decide), updz t11.zero (show (9 : Fin 32) ≠ a0 by decide),
        updz hz10 (show (9 : Fin 32) ≠ a1 by decide), s110]; decide)
    obtain ⟨n15, e15, t15⟩ := t14.aluImm hc10 u64_at_22 (off' := 0x24) (by decide)
    have q15a1 : reg n15 a1 = p := by rw [t15.regs]; simp +decide [upd]
    have q15a0 : reg n15 a0 = 0 := by rw [t15.regs]; simp +decide [upd, aluEval]
    have q158 : reg n15 8 = out := by rw [t15.regs]; simp +decide [upd, s010]
    have q15sp : reg n15 sp = S := by rw [t15.regs]; simp +decide [upd, sp10]
    obtain ⟨n16, e16, u16⟩ := t15.self.lbu hc10 u64_at_24 (off' := 0x28) (by decide)
    rw [q15a1, show m10.mem (p + 0x1) = m.mem (p + 0x1) from bt 1 (by omega)] at u16
    have q16 : reg n16 a1 = p := by rw [u16.regs]; simp +decide [upd, q15a1]
    obtain ⟨n17, e17, u17⟩ := u16.self.lbu hc10 u64_at_28 (off' := 0x2C) (by decide)
    rw [q16, add_lit_zero, bt0] at u17
    have q17 : reg n17 a1 = p := by rw [u17.regs]; simp +decide [upd, q16]
    obtain ⟨n18, e18, u18⟩ := u17.self.lbu hc10 u64_at_2c (off' := 0x30) (by decide)
    rw [q17, show m10.mem (p + 0x2) = m.mem (p + 0x2) from bt 2 (by omega)] at u18
    have q18 : reg n18 a1 = p := by rw [u18.regs]; simp +decide [upd, q17]
    obtain ⟨n19, e19, u19⟩ := u18.self.lbu hc10 u64_at_30 (off' := 0x34) (by decide)
    rw [q18, show m10.mem (p + 0x3) = m.mem (p + 0x3) from bt 3 (by omega)] at u19
    have q19 : reg n19 a1 = p := by rw [u19.regs]; simp +decide [upd, q18]
    obtain ⟨n20, e20, u20⟩ := u19.self.aluImm hc10 u64_at_34 (off' := 0x36) (by decide)
    have q20 : reg n20 a1 = p := by rw [u20.regs]; simp +decide [upd, q19]
    obtain ⟨n21, e21, u21⟩ := u20.self.lbu hc10 u64_at_36 (off' := 0x3A) (by decide)
    rw [q20, show m10.mem (p + 0x5) = m.mem (p + 0x5) from bt 5 (by omega)] at u21
    have q21 : reg n21 a1 = p := by rw [u21.regs]; simp +decide [upd, q20]
    obtain ⟨n22, e22, u22⟩ := u21.self.lbu hc10 u64_at_3a (off' := 0x3E) (by decide)
    rw [q21, show m10.mem (p + 0x6) = m.mem (p + 0x6) from bt 6 (by omega)] at u22
    have q22 : reg n22 a1 = p := by rw [u22.regs]; simp +decide [upd, q21]
    obtain ⟨n23, e23, u23⟩ := u22.self.lbu hc10 u64_at_3e (off' := 0x42) (by decide)
    rw [q22, show m10.mem (p + 0x7) = m.mem (p + 0x7) from bt 7 (by omega)] at u23
    have q23 : reg n23 a1 = p := by rw [u23.regs]; simp +decide [upd, q22]
    obtain ⟨n24, e24, u24⟩ := u23.self.lbu hc10 u64_at_42 (off' := 0x46) (by decide)
    rw [q23, show m10.mem (p + 0x4) = m.mem (p + 0x4) from bt 4 (by omega)] at u24
    obtain ⟨n25, e25, u25⟩ := u24.self.alu hc10 u64_at_46 (off' := 0x4A) (by decide)
    obtain ⟨n26, e26, u26⟩ := u25.self.aluImm hc10 u64_at_4a (off' := 0x4C) (by decide)
    obtain ⟨n27, e27, u27⟩ := u26.self.aluImm hc10 u64_at_4c (off' := 0x4E) (by decide)
    obtain ⟨n28, e28, u28⟩ := u27.self.alu hc10 u64_at_4e (off' := 0x52) (by decide)
    obtain ⟨n29, e29, u29⟩ := u28.self.aluImm hc10 u64_at_52 (off' := 0x54) (by decide)
    obtain ⟨n30, e30, u30⟩ := u29.self.aluImm hc10 u64_at_54 (off' := 0x56) (by decide)
    obtain ⟨n31, e31, u31⟩ := u30.self.aluImm hc10 u64_at_56 (off' := 0x58) (by decide)
    obtain ⟨n32, e32, u32⟩ := u31.self.alu hc10 u64_at_58 (off' := 0x5A) (by decide)
    obtain ⟨n33, e33, u33⟩ := u32.self.alu hc10 u64_at_5a (off' := 0x5C) (by decide)
    obtain ⟨n34, e34, u34⟩ := u33.self.alu hc10 u64_at_5c (off' := 0x5E) (by decide)
    obtain ⟨n35, e35, u35⟩ := u34.self.alu hc10 u64_at_5e (off' := 0x60) (by decide)
    have vlo : reg n35 a2 = memLoad32 m.mem p := by
      rw [u35.regs]; simp +decide only [upd, ite_true, ite_false, u34.regs, u33.regs, u32.regs, u31.regs, u30.regs, u29.regs, u28.regs, u27.regs, u26.regs, u25.regs, u24.regs, u23.regs, u22.regs, u21.regs, u20.regs, u19.regs, u18.regs, u17.regs, u16.regs]
      exact or_assemble' _ _ _ _
    have hi4 : memLoad32 m.mem (p + 4) = m.mem (p + 0x7) ++ m.mem (p + 0x6) ++ m.mem (p + 0x5) ++ m.mem (p + 0x4) := by
      unfold memLoad32; rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl
    have vhi : reg n35 a1 = memLoad32 m.mem (p + 4) := by
      rw [u35.regs]; simp +decide only [upd, ite_true, ite_false, u34.regs, u33.regs, u32.regs, u31.regs, u30.regs, u29.regs, u28.regs, u27.regs, u26.regs, u25.regs, u24.regs, u23.regs, u22.regs, u21.regs, u20.regs, u19.regs, u18.regs, u17.regs, u16.regs]
      exact (Cur.or_assemble _ _ _ _).trans hi4.symm
    have v8 : reg n35 8 = out := by
      rw [u35.regs]; simp +decide only [upd, ite_true, ite_false, u34.regs, u33.regs, u32.regs, u31.regs, u30.regs, u29.regs, u28.regs, u27.regs, u26.regs, u25.regs, u24.regs, u23.regs, u22.regs, u21.regs, u20.regs, u19.regs, u18.regs, u17.regs, u16.regs]; exact q158
    have vsp : reg n35 sp = S := by
      rw [u35.regs]; simp +decide only [upd, ite_true, ite_false, u34.regs, u33.regs, u32.regs, u31.regs, u30.regs, u29.regs, u28.regs, u27.regs, u26.regs, u25.regs, u24.regs, u23.regs, u22.regs, u21.regs, u20.regs, u19.regs, u18.regs, u17.regs, u16.regs]; exact q15sp
    have va0 : reg n35 a0 = 0 := by
      rw [u35.regs]; simp +decide only [upd, ite_true, ite_false, u34.regs, u33.regs, u32.regs, u31.regs, u30.regs, u29.regs, u28.regs, u27.regs, u26.regs, u25.regs, u24.regs, u23.regs, u22.regs, u21.regs, u20.regs, u19.regs, u18.regs, u17.regs, u16.regs]; exact q15a0
    have vk : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 17 → r ≠ ra → r ≠ sp →
        r ≠ 8 → r ≠ 9 → reg n35 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h7 hra' hsp' h8 h9 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; rw [u35.self.zero, hz]
      rw [u35.regs]; simp only [upd, hr, h1, h2, h3, h4, h5, h6, h7, h9, ↓reduceIte, u34.regs, u33.regs, u32.regs, u31.regs, u30.regs, u29.regs, u28.regs, u27.regs, u26.regs, u25.regs, u24.regs, u23.regs, u22.regs, u21.regs, u20.regs, u19.regs, u18.regs, u17.regs, u16.regs]
      rw [t15.regs]; simp only [upd, hr, h0, h1, ↓reduceIte]
      exact k10 r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9
    obtain ⟨n36, e36, u36⟩ := u35.self.sw hc10 u64_at_60 (off' := 0x62) (by decide)
      (by rw [v8]; exact aligned_add hout (k := 8) (by decide))
    rw [v8, vlo] at u36
    have hc36 := hc10.store32 (v := memLoad32 m.mem p) (a := out + 0x8) (hOc.sub (c := 8) (l := 4) (by omega))
    obtain ⟨n37, e37, u37⟩ := u36.sw hc36 u64_at_62 (off' := 0x64) (by decide)
      (by rw [v8]; exact aligned_add hout (k := 0xC) (by decide))
    rw [v8, vhi] at u37
    have hc37 := hc36.store32 (v := memLoad32 m.mem (p + 4)) (a := out + 0xC) (hOc.sub (c := 0xC) (l := 4) (by omega))
    obtain ⟨n38, e38, u38⟩ := u37.jump hc37 u64_at_64 (off' := 0x74) (by decide)
      (by rw [u37.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x74 (by decide)))
    obtain ⟨m', c', pc', sp', k', mem'⟩ := tail _ _ _ u38 hc37 vsp v8
      (frm _ (fun c h1 h2 => (st32 _ _ 0xC (by omega) c h1 h2).trans (st32 _ _ 8 (by omega) c h1 h2)) _) vk
    refine ⟨m', pre.trans (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.cons e15 (.cons e16 (.cons e17 (.cons e18 (.cons e19 (.cons e20 (.cons e21 (.cons e22 (.cons e23 (.cons e24 (.cons e25 (.cons e26 (.cons e27 (.cons e28 (.cons e29 (.cons e30 (.cons e31 (.cons e32 (.cons e33 (.cons e34 (.cons e35 (.cons e36 (.cons e37 (.cons e38 c')))))))))))))))))))))))))))), pc', sp', k', fun x hx => ?_⟩
    have mx : m10.mem x = memStore32 m.mem (self + 8) e x := by rw [mOut x hx, hR1]
    rw [mem', va0]; unfold u64Mem; rw [hptr, hlen, hR1]
    exact memStore8_congr (memStore32_congr (memStore32_congr mx))

end C3.RV32





