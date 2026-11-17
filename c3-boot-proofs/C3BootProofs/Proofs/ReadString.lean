import C3BootProofs.Proofs.Window
import C3BootProofs.Proofs.U16

/-!
# `c3_verify::trustroot::read_string`

`read_string(r, wide, max, printable)` reads a length, as a little-endian
`u16` when `wide` is set and a `u8` otherwise, checks that it is between 1
and `max`, and takes that many bytes with `Reader::bytes`. When `printable`
is set, every byte must be printable ASCII, from 0x20 to 0x7E. It returns
`Result<&[u8], Error>`: a pointer, null for `Err`, and the length or the
error byte (`Truncated` 0, `OutOfRange` 5, or 0xC for an unprintable byte).
-/

namespace C3.RV32

open C3.Image

/-- The length `read_string` reads, and the reader's new position. -/
def strCount (M : Word → BitVec 8) (self wide : Word) : Option (Word × Word) :=
  if wide = 0 then
    match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 1 with
    | none => none
    | some (p, e) => some ((M p).zeroExtend 32, e)
  else
    match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 2 with
    | none => none
    | some (p, e) => some ((M (p + 1)).zeroExtend 32 <<< 8 ||| (M p).zeroExtend 32, e)

/-- A printable ASCII byte. -/
def printableByte (b : BitVec 8) : Prop := 0x20 ≤ b.toNat ∧ b.toNat ≤ 0x7E

instance (b : BitVec 8) : Decidable (printableByte b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Memory after `read_string` returns once it has read the length `n` and
moved the reader to `e`. -/
def strTail (M : Word → BitVec 8) (out self e n max printable : Word) : Word → BitVec 8 :=
  if (n + 0xFFFFFFFF).ult max then
    match bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) e n with
    | none => memStore8 (memStore32 (memStore32 M (self + 8) e) out 0) (out + 4) 0
    | some (q, e') =>
      if printable = 0 ∨ ∀ i, i < n.toNat → printableByte (M (q + BitVec.ofNat 32 i)) then
        memStore32 (memStore32 (memStore32 M (self + 8) e') out q) (out + 4) n
      else memStore8 (memStore32 (memStore32 M (self + 8) e') out 0) (out + 4) 0xC
  else memStore8 (memStore32 (memStore32 M (self + 8) e) out 0) (out + 4) 5

/-- Memory after `read_string` returns, outside the stack it uses. -/
def strMem (M : Word → BitVec 8) (out self wide max printable : Word) : Word → BitVec 8 :=
  match strCount M self wide with
  | none => memStore8 (memStore32 M out 0) (out + 4) 0
  | some (n, e) => strTail M out self e n max printable

set_option maxRecDepth 10000

theorem rstr_at_0 : fetchRel readStringCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem rstr_at_2 : fetchRel readStringCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem rstr_at_4 : fetchRel readStringCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem rstr_at_6 : fetchRel readStringCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem rstr_at_8 : fetchRel readStringCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem rstr_at_a : fetchRel readStringCode 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem rstr_at_c : fetchRel readStringCode 0xC = some (.alu .add (18 : Fin 32) x0 a4, 2) := by decide
theorem rstr_at_e : fetchRel readStringCode 0xE = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem rstr_at_10 : fetchRel readStringCode 0x10 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem rstr_at_12 : fetchRel readStringCode 0x12 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem rstr_at_14 : fetchRel readStringCode 0x14 = some (.alu .add a0 x0 a1, 2) := by decide
theorem rstr_at_16 : fetchRel readStringCode 0x16 = some (.branch .beq a2 x0 0x14, 2) := by decide
theorem rstr_at_18 : fetchRel readStringCode 0x18 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem rstr_at_1c : fetchRel readStringCode 0x1C = some (.jalr ra ra 0x506, 4) := by decide
theorem rstr_at_20 : fetchRel readStringCode 0x20 = some (.aluImm .and a1 a0 0x1, 4) := by decide
theorem rstr_at_24 : fetchRel readStringCode 0x24 = some (.branch .beq a1 x0 0x1C, 2) := by decide
theorem rstr_at_26 : fetchRel readStringCode 0x26 = some (.aluImm .srl a0 a0 0x8, 2) := by decide
theorem rstr_at_28 : fetchRel readStringCode 0x28 = some (.jal x0 0x6A, 2) := by decide
theorem rstr_at_2a : fetchRel readStringCode 0x2A = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem rstr_at_2e : fetchRel readStringCode 0x2E = some (.jalr ra ra 0x3F8, 4) := by decide
theorem rstr_at_32 : fetchRel readStringCode 0x32 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem rstr_at_34 : fetchRel readStringCode 0x34 = some (.branch .beq a0 x0 0x12, 2) := by decide
theorem rstr_at_36 : fetchRel readStringCode 0x36 = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem rstr_at_3a : fetchRel readStringCode 0x3A = some (.store .sb (8 : Fin 32) a1 0x4, 4) := by decide
theorem rstr_at_3e : fetchRel readStringCode 0x3E = some (.jal x0 0x5C, 2) := by decide
theorem rstr_at_40 : fetchRel readStringCode 0x40 = some (.aluImm .srl a2 a0 0x10, 4) := by decide
theorem rstr_at_44 : fetchRel readStringCode 0x44 = some (.jal x0 0x6, 2) := by decide
theorem rstr_at_46 : fetchRel readStringCode 0x46 = some (.aluImm .and a2 a1 0xFF, 4) := by decide
theorem rstr_at_4a : fetchRel readStringCode 0x4A = some (.aluImm .add a0 a2 0xFFFFFFFF, 4) := by decide
theorem rstr_at_4e : fetchRel readStringCode 0x4E = some (.branch .bgeu a0 (19 : Fin 32) 0x36, 4) := by decide
theorem rstr_at_52 : fetchRel readStringCode 0x52 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem rstr_at_54 : fetchRel readStringCode 0x54 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem rstr_at_56 : fetchRel readStringCode 0x56 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem rstr_at_5a : fetchRel readStringCode 0x5A = some (.jalr ra ra 0x4A2, 4) := by decide
theorem rstr_at_5e : fetchRel readStringCode 0x5E = some (.load .lw a0 sp 0x4, 2) := by decide
theorem rstr_at_60 : fetchRel readStringCode 0x60 = some (.branch .beq a0 x0 0x2E, 2) := by decide
theorem rstr_at_62 : fetchRel readStringCode 0x62 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem rstr_at_64 : fetchRel readStringCode 0x64 = some (.branch .beq (18 : Fin 32) x0 0x24, 4) := by decide
theorem rstr_at_68 : fetchRel readStringCode 0x68 = some (.aluImm .add a2 x0 0x5F, 4) := by decide
theorem rstr_at_6c : fetchRel readStringCode 0x6C = some (.alu .add a3 x0 a1, 2) := by decide
theorem rstr_at_6e : fetchRel readStringCode 0x6E = some (.alu .add a4 x0 a0, 2) := by decide
theorem rstr_at_70 : fetchRel readStringCode 0x70 = some (.branch .beq a3 x0 0x18, 2) := by decide
theorem rstr_at_72 : fetchRel readStringCode 0x72 = some (.load .lbu a5 a4 0x0, 4) := by decide
theorem rstr_at_76 : fetchRel readStringCode 0x76 = some (.aluImm .add a4 a4 0x1, 2) := by decide
theorem rstr_at_78 : fetchRel readStringCode 0x78 = some (.aluImm .add a5 a5 0xFFFFFFE0, 2) := by decide
theorem rstr_at_7a : fetchRel readStringCode 0x7A = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem rstr_at_7c : fetchRel readStringCode 0x7C = some (.branch .bltu a5 a2 0xFFFFFFF4, 4) := by decide
theorem rstr_at_80 : fetchRel readStringCode 0x80 = some (.aluImm .add a0 x0 0xC, 2) := by decide
theorem rstr_at_82 : fetchRel readStringCode 0x82 = some (.jal x0 0x10, 2) := by decide
theorem rstr_at_84 : fetchRel readStringCode 0x84 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem rstr_at_86 : fetchRel readStringCode 0x86 = some (.jal x0 0xC, 2) := by decide
theorem rstr_at_88 : fetchRel readStringCode 0x88 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem rstr_at_8a : fetchRel readStringCode 0x8A = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem rstr_at_8c : fetchRel readStringCode 0x8C = some (.jal x0 0xE, 2) := by decide
theorem rstr_at_8e : fetchRel readStringCode 0x8E = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem rstr_at_92 : fetchRel readStringCode 0x92 = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem rstr_at_96 : fetchRel readStringCode 0x96 = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem rstr_at_9a : fetchRel readStringCode 0x9A = some (.load .lw ra sp 0x1C, 2) := by decide
theorem rstr_at_9c : fetchRel readStringCode 0x9C = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem rstr_at_9e : fetchRel readStringCode 0x9E = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem rstr_at_a0 : fetchRel readStringCode 0xA0 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem rstr_at_a2 : fetchRel readStringCode 0xA2 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem rstr_at_a4 : fetchRel readStringCode 0xA4 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem rstr_at_a6 : fetchRel readStringCode 0xA6 = some (.jalr x0 ra 0x0, 2) := by decide

theorem printable_ult : ∀ b : BitVec 8,
    (aluEval .add (b.zeroExtend 32) 0xFFFFFFE0).ult 0x5F = decide (printableByte b) := by decide

theorem u16_shift (b0 b1 : BitVec 8) :
    aluEval .srl ((b1.zeroExtend 32 <<< 24 ||| b0.zeroExtend 32 <<< 16)) 0x10 =
      b1.zeroExtend 32 <<< 8 ||| b0.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((b1.zeroExtend 32 <<< 24 ||| b0.zeroExtend 32 <<< 16) >>> 16).getLsbD i = _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h8 : i < 8
  · simp [hi, show 16 + i < 32 by omega, show 16 + i < 24 by omega, show ¬ (16 + i < 16) by omega, h8]
  · have hb0 := BitVec.getLsbD_of_ge b0 i (by omega)
    by_cases h16 : i < 16
    · simp [hi, show 16 + i < 32 by omega, show ¬ (16 + i < 24) by omega, show ¬ (16 + i < 16) by omega, h8, hb0,
        show 16 + i - 24 = i - 8 by omega, show i - 8 < 32 by omega]
    · have hb1 := BitVec.getLsbD_of_ge b1 (i - 8) (by omega)
      simp [hi, show ¬ (16 + i < 32) by omega, h8, hb0, hb1]

set_option maxRecDepth 20000 in
theorem rstr_loop {M : Word → BitVec 8} {base : Word} (hc : CodeIn M base readStringCode) :
    ∀ (k : Nat) (mx : Machine) (ptr : Word), k < 2 ^ 32 → St M base mx 0x70 (reg mx) →
      reg mx a3 = BitVec.ofNat 32 k → reg mx a4 = ptr → reg mx a2 = 0x5F →
      ∃ mx', Steps mx mx' ∧ (∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg mx' r = reg mx r) ∧
        ((∀ i, i < k → printableByte (M (ptr + BitVec.ofNat 32 i))) → St M base mx' 0x88 (reg mx')) ∧
        (¬ (∀ i, i < k → printableByte (M (ptr + BitVec.ofNat 32 i))) → St M base mx' 0x80 (reg mx')) := by
  intro k
  induction k with
  | zero =>
    intro mx ptr _ s h3 _ _
    obtain ⟨m1, e1, t1⟩ := s.taken hc 0x88 rstr_at_70 (by decide)
      (by rw [h3, show reg mx x0 = 0 from s.zero]; decide)
    exact ⟨m1, .single e1, fun r _ _ _ => t1.regs r, fun _ => t1.self, fun h => absurd (fun i hi => absurd hi (by omega)) h⟩
  | succ k ih =>
    intro mx ptr hk s h3 h4 h2
    have hz := s.zero
    obtain ⟨m1, e1, t1⟩ := s.notTaken hc 0x72 rstr_at_70 (by decide)
      (by
        rw [h3, show reg mx x0 = 0 from hz]
        refine beq_eq_false_iff_ne.mpr fun h => ?_
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
        exact absurd this (by show k + 1 ≠ 0; omega))
    obtain ⟨m2, e2, t2⟩ := t1.lbu hc rstr_at_72 (off' := 0x76) (by decide)
    rw [h4, add_lit_zero] at t2
    obtain ⟨m3, e3, t3⟩ := t2.aluImm hc rstr_at_76 (off' := 0x78) (by decide)
    obtain ⟨m4, e4, t4⟩ := t3.aluImm hc rstr_at_78 (off' := 0x7A) (by decide)
    obtain ⟨m5, e5, t5⟩ := t4.aluImm hc rstr_at_7a (off' := 0x7C) (by decide)
    have r5a5 : reg m5 a5 = aluEval .add ((M ptr).zeroExtend 32) 0xFFFFFFE0 := by
      rw [t5.regs]; simp +decide only [upd, ite_true, ite_false]
    have r5a2 : reg m5 a2 = 0x5F := by rw [t5.regs]; simp +decide only [upd, ite_true, ite_false]; exact h2
    have r5a3 : reg m5 a3 = BitVec.ofNat 32 k := by
      rw [t5.regs]; simp +decide only [upd, ite_true, ite_false]; rw [h3]
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = (BitVec.ofNat 32 k).toNat
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
      omega
    have r5a4 : reg m5 a4 = ptr + 1 := by rw [t5.regs]; simp +decide only [upd, ite_true, ite_false]; rw [h4]; rfl
    have r5k : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m5 r = reg mx r := fun r h3' h4' h5' => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; rw [t5.self.zero, hz]
      rw [t5.regs]; simp only [upd, hr, h3', h4', h5', ↓reduceIte]
    have addr : ∀ j, ptr + 1 + BitVec.ofNat 32 j = ptr + BitVec.ofNat 32 (j + 1) := fun j => by
      rw [show (ptr + 1 : Word) = ptr + BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, Nat.add_comm]
    by_cases hp : printableByte (M ptr)
    · obtain ⟨m6, e6, t6⟩ := t5.self.taken hc 0x70 rstr_at_7c (by decide)
        (by
          rw [r5a5, r5a2]
          show (aluEval .add ((M ptr).zeroExtend 32) 0xFFFFFFE0).ult 0x5F = true
          rw [printable_ult]; exact decide_eq_true hp)
      obtain ⟨mx', c', k', h88, h80⟩ := ih m6 (ptr + 1) (by omega) t6.self (by rw [t6.regs]; exact r5a3)
        (by rw [t6.regs]; exact r5a4) (by rw [t6.regs]; exact r5a2)
      refine ⟨mx', .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 c'))))),
        fun r h3' h4' h5' => by rw [k' r h3' h4' h5', t6.regs, r5k r h3' h4' h5'],
        fun hall => h88 fun i hi => ?_, fun hn => h80 fun hall => hn fun i hi => ?_⟩
      · rw [addr]; exact hall (i + 1) (by omega)
      · cases i with
        | zero => rw [add_ofNat_zero]; exact hp
        | succ j => have := hall j (by omega); rwa [addr] at this
    · obtain ⟨m6, e6, t6⟩ := t5.self.notTaken hc 0x80 rstr_at_7c (by decide)
        (by
          rw [r5a5, r5a2]
          show (aluEval .add ((M ptr).zeroExtend 32) 0xFFFFFFE0).ult 0x5F = false
          rw [printable_ult]; exact decide_eq_false hp)
      refine ⟨m6, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.single e6))))),
        fun r h3' h4' h5' => by rw [t6.regs, r5k r h3' h4' h5'],
        fun hall => absurd (by have := hall 0 (by omega); rwa [add_ofNat_zero] at this) hp, fun _ => t6.self⟩

theorem u16_tag (b0 b1 : BitVec 8) : aluEval .and (b1.zeroExtend 32 <<< 24 ||| b0.zeroExtend 32 <<< 16) 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show ((b1.zeroExtend 32 <<< 24 ||| b0.zeroExtend 32 <<< 16) &&& 1).getLsbD i = (0 : Word).getLsbD i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases h0 : i = 0
  · subst h0; simp
  · simp [h0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`read_string`, as compiled**: with `Reader::u16`, `Reader::u8`, and
`Reader::bytes` where the image puts them, a reader `self` over a slice that
is not null and doesn't wrap, a result address `out`, and 48 bytes of stack
below `sp`, all apart as the hypotheses list, it returns to `ra` with the
registers but `a0` through `a5` restored, and memory outside its stack as
`strMem` says. -/
theorem readString_correct (m : Machine) {base retAddr out self wide max printable : Word}
    (hc : CodeIn m.mem base readStringCode) (hu16 : CodeIn m.mem (base + 0xFFFFC51E) readerU16Code)
    (hu8 : CodeIn m.mem (base + 0xFFFFC422) readerU8Code) (hb : CodeIn m.mem (base + 0xFFFFC4F8) readerBytesCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = self)
    (ha2 : reg m a2 = wide) (ha3 : reg m a3 = max) (ha4 : reg m a4 = printable)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hself : self.toNat % 4 = 0) (hout : out.toNat % 4 = 0)
    (hbuf : memLoad32 m.mem self ≠ 0 ∧
      (memLoad32 m.mem self).toNat + (memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32)
    (hSc : Sep (reg m sp + 0xFFFFFFD0) 48 base readStringCode.length)
    (hSu16 : Sep (reg m sp + 0xFFFFFFD0) 48 (base + 0xFFFFC51E) readerU16Code.length)
    (hSu8 : Sep (reg m sp + 0xFFFFFFD0) 48 (base + 0xFFFFC422) readerU8Code.length)
    (hSb : Sep (reg m sp + 0xFFFFFFD0) 48 (base + 0xFFFFC4F8) readerBytesCode.length)
    (hOc : Sep out 8 base readStringCode.length)
    (hEu16 : Sep (self + 8) 4 (base + 0xFFFFC51E) readerU16Code.length)
    (hEu8 : Sep (self + 8) 4 (base + 0xFFFFC422) readerU8Code.length)
    (hEb : Sep (self + 8) 4 (base + 0xFFFFC4F8) readerBytesCode.length)
    (hEc : Sep (self + 8) 4 base readStringCode.length)
    (hRS : Sep self 12 (reg m sp + 0xFFFFFFD0) 48) (hOS : Sep out 8 (reg m sp + 0xFFFFFFD0) 48)
    (hBS : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (reg m sp + 0xFFFFFFD0) 48)
    (hBE : Sep (memLoad32 m.mem self) (memLoad32 m.mem (self + 4)).toNat (self + 8) 4) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFD0) 48 x 1 → m'.mem x = strMem m.mem out self wide max printable x := by
  obtain ⟨S, hSd⟩ : ∃ S, reg m sp + 0xFFFFFFD0 = S := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFFE0 = G := ⟨_, rfl⟩
  rw [hSd] at hSc hSu16 hSu8 hSb hRS hOS hBS ⊢
  obtain ⟨ptr, hptr⟩ : ∃ ptr, memLoad32 m.mem self = ptr := ⟨_, rfl⟩
  obtain ⟨len, hlen⟩ : ∃ len, memLoad32 m.mem (self + 4) = len := ⟨_, rfl⟩
  rw [hptr, hlen] at hbuf hBS hBE
  have hGS : G = S + BitVec.ofNat 32 16 := by rw [← hGd, ← hSd, BitVec.add_assoc]; rfl
  have hSG : G + 0xFFFFFFF0 = S := by rw [← hGd, ← hSd, BitVec.add_assoc]; rfl
  have hspG : G + 0x20 = reg m sp := by rw [← hGd, BitVec.add_assoc]; exact BitVec.add_zero _
  have hGa : G.toNat % 4 = 0 := hGd ▸ aligned_add hsp (k := 0xFFFFFFE0) (by decide)
  have fr : ∀ c l, c + l ≤ 32 → ∀ (x : Word) (n : Nat), Sep S 48 x n → Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := 16 + c) (l := l) (by omega)
  have s16 : ∀ (x : Word) (n : Nat), Sep S 48 x n → Sep (G + 0xFFFFFFF0) 16 x n := fun x n hx => by
    rw [hSG]; have := hx.sub (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at this
  have s16R : ∀ {a : Word} {n : Nat}, Sep a n S 48 → Sep a n (G + 0xFFFFFFF0) 16 := fun h => by
    rw [hSG]; have := h.subR (c := 0) (l := 16) (by omega); rwa [add_ofNat_zero] at this
  have inG : ∀ c, c < 32 → Sep (G + 0xFFFFFFF0) 16 (G + BitVec.ofNat 32 c) 1 := fun c hc' => by
    rw [hSG, hGS, add_ofNat_assoc]
    have := sep_offsets S (c := 0) (n := 16) (d := 16 + c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc rstr_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFE0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc rstr_at_2 (off' := 4) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x1C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (fr 0x1C 4 (by omega) _ _ hSc)
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 rstr_at_4 (off' := 6) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x18) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (fr 0x18 4 (by omega) _ _ hSc)
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 rstr_at_6 (off' := 8) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x14) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  have hc4 := hc3.store32 (v := reg m 9) (fr 0x14 4 (by omega) _ _ hSc)
  obtain ⟨m5, e5, t5⟩ := t4.sw hc4 rstr_at_8 (off' := 0xA) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x10) (by decide))
  rw [u1sp, f1 18 (by decide)] at t5
  have hc5 := hc4.store32 (v := reg m 18) (fr 0x10 4 (by omega) _ _ hSc)
  obtain ⟨m6, e6, t6⟩ := t5.sw hc5 rstr_at_a (off' := 0xC) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [u1sp, f1 19 (by decide)] at t6
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 m.mem (G + 0x1C) (reg m ra))
      (G + 0x18) (reg m 8)) (G + 0x14) (reg m 9)) (G + 0x10) (reg m 18)) (G + 0xC) (reg m 19) = M5 := ⟨_, rfl⟩
  rw [hM5] at t6
  have M5out : ∀ x, Sep S 48 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5]
    exact (memStore32_get_sep (fr 0xC 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x10 4 (by omega) x 1 hx)).trans
      ((memStore32_get_sep (fr 0x14 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x18 4 (by omega) x 1 hx)).trans
      (memStore32_get_sep (fr 0x1C 4 (by omega) x 1 hx)))))
  have codeOut : ∀ {b : Word} {code : List Nat}, Sep S 48 b code.length → CodeIn m.mem b code → CodeIn M5 b code :=
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
  have us : ∀ (g : Fin 32 → Word) (r : Fin 32) (v : Word), r.val ≠ 0 → upd g r v r = v := fun g r v h => by
    simp only [upd, h, ↓reduceIte]
  have hO4 : Sep out 4 S 48 := by have := hOS.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have hcO : Sep out 4 base readStringCode.length := by
    have := hOc.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have ldO : ∀ (Mx : Word → BitVec 8) (v : Word) (w : BitVec 8) c, 0xC ≤ c → c + 4 ≤ 0x20 →
      memLoad32 (memStore8 (memStore32 Mx out v) (out + 0x4) w) (G + BitVec.ofNat 32 c) =
        memLoad32 Mx (G + BitVec.ofNat 32 c) := fun Mx v w c h1 h2 =>
    (memLoad32_congr fun j hj => memStore8_ne (by
      rw [add_ofNat_assoc, hGS, add_ofNat_assoc]
      exact fun e => hOS 4 (by omega) (16 + (c + j)) (by omega) e.symm)).trans
    (memLoad32_store32_sep (by rw [hGS, add_ofNat_assoc]; exact hO4.subR (c := 16 + c) (l := 4) (by omega)))
  have ldO2 : ∀ (Mx : Word → BitVec 8) (v w : Word) c, 0xC ≤ c → c + 4 ≤ 0x20 →
      memLoad32 (memStore32 (memStore32 Mx out v) (out + 0x4) w) (G + BitVec.ofNat 32 c) =
        memLoad32 Mx (G + BitVec.ofNat 32 c) := fun Mx v w c h1 h2 =>
    (memLoad32_store32_sep (by
      rw [hGS, add_ofNat_assoc]; exact (hOS.sub (c := 4) (l := 4) (by omega)).subR (c := 16 + c) (l := 4) (by omega))).trans
    (memLoad32_store32_sep (by rw [hGS, add_ofNat_assoc]; exact hO4.subR (c := 16 + c) (l := 4) (by omega)))
  have epi : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx base mx 0x9A fx →
      CodeIn Mx base readStringCode → fx sp = G →
      (∀ c, 0xC ≤ c → c + 4 ≤ 0x20 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c)) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
        r ≠ 18 → r ≠ 19 → fx r = reg m r) →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧ m'.mem = Mx := by
    intro Mx mx fx s hcx hs hF hk
    have lA : memLoad32 Mx (G + 0x1C) = reg m ra := (hF 0x1C (by omega) (by omega)).trans fA
    have lB : memLoad32 Mx (G + 0x18) = reg m 8 := (hF 0x18 (by omega) (by omega)).trans fB
    have lC : memLoad32 Mx (G + 0x14) = reg m 9 := (hF 0x14 (by omega) (by omega)).trans fC
    have lD : memLoad32 Mx (G + 0x10) = reg m 18 := (hF 0x10 (by omega) (by omega)).trans fD
    have lE : memLoad32 Mx (G + 0xC) = reg m 19 := (hF 0xC (by omega) (by omega)).trans fE
    obtain ⟨n3, d3, u3⟩ := s.lw hcx rstr_at_9a (off' := 0x9C) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0x1C) (by decide))
    rw [hs, lA] at u3
    obtain ⟨n4, d4, u4⟩ := u3.lw hcx rstr_at_9c (off' := 0x9E) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x18) (by decide))
    rw [show upd fx ra (reg m ra) sp = G by simp +decide only [upd]; exact hs, lB] at u4
    obtain ⟨n5, d5, u5⟩ := u4.lw hcx rstr_at_9e (off' := 0xA0) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x14) (by decide))
    rw [show upd (upd fx ra (reg m ra)) 8 (reg m 8) sp = G by simp +decide only [upd]; exact hs, lC] at u5
    obtain ⟨n6, d6, u6⟩ := u5.lw hcx rstr_at_a0 (off' := 0xA2) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0x10) (by decide))
    rw [show upd (upd (upd fx ra (reg m ra)) 8 (reg m 8)) 9 (reg m 9) sp = G by simp +decide only [upd]; exact hs,
      lD] at u6
    obtain ⟨n7, d7, u7⟩ := u6.lw hcx rstr_at_a2 (off' := 0xA4) (by decide)
      (by simp +decide only [upd]; rw [hs]; exact aligned_add hGa (k := 0xC) (by decide))
    rw [show upd (upd (upd (upd fx ra (reg m ra)) 8 (reg m 8)) 9 (reg m 9)) 18 (reg m 18) sp = G by
      simp +decide only [upd]; exact hs, lE] at u7
    obtain ⟨n8, d8, u8⟩ := u7.aluImm hcx rstr_at_a4 (off' := 0xA6) (by decide)
    obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.jalr hcx rstr_at_a6
    refine ⟨n9, .cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.single d9)))))), ?_, ?_,
      fun r h0 h1 h2 h3 h4 h5 => ?_, by rw [mem9]⟩
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
  have err92 : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx base mx 0x92 fx →
      CodeIn Mx base readStringCode → fx 8 = out → fx sp = G →
      (∀ c, 0xC ≤ c → c + 4 ≤ 0x20 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c)) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
        r ≠ 18 → r ≠ 19 → fx r = reg m r) →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
        m'.mem = memStore8 (memStore32 Mx out 0) (out + 0x4) ((fx a0).extractLsb' 0 8) := by
    intro Mx mx fx s hcx h8 hs hF hk
    have hzx := s.zero
    obtain ⟨n1, d1, u1⟩ := s.sw hcx rstr_at_92 (off' := 0x96) (by decide)
      (by rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out]; exact hout)
    rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out, show fx x0 = 0 from hzx] at u1
    have hc1 := hcx.store32 (v := 0) (a := out) hcO
    obtain ⟨n2, d2, u2⟩ := u1.sb hc1 rstr_at_96 (off' := 0x9A) (by decide)
    rw [h8] at u2
    have hc2 := hc1.store8 (v := (fx a0).extractLsb' 0 8) (a := out + 0x4) (hOc.sub (c := 4) (l := 1) (by omega))
    obtain ⟨m', c', pc', sp', k', mem'⟩ := epi _ _ _ u2 hc2 hs
      (fun c h1 h2 => (ldO Mx 0 _ c h1 h2).trans (hF c h1 h2)) hk
    exact ⟨m', .cons d1 (.cons d2 c'), pc', sp', k', mem'⟩
  have cont : ∀ (mx : Machine) (fx : Fin 32 → Word) (Mc : Word → BitVec 8) (n e : Word),
      Steps m mx → St Mc base mx 0x4A fx → fx a2 = n → fx 8 = out → fx 9 = self → fx 18 = printable →
      fx 19 = max → fx sp = G →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
        r ≠ 18 → r ≠ 19 → fx r = reg m r) →
      (∀ x, Sep S 48 x 1 → Mc x = memStore32 m.mem (self + 8) e x) →
      (∀ c, 0xC ≤ c → c + 4 ≤ 0x20 → memLoad32 Mc (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c)) →
      memLoad32 Mc self = ptr → memLoad32 Mc (self + 4) = len → memLoad32 Mc (self + 8) = e →
      CodeIn Mc base readStringCode → CodeIn Mc (base + 0xFFFFC4F8) readerBytesCode →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
        ∀ x, Sep S 48 x 1 → m'.mem x = strTail m.mem out self e n max printable x := by
    intro mx fx Mc n e pre s hfa2 hf8 hf9 hf18 hf19 hfsp hk hMc hFc hl0 hl4 hl8 hcc hbc
    have hzx := s.zero
    obtain ⟨n1, d1, u1⟩ := s.aluImm hcc rstr_at_4a (off' := 0x4E) (by decide)
    rw [hfa2] at u1
    have q19 : upd fx a0 (aluEval .add n 0xFFFFFFFF) 19 = max := by rw [updz hzx (by decide)]; exact hf19
    by_cases hlt : (n + 0xFFFFFFFF).ult max = true
    · obtain ⟨n2, d2, u2⟩ := u1.notTaken hcc 0x52 rstr_at_4e (by decide)
        (by rw [us _ a0 _ (by decide), q19]; show (!((n + 0xFFFFFFFF).ult max)) = false; rw [hlt]; rfl)
      obtain ⟨n3, d3, u3⟩ := u2.aluImm hcc rstr_at_52 (off' := 0x54) (by decide)
      obtain ⟨n4, d4, u4⟩ := u3.alu hcc rstr_at_54 (off' := 0x56) (by decide)
      obtain ⟨n5, c5, pc5, mem5, regs5⟩ := u4.callRa (cb := base + 0xFFFFC4F8) hcc rstr_at_56 rstr_at_5a
        (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xFFFFC4F8 (by decide))
      have r5 : ∀ r, reg n5 r = upd (upd (upd (upd fx a0 (aluEval .add n 0xFFFFFFFF)) a0
          (aluEval .add (upd fx a0 (aluEval .add n 0xFFFFFFFF) sp) 4)) a1
          (aluEval .add (upd (upd fx a0 (aluEval .add n 0xFFFFFFFF)) a0
            (aluEval .add (upd fx a0 (aluEval .add n 0xFFFFFFFF) sp) 4) x0)
            (upd (upd fx a0 (aluEval .add n 0xFFFFFFFF)) a0
              (aluEval .add (upd fx a0 (aluEval .add n 0xFFFFFFFF) sp) 4) 9))) ra
          (base + BitVec.ofNat 32 (0x56 + 8)) r := regs5
      have g5 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ ra → reg n5 r = fx r := fun r h0 h1 hra' => by
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; rw [r5]; simp [upd, hzx]
        rw [r5]; simp only [upd, hr, h0, h1, hra', ↓reduceIte]
      have p5a0 : reg n5 a0 = G + 4 := by rw [r5]; simp +decide only [upd, ite_true, ite_false]; rw [hfsp]; rfl
      have p5a1 : reg n5 a1 = self := by
        rw [r5]; simp +decide only [upd, ite_true, ite_false]; rw [hf9]; exact BitVec.zero_add self
      have p5a2 : reg n5 a2 = n := (g5 a2 (by decide) (by decide) (by decide)).trans hfa2
      have p5ra : reg n5 ra = base + BitVec.ofNat 32 (0x56 + 8) := by rw [r5]; simp +decide only [upd, ite_true, ite_false]
      obtain ⟨n6, c6, pc6, mem6, fr6⟩ := readerBytes_correct n5 (base + 0xFFFFC4F8) (base + BitVec.ofNat 32 (0x56 + 8))
        (G + 4) self n (by show CodeIn n5.mem _ _; rw [mem5]; exact hbc) pc5 p5a0 p5a1 p5a2 p5ra
        (even_clear _ (even_at base hbase (0x56 + 8) (by decide))) (aligned_add hGa (k := 4) (by decide)) hself
        (fr 4 8 (by omega) _ _ hSb) hEb
      rw [mem5] at mem6
      have hRb : bytesResult (memLoad32 Mc self) (memLoad32 Mc (self + 4)) (memLoad32 Mc (self + 8)) n =
          bytesResult ptr len e n := by rw [hl0, hl4, hl8]
      have k6 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg n6 r = fx r :=
        fun r h0 h1 h2 h3 h4 h5 hra' => (fr6 r h3 h4 h5).trans (g5 r h0 h1 hra')
      have q6 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
          r ≠ 18 → r ≠ 19 → reg n6 r = reg m r := fun r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19 =>
        (k6 r h0 h1 h2 h3 h4 h5 hra').trans (hk r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19)
      have sp6 : reg n6 sp = G := (k6 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfsp
      have s06 : reg n6 8 = out := (k6 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hf8
      have s26 : reg n6 18 = printable :=
        (k6 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hf18
      have frB : ∀ c, 0xC ≤ c → c + 4 ≤ 0x20 → memLoad32 n6.mem (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c) :=
        fun c h1 h2 => by
          rw [mem6, bytesMem_load (show Sep (G + 4) 8 (G + BitVec.ofNat 32 c) 4 from
            sep_offsets G (c := 4) (n := 8) (d := c) (k := 4) (Or.inl (by omega)) (by omega) (by omega))
            (by rw [hGS, add_ofNat_assoc]; exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 16 + c) (l := 4) (by omega))]
          exact hFc c h1 h2
      have outB : ∀ x, Sep S 48 x 1 → Sep (G + 4) 8 x 1 := fun x hx => fr 4 8 (by omega) x 1 hx
      have m6x : ∀ x, Sep S 48 x 1 → n6.mem x =
          match bytesResult ptr len e n with
          | none => memStore32 m.mem (self + 8) e x
          | some (_, e') => memStore32 m.mem (self + 8) e' x := fun x hx => by
        rw [mem6, bytesMem_outside (outB x hx), hRb]
        cases bytesResult ptr len e n with
        | none => exact hMc x hx
        | some pe => exact (memStore32_congr (hMc x hx)).trans (memStore32_overwrite _ _ _ _ _)
      have hc6 : CodeIn n6.mem base readStringCode := fun i hi => by
        rw [mem6, bytesMem_outside (outB _ (hSc.subR (c := i) (l := 1) (by omega))), hRb]
        cases bytesResult ptr len e n with
        | none => exact hcc i hi
        | some pe => exact (memStore32_get_sep (hEc.subR (c := i) (l := 1) (by omega))).trans (hcc i hi)
      have t6 : St n6.mem base n6 0x5E (reg n6) := ⟨by rw [pc6], rfl, fun _ => rfl⟩
      have hz6 := t6.zero
      obtain ⟨n7, d7, u7⟩ := t6.lw hc6 rstr_at_5e (off' := 0x60) (by decide)
        (by rw [sp6]; exact aligned_add hGa (k := 4) (by decide))
      rw [sp6] at u7
      have pre6 : Steps m n6 := pre.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans c6)))))
      rcases hbr : bytesResult ptr len e n with _ | ⟨q, e'⟩
      · obtain ⟨b0, b4⟩ := bytesMem_none (out := G + 4) (hRb.trans hbr)
        rw [← mem6] at b0 b4
        rw [b0] at u7
        obtain ⟨n8, d8, u8⟩ := u7.taken hc6 0x8E rstr_at_60 (by decide)
          (by rw [us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq 0 0 = true))
        obtain ⟨n9, d9, u9⟩ := u8.lbu hc6 rstr_at_8e (off' := 0x92) (by decide)
        rw [updz hz6 (show sp ≠ a0 by decide), sp6, show G + (0x8 : Word) = G + 4 + 4 by rw [BitVec.add_assoc]; rfl, b4] at u9
        obtain ⟨m', c', pc', sp', k', mem'⟩ := err92 _ _ _ u9 hc6
          (by rw [updz u7.zero (by decide), updz hz6 (by decide)]; exact s06)
          (by rw [updz u7.zero (by decide), updz hz6 (by decide)]; exact sp6) frB
          (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => by
            rw [updz u7.zero h0, updz hz6 h0]; exact q6 r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
        refine ⟨m', pre6.trans (.cons d7 (.cons d8 (.cons d9 c'))), pc', sp', k', fun x hx => ?_⟩
        have mx : n6.mem x = memStore32 m.mem (self + 8) e x := by rw [m6x x hx, hbr]
        rw [mem', us _ a0 _ (by decide)]; unfold strTail; simp only [hlt, ↓reduceIte]; rw [hptr, hlen, hbr]
        exact memStore8_congr (memStore32_congr mx)
      · obtain ⟨b0, b4⟩ := bytesMem_some (out := G + 4) (hRb.trans hbr)
        rw [← mem6] at b0 b4
        rw [b0] at u7
        have hn0 : n ≠ 0 := fun h0 => by
          rw [h0] at hlt
          have h1 : (0 + 0xFFFFFFFF : Word).toNat < max.toNat := of_decide_eq_true hlt
          have h2 := max.isLt
          rw [show (0 + 0xFFFFFFFF : Word).toNat = 4294967295 from rfl] at h1
          omega
        have hq0 : q ≠ 0 := bytesResult_ne_zero hbuf.1 hbuf.2 hn0 hbr
        obtain ⟨hq1, hle2⟩ : ptr + e = q ∧ e.toNat + n.toNat ≤ len.toNat := by
          have hb2 := hbr
          rw [bytesResult_eq] at hb2
          split at hb2
          · next h => injection hb2 with h'; injection h' with h1 h2; exact ⟨h1, h⟩
          · cases hb2
        have bufeq : ∀ i, i < n.toNat → n6.mem (q + BitVec.ofNat 32 i) = m.mem (q + BitVec.ofNat 32 i) := fun i hi => by
          have addr : q + BitVec.ofNat 32 i = ptr + BitVec.ofNat 32 (e.toNat + i) := by
            rw [← hq1, ← add_ofNat_assoc, Cur.ofNat_toNat_self]
          have sS : Sep S 48 (q + BitVec.ofNat 32 i) 1 := by
            rw [addr]; exact (hBS.sub (c := e.toNat + i) (l := 1) (by omega)).symm
          have sE : Sep (self + 8) 4 (q + BitVec.ofNat 32 i) 1 := by
            rw [addr]; exact (hBE.sub (c := e.toNat + i) (l := 1) (by omega)).symm
          rw [m6x _ sS, hbr]; exact memStore32_get_sep sE
        obtain ⟨n8, d8, u8⟩ := u7.notTaken hc6 0x62 rstr_at_60 (by decide)
          (by rw [us _ a0 _ (by decide)]; exact beq_eq_false_iff_ne.mpr hq0)
        obtain ⟨n9, d9, u9⟩ := u8.lw hc6 rstr_at_62 (off' := 0x64) (by decide)
          (by rw [updz hz6 (show sp ≠ a0 by decide), sp6]; exact aligned_add hGa (k := 8) (by decide))
        rw [updz hz6 (show sp ≠ a0 by decide), sp6, show G + (0x8 : Word) = G + 4 + 4 by rw [BitVec.add_assoc]; rfl, b4] at u9
        have v9a0 : reg n9 a0 = q := by rw [u9.regs]; simp +decide only [upd, ite_true, ite_false]
        have v9a1 : reg n9 a1 = n := by rw [u9.regs]; simp +decide only [upd, ite_true, ite_false]
        have v98 : reg n9 8 = out := by rw [u9.regs]; simp +decide only [upd, ite_false]; exact s06
        have v918 : reg n9 18 = printable := by rw [u9.regs]; simp +decide only [upd, ite_false]; exact s26
        have v9sp : reg n9 sp = G := by rw [u9.regs]; simp +decide only [upd, ite_false]; exact sp6
        have v9k : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
            r ≠ 18 → r ≠ 19 → reg n9 r = reg m r := fun r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19 => by
          by_cases hr : r.val = 0
          · have : r = 0 := Fin.ext hr
            subst this; rw [u9.self.zero, hz]
          rw [u9.regs]; simp only [upd, hr, h0, h1, ↓reduceIte]
          exact q6 r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19
        have pre9 : Steps m n9 := pre6.trans (.cons d7 (.cons d8 (.single d9)))
        have store88 : ∀ (mx : Machine) (fx : Fin 32 → Word), Steps n9 mx → St n6.mem base mx 0x88 fx →
            fx a0 = q → fx a1 = n → fx 8 = out → fx sp = G →
            (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
              r ≠ 18 → r ≠ 19 → fx r = reg m r) →
            (printable = 0 ∨ ∀ i, i < n.toNat → printableByte (m.mem (q + BitVec.ofNat 32 i))) →
            ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
              (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
              ∀ x, Sep S 48 x 1 → m'.mem x = strTail m.mem out self e n max printable x := by
          intro mx fx c s ha0' ha1' h8 hs hk' hcond
          obtain ⟨o1, f1', w1⟩ := s.sw hc6 rstr_at_88 (off' := 0x8A) (by decide)
            (by rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out]; exact hout)
          rw [h8, show out + (0x0 : Word) = out from BitVec.add_zero out, ha0'] at w1
          have hc1 := hc6.store32 (v := q) (a := out) hcO
          obtain ⟨o2, f2', w2⟩ := w1.sw hc1 rstr_at_8a (off' := 0x8C) (by decide)
            (by rw [h8]; exact aligned_add hout (k := 4) (by decide))
          rw [h8, ha1'] at w2
          have hc2 := hc1.store32 (v := n) (a := out + 0x4) (hOc.sub (c := 4) (l := 4) (by omega))
          obtain ⟨o3, f3', w3⟩ := w2.jump hc2 rstr_at_8c (off' := 0x9A) (by decide)
            (by rw [w2.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x9A (by decide)))
          obtain ⟨m', c', pc', sp', k', mem'⟩ := epi _ _ _ w3 hc2 hs
            (fun c h1 h2 => (ldO2 _ _ _ c h1 h2).trans (frB c h1 h2)) hk'
          refine ⟨m', pre9.trans (c.trans (.cons f1' (.cons f2' (.cons f3' c')))), pc', sp', k', fun x hx => ?_⟩
          have mx' : n6.mem x = memStore32 m.mem (self + 8) e' x := by rw [m6x x hx, hbr]
          rw [mem']; unfold strTail; rw [ite_eq_left hlt, hptr, hlen, hbr]; dsimp only; rw [ite_eq_left hcond]
          exact memStore32_congr (memStore32_congr mx')
        by_cases hpz : printable = 0
        · obtain ⟨n10, d10, u10⟩ := u9.self.taken hc6 0x88 rstr_at_64 (by decide)
            (by rw [v918, hpz, show reg n9 x0 = 0 from u9.self.zero]; decide)
          exact store88 n10 _ (.single d10) u10 v9a0 v9a1 v98 v9sp v9k (Or.inl hpz)
        · obtain ⟨n10, d10, u10⟩ := u9.self.notTaken hc6 0x68 rstr_at_64 (by decide)
            (by rw [v918, show reg n9 x0 = 0 from u9.self.zero]; exact beq_eq_false_iff_ne.mpr hpz)
          obtain ⟨n11, d11, u11⟩ := u10.aluImm hc6 rstr_at_68 (off' := 0x6C) (by decide)
          obtain ⟨n12, d12, u12⟩ := u11.alu hc6 rstr_at_6c (off' := 0x6E) (by decide)
          obtain ⟨n13, d13, u13⟩ := u12.alu hc6 rstr_at_6e (off' := 0x70) (by decide)
          have v13a3 : reg n13 a3 = BitVec.ofNat 32 n.toNat := by
            rw [u13.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v9a1, Cur.ofNat_toNat_self]; exact BitVec.zero_add n
          have v13a4 : reg n13 a4 = q := by
            rw [u13.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v9a0]; exact BitVec.zero_add q
          have v13a2 : reg n13 a2 = 0x5F := by rw [u13.regs]; simp +decide only [upd, ite_true, ite_false]; rfl
          have v13k : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n13 r = reg n9 r := fun r h2 h3 h4 => by
            by_cases hr : r.val = 0
            · have : r = 0 := Fin.ext hr
              subst this; rw [u13.self.zero, u9.self.zero]
            rw [u13.regs]; simp only [upd, hr, h2, h3, h4, ↓reduceIte]
          obtain ⟨mx', cx, kx, h88, h80⟩ := rstr_loop hc6 n.toNat n13 q n.isLt u13.self v13a3 v13a4 v13a2
          have kk : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg mx' r = reg n9 r := fun r h2 h3 h4 h5 =>
            (kx r h3 h4 h5).trans (v13k r h2 h3 h4)
          have pre13 : Steps n9 n13 := .cons d10 (.cons d11 (.cons d12 (.single d13)))
          by_cases hall : ∀ i, i < n.toNat → printableByte (m.mem (q + BitVec.ofNat 32 i))
          · have t88 := h88 fun i hi => by rw [bufeq i hi]; exact hall i hi
            exact store88 mx' _ (pre13.trans cx) t88
              ((kk a0 (by decide) (by decide) (by decide) (by decide)).trans v9a0)
              ((kk a1 (by decide) (by decide) (by decide) (by decide)).trans v9a1)
              ((kk 8 (by decide) (by decide) (by decide) (by decide)).trans v98)
              ((kk sp (by decide) (by decide) (by decide) (by decide)).trans v9sp)
              (fun r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19 => (kk r h2 h3 h4 h5).trans
                (v9k r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19)) (Or.inr hall)
          · have t80 := h80 fun h => hall fun i hi => by rw [← bufeq i hi]; exact h i hi
            obtain ⟨o1, f1', w1⟩ := t80.aluImm hc6 rstr_at_80 (off' := 0x82) (by decide)
            obtain ⟨o2, f2', w2⟩ := w1.jump hc6 rstr_at_82 (off' := 0x92) (by decide)
              (by rw [w1.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x92 (by decide)))
            have z80 := t80.zero
            obtain ⟨m', c', pc', sp', k', mem'⟩ := err92 _ _ _ w2 hc6
              (by rw [updz z80 (by decide), kk 8 (by decide) (by decide) (by decide) (by decide)]; exact v98)
              (by rw [updz z80 (by decide), kk sp (by decide) (by decide) (by decide) (by decide)]; exact v9sp) frB
              (fun r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19 => by
                rw [updz z80 h0, kk r h2 h3 h4 h5]; exact v9k r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19)
            refine ⟨m', pre9.trans (pre13.trans (cx.trans (.cons f1' (.cons f2' c')))), pc', sp', k', fun x hx => ?_⟩
            have mx' : n6.mem x = memStore32 m.mem (self + 8) e' x := by rw [m6x x hx, hbr]
            have hn : ¬ (printable = 0 ∨ ∀ i, i < n.toNat → printableByte (m.mem (q + BitVec.ofNat 32 i))) := by
              rintro (h | h)
              · exact hpz h
              · exact hall h
            rw [mem', us _ a0 _ (by decide)]; unfold strTail; rw [ite_eq_left hlt, hptr, hlen, hbr]; dsimp only
            rw [ite_eq_right hn]
            exact memStore8_congr (memStore32_congr mx')
    · have hf : (n + 0xFFFFFFFF).ult max = false := by
        cases h : (n + 0xFFFFFFFF).ult max
        · rfl
        · exact absurd h hlt
      obtain ⟨n2, d2, u2⟩ := u1.taken hcc 0x84 rstr_at_4e (by decide)
        (by rw [us _ a0 _ (by decide), q19]; show (!((n + 0xFFFFFFFF).ult max)) = true; rw [hf]; rfl)
      obtain ⟨n3, d3, u3⟩ := u2.aluImm hcc rstr_at_84 (off' := 0x86) (by decide)
      obtain ⟨n4, d4, u4⟩ := u3.jump hcc rstr_at_86 (off' := 0x92) (by decide)
        (by rw [u3.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x92 (by decide)))
      obtain ⟨m', c', pc', sp', k', mem'⟩ := err92 _ _ _ u4 hcc
        (by rw [updz u1.zero (by decide), updz hzx (by decide)]; exact hf8)
        (by rw [updz u1.zero (by decide), updz hzx (by decide)]; exact hfsp) hFc
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => by
          rw [updz u1.zero h0, updz hzx h0]; exact hk r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
      refine ⟨m', pre.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 c')))), pc', sp', k', fun x hx => ?_⟩
      rw [mem', us _ a0 _ (by decide)]; unfold strTail; rw [ite_eq_right hlt]
      exact memStore8_congr (memStore32_congr (hMc x hx))
  obtain ⟨m7, e7, t7⟩ := t6.alu hc6 rstr_at_c (off' := 0xE) (by decide)
  obtain ⟨m8, e8, t8⟩ := t7.alu hc6 rstr_at_e (off' := 0x10) (by decide)
  obtain ⟨m9, e9, t9⟩ := t8.alu hc6 rstr_at_10 (off' := 0x12) (by decide)
  obtain ⟨m10, e10, t10⟩ := t9.alu hc6 rstr_at_12 (off' := 0x14) (by decide)
  obtain ⟨m11, e11, t11⟩ := t10.alu hc6 rstr_at_14 (off' := 0x16) (by decide)
  have v11a0 : reg m11 a0 = self := by rw [t11.regs]; simp +decide [upd, aluEval, ha1]
  have v11a2 : reg m11 a2 = wide := by rw [t11.regs]; simp +decide [upd, ha2]
  have v118 : reg m11 8 = out := by rw [t11.regs]; simp +decide [upd, aluEval, ha0]
  have v119 : reg m11 9 = self := by rw [t11.regs]; simp +decide [upd, aluEval, ha1]
  have v1118 : reg m11 18 = printable := by rw [t11.regs]; simp +decide [upd, aluEval, ha4]
  have v1119 : reg m11 19 = max := by rw [t11.regs]; simp +decide [upd, aluEval, ha3]
  have v11sp : reg m11 sp = G := by rw [t11.regs]; simp +decide [upd]
  have v11k : ∀ r, r ≠ a0 → r ≠ sp → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → reg m11 r = reg m r :=
    fun r h0 h1 h2 h3 h4 h5 => by
      rw [t11.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1, h2, h3, h4, h5]
  have u11 := t11.self
  have pre11 : Steps m m11 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9
    (.cons e10 (.single e11))))))))))
  have selfS : ∀ j, j < 12 → Sep S 48 (self + BitVec.ofNat 32 j) 1 := fun j hj => (hRS.sub (c := j) (l := 1) hj).symm
  have frameE : ∀ c, 0xC ≤ c → c + 1 ≤ 0x20 → Sep (self + 8) 4 (G + BitVec.ofNat 32 c) 1 := fun c h1 h2 => by
    rw [hGS, add_ofNat_assoc]; exact (hRS.sub (c := 8) (l := 4) (by omega)).subR (c := 16 + c) (l := 1) (by omega)
  have mcFacts : ∀ (Mc : Word → BitVec 8) (e : Word), (∀ x, Sep S 48 x 1 → Mc x = memStore32 m.mem (self + 8) e x) →
      memLoad32 Mc self = ptr ∧ memLoad32 Mc (self + 4) = len ∧ memLoad32 Mc (self + 8) = e := fun Mc e h => by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hptr]; refine memLoad32_congr fun j hj => ?_
      rw [h _ (selfS j (by omega))]
      exact memStore32_get_sep (sep_offsets self (c := 8) (n := 4) (d := j) (k := 1) (Or.inr (by omega)) (by omega) (by omega))
    · rw [← hlen]; refine memLoad32_congr fun j hj => ?_
      rw [show self + 4 + BitVec.ofNat 32 j = self + BitVec.ofNat 32 (4 + j) by
        rw [show (self + 4 : Word) = self + BitVec.ofNat 32 4 from rfl, add_ofNat_assoc], h _ (selfS (4 + j) (by omega))]
      exact memStore32_get_sep (sep_offsets self (c := 8) (n := 4) (d := 4 + j) (k := 1) (Or.inr (by omega)) (by omega) (by omega))
    · rw [show memLoad32 Mc (self + 8) = memLoad32 (memStore32 m.mem (self + 8) e) (self + 8) from
        memLoad32_congr fun j hj => by
          rw [show self + 8 + BitVec.ofNat 32 j = self + BitVec.ofNat 32 (8 + j) by
            rw [show (self + 8 : Word) = self + BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]]
          exact h _ (selfS (8 + j) (by omega))]
      exact memLoad32_store32_same _ _ _
  have hb8 : base + 0xFFFFC422 + 0xD6 = base + 0xFFFFC4F8 := by rw [BitVec.add_assoc]; rfl
  have hb16 : base + 0xFFFFC51E + 0xFFFFFFDA = base + 0xFFFFC4F8 := by rw [BitVec.add_assoc]; rfl
  by_cases hw : wide = 0
  · obtain ⟨m12, e12, t12⟩ := u11.taken hc6 0x2A rstr_at_16 (by decide)
      (by rw [v11a2, hw, show reg m11 x0 = 0 from u11.zero]; decide)
    obtain ⟨m13, c13, pc13, mem13, regs13⟩ := t12.callRa (cb := base + 0xFFFFC422) hc6 rstr_at_2a rstr_at_2e
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xFFFFC422 (by decide))
    have g13 : ∀ r, r ≠ ra → reg m13 r = reg m11 r := fun r h => by
      rw [regs13]; by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, u11.zero]
      · simp [upd, hr, h]
    obtain ⟨m14, c14, pc14, sp14, a014, a114, k14, mem14⟩ := readerU8_correct m13 (base + 0xFFFFC422)
      (base + BitVec.ofNat 32 (0x2A + 8)) self (by show CodeIn m13.mem _ _; rw [mem13]; exact codeOut hSu8 hu8)
      (by show CodeIn m13.mem _ _; rw [mem13, hb8]; exact codeOut hSb hb) (even_at base hbase 0xFFFFC422 (by decide))
      pc13 (by rw [g13 a0 (by decide)]; exact v11a0) (by rw [regs13]; simp +decide [upd])
      (even_clear _ (even_at base hbase (0x2A + 8) (by decide))) (by rw [g13 sp (by decide), v11sp]; exact hGa) hself
      (by rw [mem13, l0, l4]; exact hbuf) (by rw [g13 sp (by decide), v11sp]; exact s16 _ _ hSu8)
      (by rw [g13 sp (by decide), v11sp, hb8]; exact s16 _ _ hSb) hEu8 (by rw [hb8]; exact hEb)
      (by rw [g13 sp (by decide), v11sp]; exact s16R hRS) (by rw [mem13, l0, l4, g13 sp (by decide), v11sp]; exact s16R hBS)
      (by rw [mem13, l0, l4]; exact hBE)
    rw [g13 sp (by decide), v11sp, mem13] at mem14
    rw [g13 sp (by decide), v11sp] at sp14
    rw [mem13] at a014 a114
    have hR8 : bytesResult (memLoad32 M5 self) (memLoad32 M5 (self + 4)) (memLoad32 M5 (self + 8)) 1 =
        bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 := by rw [l0, l4, l8]
    have k14' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
        r ≠ 18 → r ≠ 19 → reg m14 r = reg m r := fun r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19 =>
      (k14 r h0 h1 h2 h3 h4 h5).trans ((g13 r hra').trans (v11k r h0 hsp' h8 h9 h18 h19))
    have kv : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m14 r = reg m11 r :=
      fun r h0 h1 h2 h3 h4 h5 hra' => (k14 r h0 h1 h2 h3 h4 h5).trans (g13 r hra')
    have s014 : reg m14 8 = out := (kv 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v118
    have s114 : reg m14 9 = self := (kv 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v119
    have s214 : reg m14 18 = printable :=
      (kv 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v1118
    have s314 : reg m14 19 = max :=
      (kv 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v1119
    have m14x : ∀ x, Sep S 48 x 1 → m14.mem x =
        match bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 with
        | none => m.mem x
        | some (_, e) => memStore32 m.mem (self + 8) e x := fun x hx => by
      rw [mem14 x (s16 _ _ hx)]; unfold reservedMem; rw [hR8]
      cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 with
      | none => exact M5out x hx
      | some pe => exact memStore32_congr (M5out x hx)
    have fr14 : ∀ c, 0xC ≤ c → c + 4 ≤ 0x20 → memLoad32 m14.mem (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, mem14 _ (inG (c + j) (by omega))]; unfold reservedMem
        cases bytesResult (memLoad32 M5 self) (memLoad32 M5 (self + 4)) (memLoad32 M5 (self + 8)) 1 with
        | none => rfl
        | some pe => exact memStore32_get_sep (frameE (c + j) (by omega) (by omega))
    have code14 : ∀ {b : Word} {code : List Nat}, Sep S 48 b code.length → Sep (self + 8) 4 b code.length →
        CodeIn m.mem b code → CodeIn m14.mem b code := fun h1 h2 hc' i hi => by
      rw [m14x _ (h1.subR (c := i) (l := 1) (by omega))]
      cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 with
      | none => exact hc' i hi
      | some pe => exact (memStore32_get_sep (h2.subR (c := i) (l := 1) (by omega))).trans (hc' i hi)
    have hc14 := code14 hSc hEc hc
    have t14 : St m14.mem base m14 0x32 (reg m14) := ⟨by rw [pc14], rfl, fun _ => rfl⟩
    have hz14 := t14.zero
    obtain ⟨n15, d15, u15⟩ := t14.aluImm hc14 rstr_at_32 (off' := 0x34) (by decide)
    have pre14 : Steps m m14 := pre11.trans (.cons e12 (c13.trans c14))
    rcases hbr : bytesResult ptr len (memLoad32 m.mem (self + 8)) 1 with _ | ⟨p, e⟩
    · have ha0' : reg m14 a0 = 1 := by rw [a014]; unfold u8Result; rw [hR8, hbr]
      have ha1' : reg m14 a1 = 0 := by rw [a114]; unfold u8Result; rw [hR8, hbr]
      obtain ⟨n16, d16, u16⟩ := u15.notTaken hc14 0x36 rstr_at_34 (by decide)
        (by rw [ha0', us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq (aluEval .and 1 1) 0 = false))
      obtain ⟨n17, d17, u17⟩ := u16.sw hc14 rstr_at_36 (off' := 0x3A) (by decide)
        (by rw [updz hz14 (show (8 : Fin 32) ≠ a0 by decide), s014, show out + (0x0 : Word) = out from BitVec.add_zero out]
            exact hout)
      rw [updz hz14 (show (8 : Fin 32) ≠ a0 by decide), s014, show out + (0x0 : Word) = out from BitVec.add_zero out,
        upd_x0] at u17
      have hc17 := hc14.store32 (v := 0) (a := out) hcO
      obtain ⟨n18, d18, u18⟩ := u17.sb hc17 rstr_at_3a (off' := 0x3E) (by decide)
      rw [updz hz14 (show (8 : Fin 32) ≠ a0 by decide), s014, updz hz14 (show a1 ≠ a0 by decide), ha1'] at u18
      have hc18 := hc17.store8 (v := (0 : Word).extractLsb' 0 8) (a := out + 0x4) (hOc.sub (c := 4) (l := 1) (by omega))
      obtain ⟨n19, d19, u19⟩ := u18.jump hc18 rstr_at_3e (off' := 0x9A) (by decide)
        (by rw [u18.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x9A (by decide)))
      obtain ⟨m', c', pc', sp', k', mem'⟩ := epi _ _ _ u19 hc18 (by rw [updz hz14 (by decide)]; exact sp14)
        (fun c h1 h2 => (ldO _ _ _ c h1 h2).trans (fr14 c h1 h2))
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => by
          rw [updz hz14 h0]; exact k14' r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
      refine ⟨m', pre14.trans (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 c'))))), pc', sp', k', fun x hx => ?_⟩
      have mx : m14.mem x = m.mem x := by rw [m14x x hx, hbr]
      rw [mem']; unfold strMem strCount; rw [ite_eq_left hw, hptr, hlen, hbr]
      exact memStore8_congr (memStore32_congr mx)
    · obtain ⟨hp1, hle⟩ : ptr + memLoad32 m.mem (self + 8) = p ∧ (memLoad32 m.mem (self + 8)).toNat + 1 ≤ len.toNat := by
        have hb2 := hbr
        rw [bytesResult_eq] at hb2
        split at hb2
        · next h => injection hb2 with h'; injection h' with h1 h2; exact ⟨h1, h⟩
        · cases hb2
      have hM5p : M5 p = m.mem p := by
        have := M5out (ptr + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + 0))
          (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + 0) (l := 1) (by omega)).symm
        rwa [Nat.add_zero, Cur.ofNat_toNat_self, hp1] at this
      have ha0' : reg m14 a0 = 0 := by rw [a014]; unfold u8Result; rw [hR8, hbr]
      have ha1' : reg m14 a1 = (m.mem p).zeroExtend 32 := by
        rw [a114]; unfold u8Result; rw [hR8, hbr]; show (M5 p).zeroExtend 32 = _; rw [hM5p]
      obtain ⟨n16, d16, u16⟩ := u15.taken hc14 0x46 rstr_at_34 (by decide)
        (by rw [ha0', us _ a0 _ (by decide)]; exact (by decide : branchTaken .beq (aluEval .and 0 1) 0 = true))
      obtain ⟨n17, d17, u17⟩ := u16.aluImm hc14 rstr_at_46 (off' := 0x4A) (by decide)
      rw [updz hz14 (show a1 ≠ a0 by decide), ha1', zext_and_ff] at u17
      have mce : ∀ x, Sep S 48 x 1 → m14.mem x = memStore32 m.mem (self + 8) e x := fun x hx => by rw [m14x x hx, hbr]
      obtain ⟨q0, q4, q8⟩ := mcFacts m14.mem e mce
      obtain ⟨m', c', pc', sp', k', mem'⟩ := cont n17 _ m14.mem ((m.mem p).zeroExtend 32) e
        (pre14.trans (.cons d15 (.cons d16 (.single d17)))) u17 (us _ a2 _ (by decide))
        (by rw [updz u16.zero (by decide), updz hz14 (by decide)]; exact s014)
        (by rw [updz u16.zero (by decide), updz hz14 (by decide)]; exact s114)
        (by rw [updz u16.zero (by decide), updz hz14 (by decide)]; exact s214)
        (by rw [updz u16.zero (by decide), updz hz14 (by decide)]; exact s314)
        (by rw [updz u16.zero (by decide), updz hz14 (by decide)]; exact sp14)
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => by
          rw [updz u16.zero h2, updz hz14 h0]; exact k14' r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
        mce fr14 q0 q4 q8 hc14 (code14 hSb hEb hb)
      refine ⟨m', c', pc', sp', k', fun x hx => ?_⟩
      rw [mem' x hx]; unfold strMem strCount; rw [ite_eq_left hw, hptr, hlen, hbr]
  · obtain ⟨m12, e12, t12⟩ := u11.notTaken hc6 0x18 rstr_at_16 (by decide)
      (by rw [v11a2, show reg m11 x0 = 0 from u11.zero]; exact beq_eq_false_iff_ne.mpr hw)
    obtain ⟨m13, c13, pc13, mem13, regs13⟩ := t12.callRa (cb := base + 0xFFFFC51E) hc6 rstr_at_18 rstr_at_1c
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xFFFFC51E (by decide))
    have g13 : ∀ r, r ≠ ra → reg m13 r = reg m11 r := fun r h => by
      rw [regs13]; by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, u11.zero]
      · simp [upd, hr, h]
    obtain ⟨m14, c14, pc14, sp14, a014, k14, mem14⟩ := readerU16_correct m13 (base + 0xFFFFC51E)
      (base + BitVec.ofNat 32 (0x18 + 8)) self (by show CodeIn m13.mem _ _; rw [mem13]; exact codeOut hSu16 hu16)
      (by show CodeIn m13.mem _ _; rw [mem13, hb16]; exact codeOut hSb hb) (even_at base hbase 0xFFFFC51E (by decide))
      pc13 (by rw [g13 a0 (by decide)]; exact v11a0) (by rw [regs13]; simp +decide [upd])
      (even_clear _ (even_at base hbase (0x18 + 8) (by decide))) (by rw [g13 sp (by decide), v11sp]; exact hGa) hself
      (by rw [mem13, l0, l4]; exact hbuf) (by rw [g13 sp (by decide), v11sp]; exact s16 _ _ hSu16)
      (by rw [g13 sp (by decide), v11sp, hb16]; exact s16 _ _ hSb) hEu16 (by rw [hb16]; exact hEb)
      (by rw [g13 sp (by decide), v11sp]; exact s16R hRS) (by rw [mem13, l0, l4, g13 sp (by decide), v11sp]; exact s16R hBS)
      (by rw [mem13, l0, l4]; exact hBE)
    rw [g13 sp (by decide), v11sp, mem13] at mem14
    rw [g13 sp (by decide), v11sp] at sp14
    rw [mem13] at a014
    have hR16 : bytesResult (memLoad32 M5 self) (memLoad32 M5 (self + 4)) (memLoad32 M5 (self + 8)) 2 =
        bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 := by rw [l0, l4, l8]
    have k14' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → r ≠ sp → r ≠ 8 → r ≠ 9 →
        r ≠ 18 → r ≠ 19 → reg m14 r = reg m r := fun r h0 h1 h2 h3 h4 h5 hra' hsp' h8 h9 h18 h19 =>
      (k14 r h0 h1 h2 h3 h4 h5).trans ((g13 r hra').trans (v11k r h0 hsp' h8 h9 h18 h19))
    have kv : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m14 r = reg m11 r :=
      fun r h0 h1 h2 h3 h4 h5 hra' => (k14 r h0 h1 h2 h3 h4 h5).trans (g13 r hra')
    have s014 : reg m14 8 = out := (kv 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v118
    have s114 : reg m14 9 = self := (kv 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v119
    have s214 : reg m14 18 = printable :=
      (kv 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v1118
    have s314 : reg m14 19 = max :=
      (kv 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v1119
    have m14x : ∀ x, Sep S 48 x 1 → m14.mem x =
        match bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 with
        | none => m.mem x
        | some (_, e) => memStore32 m.mem (self + 8) e x := fun x hx => by
      rw [mem14 x (s16 _ _ hx)]; unfold u16Mem; rw [hR16]
      cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 with
      | none => exact M5out x hx
      | some pe => exact memStore32_congr (M5out x hx)
    have fr14 : ∀ c, 0xC ≤ c → c + 4 ≤ 0x20 → memLoad32 m14.mem (G + BitVec.ofNat 32 c) = memLoad32 M5 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, mem14 _ (inG (c + j) (by omega))]; unfold u16Mem
        cases bytesResult (memLoad32 M5 self) (memLoad32 M5 (self + 4)) (memLoad32 M5 (self + 8)) 2 with
        | none => rfl
        | some pe => exact memStore32_get_sep (frameE (c + j) (by omega) (by omega))
    have code14 : ∀ {b : Word} {code : List Nat}, Sep S 48 b code.length → Sep (self + 8) 4 b code.length →
        CodeIn m.mem b code → CodeIn m14.mem b code := fun h1 h2 hc' i hi => by
      rw [m14x _ (h1.subR (c := i) (l := 1) (by omega))]
      cases bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 with
      | none => exact hc' i hi
      | some pe => exact (memStore32_get_sep (h2.subR (c := i) (l := 1) (by omega))).trans (hc' i hi)
    have hc14 := code14 hSc hEc hc
    have t14 : St m14.mem base m14 0x20 (reg m14) := ⟨by rw [pc14], rfl, fun _ => rfl⟩
    have hz14 := t14.zero
    obtain ⟨n15, d15, u15⟩ := t14.aluImm hc14 rstr_at_20 (off' := 0x24) (by decide)
    have pre14 : Steps m m14 := pre11.trans (.cons e12 (c13.trans c14))
    rcases hbr : bytesResult ptr len (memLoad32 m.mem (self + 8)) 2 with _ | ⟨p, e⟩
    · have ha0' : reg m14 a0 = 1 := by rw [a014]; unfold u16Result; rw [hR16, hbr]
      obtain ⟨n16, d16, u16⟩ := u15.notTaken hc14 0x26 rstr_at_24 (by decide)
        (by rw [ha0', us _ a1 _ (by decide)]; exact (by decide : branchTaken .beq (aluEval .and 1 1) 0 = false))
      obtain ⟨n17, d17, u17⟩ := u16.aluImm hc14 rstr_at_26 (off' := 0x28) (by decide)
      obtain ⟨n18, d18, u18⟩ := u17.jump hc14 rstr_at_28 (off' := 0x92) (by decide)
        (by rw [u17.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x92 (by decide)))
      obtain ⟨m', c', pc', sp', k', mem'⟩ := err92 _ _ _ u18 hc14
        (by rw [updz u15.zero (by decide), updz hz14 (by decide)]; exact s014)
        (by rw [updz u15.zero (by decide), updz hz14 (by decide)]; exact sp14) fr14
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => by
          rw [updz u15.zero h0, updz hz14 h1]; exact k14' r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
      refine ⟨m', pre14.trans (.cons d15 (.cons d16 (.cons d17 (.cons d18 c')))), pc', sp', k', fun x hx => ?_⟩
      have mx : m14.mem x = m.mem x := by rw [m14x x hx, hbr]
      rw [mem', us _ a0 _ (by decide), updz hz14 (show a0 ≠ a1 by decide), ha0']
      unfold strMem strCount; rw [ite_eq_right hw, hptr, hlen, hbr]
      exact memStore8_congr (memStore32_congr mx)
    · obtain ⟨hp1, hle⟩ : ptr + memLoad32 m.mem (self + 8) = p ∧ (memLoad32 m.mem (self + 8)).toNat + 2 ≤ len.toNat := by
        have hb2 := hbr
        rw [bytesResult_eq] at hb2
        split at hb2
        · next h => injection hb2 with h'; injection h' with h1 h2; exact ⟨h1, h⟩
        · cases hb2
      have hM5 : ∀ j, j < 2 → M5 (p + BitVec.ofNat 32 j) = m.mem (p + BitVec.ofNat 32 j) := fun j hj => by
        have := M5out (ptr + BitVec.ofNat 32 ((memLoad32 m.mem (self + 8)).toNat + j))
          (hBS.sub (c := (memLoad32 m.mem (self + 8)).toNat + j) (l := 1) (by omega)).symm
        rwa [← add_ofNat_assoc, Cur.ofNat_toNat_self, hp1] at this
      have hM50 : M5 p = m.mem p := by have := hM5 0 (by omega); rwa [add_ofNat_zero] at this
      have hM51 : M5 (p + 1) = m.mem (p + 1) := hM5 1 (by omega)
      have ha0' : reg m14 a0 = (m.mem (p + 1)).zeroExtend 32 <<< 24 ||| (m.mem p).zeroExtend 32 <<< 16 := by
        rw [a014]; unfold u16Result; rw [hR16, hbr]; dsimp only; rw [hM50, hM51]
      obtain ⟨n16, d16, u16⟩ := u15.taken hc14 0x40 rstr_at_24 (by decide)
        (by rw [ha0', us _ a1 _ (by decide), u16_tag]; exact bt_beq_self _)
      obtain ⟨n17, d17, u17⟩ := u16.aluImm hc14 rstr_at_40 (off' := 0x44) (by decide)
      rw [updz hz14 (show a0 ≠ a1 by decide), ha0', u16_shift] at u17
      obtain ⟨n18, d18, u18⟩ := u17.jump hc14 rstr_at_44 (off' := 0x4A) (by decide)
        (by rw [u17.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x4A (by decide)))
      have mce : ∀ x, Sep S 48 x 1 → m14.mem x = memStore32 m.mem (self + 8) e x := fun x hx => by rw [m14x x hx, hbr]
      obtain ⟨q0, q4, q8⟩ := mcFacts m14.mem e mce
      obtain ⟨m', c', pc', sp', k', mem'⟩ := cont n18 _ m14.mem
        ((m.mem (p + 1)).zeroExtend 32 <<< 8 ||| (m.mem p).zeroExtend 32) e
        (pre14.trans (.cons d15 (.cons d16 (.cons d17 (.single d18))))) u18 (us _ a2 _ (by decide))
        (by rw [updz (upd_x0 _ _ _) (by decide), updz hz14 (by decide)]; exact s014)
        (by rw [updz (upd_x0 _ _ _) (by decide), updz hz14 (by decide)]; exact s114)
        (by rw [updz (upd_x0 _ _ _) (by decide), updz hz14 (by decide)]; exact s214)
        (by rw [updz (upd_x0 _ _ _) (by decide), updz hz14 (by decide)]; exact s314)
        (by rw [updz (upd_x0 _ _ _) (by decide), updz hz14 (by decide)]; exact sp14)
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19 => by
          rw [updz (upd_x0 _ _ _) h2, updz hz14 h1]; exact k14' r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 h19)
        mce fr14 q0 q4 q8 hc14 (code14 hSb hEb hb)
      refine ⟨m', c', pc', sp', k', fun x hx => ?_⟩
      rw [mem' x hx]; unfold strMem strCount; rw [ite_eq_right hw, hptr, hlen, hbr]

end C3.RV32


