import C3BootProofs.Proofs.TimeDigits4
import C3BootProofs.Proofs.MagicCur
import C3BootProofs.Proofs.PartCur
import C3BootProofs.Proofs.UintSelect12
import C3BootProofs.Proofs.FieldSubInner

/-!
# `c3_verify::manifest::parse`, as compiled

The current image's `parse` reads the 32-byte version 2 manifest. It builds
a `Reader` over the bytes at `a1` on its stack, calls `Reader::magic`,
`Reader::u16`, `Reader::reserved`, and `manifest::part` three times, and
then checks the layout. It returns `Result<Manifest, Error>` through `a0`:
a tag byte (0 for `Ok`, 1 for `Err`), the error byte at offset 1, and the
three parts' offsets and lengths from offset 4.

`parseErrV2` is what the compiled checks decide, in the code's own word
arithmetic, and `parseMemV2` is the memory they leave.
`manifestParse_correct` proves the function computes them, each call
through the callee's theorem. The code sits at its absolute address, above
`0x40000000`, and the stack, manifest, and result sit below it.
-/

namespace C3.RV32.Cur

open C3.RV32 C3.Image

/-- Where the image puts `parse`. -/
abbrev MP : Word := BitVec.ofNat 32 manifestParseAddress

/-- The functions `parse` runs, where the image puts them. -/
structure MPCode (M : Word → BitVec 8) : Prop where
  parse : CodeIn M MP manifestParseCode
  magic : CodeIn M (BitVec.ofNat 32 readerMagicAddress) readerMagicCode
  array4 : CodeIn M (BitVec.ofNat 32 readerArray4Address) readerArray4Code
  bytes : CodeIn M (BitVec.ofNat 32 readerBytesAddress) readerBytesCode
  u16 : CodeIn M (BitVec.ofNat 32 readerU16Address) readerU16Code
  reserved : CodeIn M (BitVec.ofNat 32 readerReservedAddress) readerReservedCode
  part : CodeIn M (BitVec.ofNat 32 manifestPartAddress) manifestPartCode
  u32 : CodeIn M (BitVec.ofNat 32 readerU32Address) readerU32Code

/-- The error the compiled `parse` returns for the 32 bytes at `bp`, or
`none` when it accepts them. -/
def parseErrV2 (M : Word → BitVec 8) (bp : Word) : Option (BitVec 8) :=
  if !(mw M bp 0 == 0x4C533343) then some 2
  else if !(((M (bp + BitVec.ofNat 32 5)).zeroExtend 32 <<< 24 |||
      (M (bp + BitVec.ofNat 32 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 2) then some 3
  else if !(allZero M (bp + BitVec.ofNat 32 6) 2) then some 4
  else if partOut 37 0x1D0000 (mw M bp 12) then some 5
  else if partOut 49 0x4000 (mw M bp 20) then some 5
  else if partOut 18 0x60000 (mw M bp 28) then some 5
  else if !(mw M bp 8 == 0x10000) then some 7
  else if (0xFFFEFFFF : Word).ult (mw M bp 12) then some 6
  else if (mw M bp 20 + mw M bp 16).ult (mw M bp 20) then some 6
  else if (mw M bp 28 + mw M bp 24).ult (mw M bp 28) then some 6
  else if (mw M bp 16).ult (0x10000 + mw M bp 12) then some 7
  else if (mw M bp 24).ult (mw M bp 20 + mw M bp 16) then some 7
  else if (0x1E0000 : Word).ult (mw M bp 28 + mw M bp 24) then some 7
  else none

/-- Memory after `parse` returns, outside the stack it uses. -/
def parseMemV2 (M : Word → BitVec 8) (out bp : Word) : Word → BitVec 8 :=
  match parseErrV2 M bp with
  | some e => memStore8 (memStore8 M (out + 1) e) out 1
  | none =>
    memStore8 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
      (out + 4) 0x10000) (out + 8) (mw M bp 12)) (out + 0x0C) (mw M bp 16))
      (out + 0x10) (mw M bp 20)) (out + 0x14) (mw M bp 24)) (out + 0x18) (mw M bp 28)) out 0

section
set_option maxRecDepth 20000
theorem mp_0 : fetchRel manifestParseCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem mp_24 : fetchRel manifestParseCode 0x24 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem mp_28 : fetchRel manifestParseCode 0x28 = some (.jalr ra ra 0xFFFFFE56, 4) := by decide
theorem mp_2c : fetchRel manifestParseCode 0x2C = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem mp_30 : fetchRel manifestParseCode 0x30 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem mp_34 : fetchRel manifestParseCode 0x34 = some (.branch .bne a1 x0 0x8E, 2) := by decide
theorem mp_36 : fetchRel manifestParseCode 0x36 = some (.alu .add a0 x0 sp, 2) := by decide
theorem mp_38 : fetchRel manifestParseCode 0x38 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem mp_3c : fetchRel manifestParseCode 0x3C = some (.jalr ra ra 0xFFFFFD42, 4) := by decide
theorem mp_40 : fetchRel manifestParseCode 0x40 = some (.aluImm .and a1 a0 0x1, 4) := by decide
theorem mp_44 : fetchRel manifestParseCode 0x44 = some (.branch .beq a1 x0 0x6, 2) := by decide
theorem mp_4a : fetchRel manifestParseCode 0x4A = some (.aluImm .srl a0 a0 0x10, 2) := by decide
theorem mp_4c : fetchRel manifestParseCode 0x4C = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem mp_4e : fetchRel manifestParseCode 0x4E = some (.branch .bne a0 a1 0x72, 4) := by decide
theorem mp_56 : fetchRel manifestParseCode 0x56 = some (.auipc ra 0x0, 4) := by decide
theorem mp_5a : fetchRel manifestParseCode 0x5A = some (.jalr ra ra 0xFFFFFD34, 4) := by decide
theorem mp_5e : fetchRel manifestParseCode 0x5E = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem mp_62 : fetchRel manifestParseCode 0x62 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem mp_66 : fetchRel manifestParseCode 0x66 = some (.branch .bne a1 x0 0x5C, 2) := by decide
theorem mp_74 : fetchRel manifestParseCode 0x74 = some (.auipc ra 0x0, 4) := by decide
theorem mp_78 : fetchRel manifestParseCode 0x78 = some (.jalr ra ra 0xCA, 4) := by decide
theorem mp_7c : fetchRel manifestParseCode 0x7C = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem mp_80 : fetchRel manifestParseCode 0x80 = some (.branch .bne a0 x0 0x3A, 2) := by decide
theorem mp_90 : fetchRel manifestParseCode 0x90 = some (.auipc ra 0x0, 4) := by decide
theorem mp_94 : fetchRel manifestParseCode 0x94 = some (.jalr ra ra 0xAE, 4) := by decide
theorem mp_98 : fetchRel manifestParseCode 0x98 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem mp_9c : fetchRel manifestParseCode 0x9C = some (.branch .bne a0 x0 0x1E, 2) := by decide
theorem mp_ac : fetchRel manifestParseCode 0xAC = some (.auipc ra 0x0, 4) := by decide
theorem mp_b0 : fetchRel manifestParseCode 0xB0 = some (.jalr ra ra 0x92, 4) := by decide
theorem mp_b4 : fetchRel manifestParseCode 0xB4 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem mp_b8 : fetchRel manifestParseCode 0xB8 = some (.branch .beq a0 x0 0x24, 2) := by decide
theorem mp_ba : fetchRel manifestParseCode 0xBA = some (.load .lbu a0 sp 0xD, 4) := by decide
theorem mp_be : fetchRel manifestParseCode 0xBE = some (.jal x0 0x4, 2) := by decide
theorem mp_c0 : fetchRel manifestParseCode 0xC0 = some (.aluImm .add a0 x0 0x3, 2) := by decide
theorem mp_c2 : fetchRel manifestParseCode 0xC2 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem mp_c6 : fetchRel manifestParseCode 0xC6 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem mp_c8 : fetchRel manifestParseCode 0xC8 = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem mp_d8 : fetchRel manifestParseCode 0xD8 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem mp_da : fetchRel manifestParseCode 0xDA = some (.jalr x0 ra 0x0, 2) := by decide
theorem mp_e0 : fetchRel manifestParseCode 0xE0 = some (.branch .bne a1 a0 0x56, 4) := by decide
theorem mp_e6 : fetchRel manifestParseCode 0xE6 = some (.branch .bne (9 : Fin 32) a3 0x54, 4) := by decide
theorem mp_f2 : fetchRel manifestParseCode 0xF2 = some (.branch .bltu a1 (20 : Fin 32) 0xFFFFFFD0, 4) := by decide
theorem mp_fa : fetchRel manifestParseCode 0xFA = some (.branch .bltu a4 (19 : Fin 32) 0xFFFFFFC8, 4) := by decide
theorem mp_106 : fetchRel manifestParseCode 0x106 = some (.branch .bltu a5 a2 0xFFFFFFBC, 4) := by decide
theorem mp_10c : fetchRel manifestParseCode 0x10C = some (.branch .bltu (18 : Fin 32) a3 0x2E, 4) := by decide
theorem mp_110 : fetchRel manifestParseCode 0x110 = some (.branch .bltu a1 a4 0x2A, 4) := by decide
theorem mp_11a : fetchRel manifestParseCode 0x11A = some (.branch .bltu a3 a5 0xFFFFFFA8, 4) := by decide
theorem mp_134 : fetchRel manifestParseCode 0x134 = some (.jal x0 0xFFFFFF94, 2) := by decide
theorem mp_13a : fetchRel manifestParseCode 0x13A = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem mp_13c : fetchRel manifestParseCode 0x13C = some (.jal x0 0xFFFFFF86, 2) := by decide
end

/-- What `parse` saves, and where in its frame. -/
abbrev mpPs : List (Fin 32 × Word) :=
  [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20), ((19 : Fin 32), 0x1C),
    ((20 : Fin 32), 0x18)]

def mpA : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 x0 0x20, .sw sp a1 0x0, .sw sp a0 0x4, .sw sp x0 0x8,
    .lui a1 0x4C533000, .aluImm .add a1 a1 0x343, .alu .add a0 x0 sp]
def mpR : List BInstr := [.alu .add a0 x0 sp, .aluImm .add a1 x0 0x2]
def mpP1 : List BInstr := [.aluImm .add a0 sp 0xC, .alu .add a1 x0 sp, .aluImm .add a2 x0 0x25, .lui a3 0x1D0000]
def mpP2 : List BInstr :=
  [.lw (9 : Fin 32) sp 0x10, .lw (20 : Fin 32) sp 0x14, .aluImm .add a0 sp 0xC, .alu .add a1 x0 sp,
    .aluImm .add a2 x0 0x31, .lui a3 0x4000]
def mpP3 : List BInstr :=
  [.lw (18 : Fin 32) sp 0x10, .lw (19 : Fin 32) sp 0x14, .aluImm .add a0 sp 0xC, .alu .add a1 x0 sp,
    .aluImm .add a2 x0 0x12, .lui a3 0x60000]
def mpL1 : List BInstr := [.lw a0 sp 0x4, .lw a1 sp 0x8]
def mpL2 : List BInstr := [.lui a3 0x10000]
def mpL3 : List BInstr := [.lui a0 0xFFFF0000, .aluImm .add a1 a0 0xFFFFFFFF, .aluImm .add a0 x0 0x6]
def mpL4 : List BInstr := [.alu .add a4 (19 : Fin 32) (18 : Fin 32)]
def mpL5 : List BInstr := [.lw a1 sp 0x10, .lw a2 sp 0x14, .alu .add a5 a2 a1]
def mpL6 : List BInstr := [.alu .add a3 a3 (20 : Fin 32)]
def mpL7 : List BInstr := [.lui a3 0x1E0000, .aluImm .add a0 x0 0x7]
def mpOk : List BInstr :=
  [.aluImm .add a0 x0 0x0, .lui a3 0x10000, .sw (8 : Fin 32) a3 0x4, .sw (8 : Fin 32) (20 : Fin 32) 0x8,
    .sw (8 : Fin 32) (18 : Fin 32) 0xC, .sw (8 : Fin 32) (19 : Fin 32) 0x10, .sw (8 : Fin 32) a1 0x14,
    .sw (8 : Fin 32) a2 0x18]

section
set_option maxRecDepth 20000
theorem mpSave_end : blockEnd manifestParseCode 2 (saveBlock mpPs) = some 0xE := by decide
theorem mpRestore_end : blockEnd manifestParseCode 0xCC (restoreBlock mpPs) = some 0xD8 := by decide
theorem mpA_end : blockEnd manifestParseCode 0xE mpA = some 0x24 := by decide
theorem mpR_end : blockEnd manifestParseCode 0x52 mpR = some 0x56 := by decide
theorem mpP1_end : blockEnd manifestParseCode 0x68 mpP1 = some 0x74 := by decide
theorem mpP2_end : blockEnd manifestParseCode 0x82 mpP2 = some 0x90 := by decide
theorem mpP3_end : blockEnd manifestParseCode 0x9E mpP3 = some 0xAC := by decide
theorem mpOk_end : blockEnd manifestParseCode 0x11E mpOk = some 0x134 := by decide
theorem mpL1_end : blockEnd manifestParseCode 0xDC mpL1 = some 0xE0 := by decide
theorem mpL2_end : blockEnd manifestParseCode 0xE4 mpL2 = some 0xE6 := by decide
theorem mpL3_end : blockEnd manifestParseCode 0xEA mpL3 = some 0xF2 := by decide
theorem mpL4_end : blockEnd manifestParseCode 0xF6 mpL4 = some 0xFA := by decide
theorem mpL5_end : blockEnd manifestParseCode 0xFE mpL5 = some 0x106 := by decide
theorem mpL6_end : blockEnd manifestParseCode 0x10A mpL6 = some 0x10C := by decide
theorem mpL7_end : blockEnd manifestParseCode 0x114 mpL7 = some 0x11A := by decide
end

/-- `andi a1, a0, 0xFF; addi a1, a1, -0xFF; bne a1, x0` continues when the
low byte of `a0` is 0xFF and goes to `T` otherwise. -/
theorem mp_check {Mx : Word → BitVec 8} {base : Word} {m : Machine} {off T : Nat}
    {o : Word} (s : St Mx base m off (reg m)) (hc : CodeIn Mx base manifestParseCode)
    (h1 : fetchRel manifestParseCode off = some (.aluImm .and a1 a0 0xFF, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.aluImm .add a1 a1 0xFFFFFF01, 4))
    (h3 : fetchRel manifestParseCode (off + 8) = some (.branch .bne a1 x0 o, 2))
    (ho : BitVec.ofNat 32 (off + 8) + o = BitVec.ofNat 32 T) :
    ∃ m', Steps m m' ∧ (∀ r, r ≠ a1 → reg m' r = reg m r) ∧
      ((reg m a0 &&& 0xFF = 0xFF ∧ St Mx base m' (off + 10) (reg m')) ∨
       (reg m a0 &&& 0xFF ≠ 0xFF ∧ St Mx base m' T (reg m'))) := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.aluImm hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc h2 (off' := off + 8) (ofNat_add_ofNat (off + 4) 4)
  have g2 : ∀ r, r ≠ a1 → upd (upd (reg m) a1 (aluEval .and (reg m a0) 0xFF)) a1
      (aluEval .add (upd (reg m) a1 (aluEval .and (reg m a0) 0xFF) a1) 0xFFFFFF01) r = reg m r :=
    fun r h => by rw [updz (by rw [updz hz (by decide)]; exact hz) h, updz hz h]
  have v2 : upd (upd (reg m) a1 (aluEval .and (reg m a0) 0xFF)) a1
      (aluEval .add (upd (reg m) a1 (aluEval .and (reg m a0) 0xFF) a1) 0xFFFFFF01) a1 =
        (reg m a0 &&& 0xFF) + 0xFFFFFF01 := by simp +decide [upd, aluEval]
  have z2 : upd (upd (reg m) a1 (aluEval .and (reg m a0) 0xFF)) a1
      (aluEval .add (upd (reg m) a1 (aluEval .and (reg m a0) 0xFF) a1) 0xFFFFFF01) x0 = 0 := by simp [upd]
  by_cases h : reg m a0 &&& 0xFF = 0xFF
  · obtain ⟨m3, e3, t3⟩ := t2.notTaken hc (off + 10) h3 (ofNat_add_ofNat (off + 8) 2)
      (by rw [v2, z2, h]; decide)
    exact ⟨m3, .cons e1 (.cons e2 (.single e3)), fun r hr => by rw [t3.regs]; exact g2 r hr,
      .inl ⟨h, t3.self⟩⟩
  · have hne : (reg m a0 &&& 0xFF) + 0xFFFFFF01 ≠ 0 := fun e => h (by
      have := congrArg (· + 0xFF) e
      simp only [BitVec.add_assoc] at this
      rw [show (0xFFFFFF01 : Word) + 0xFF = 0 from rfl] at this
      exact (BitVec.add_zero _).symm.trans (this.trans (BitVec.zero_add _)))
    obtain ⟨m3, e3, t3⟩ := t2.taken hc T h3 ho (by rw [v2, z2]; exact bne_iff_ne.mpr hne)
    exact ⟨m3, .cons e1 (.cons e2 (.single e3)), fun r hr => by rw [t3.regs]; exact g2 r hr,
      .inr ⟨h, t3.self⟩⟩

theorem u16_and1 (x y : BitVec 8) : (x.zeroExtend 32 <<< 24 ||| y.zeroExtend 32 <<< 16 : Word) &&& 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases h0 : i = 0
  · subst h0; simp
  · simp [h0]

/-- `Reader::bytes` on the 32-byte manifest. -/
theorem br32 (bp : Word) (pos n : Nat) (h : pos + n ≤ 32) :
    bytesResult bp 0x20 (BitVec.ofNat 32 pos) (BitVec.ofNat 32 n) =
      some (bp + BitVec.ofNat 32 pos, BitVec.ofNat 32 (pos + n)) := by
  rw [bytesResult_eq, if_pos (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp only [Nat.reducePow,
    show (0x20 : Word).toNat = 32 from rfl]; omega), ofNat_add_ofNat]

theorem allZero_congr {M M' : Word → BitVec 8} : ∀ {n : Nat} {p : Word},
    (∀ i, i < n → M' (p + BitVec.ofNat 32 i) = M (p + BitVec.ofNat 32 i)) → allZero M' p n = allZero M p n
  | 0, _, _ => rfl
  | k + 1, p, h => by
    simp only [allZero]
    have h0 := h 0 (by omega)
    rw [add_ofNat_zero] at h0
    have ih : allZero M' (p + 1) k = allZero M (p + 1) k := allZero_congr fun i hi => by
      have := h (1 + i) (by omega)
      rw [← add_ofNat_assoc] at this
      exact this
    rw [h0, ih]

/-- What `parse` keeps true between its calls: memory outside its 0x80-byte
stack `H` is `M0`, its saved registers are as `Ms` holds them, and the
reader at `H + 0x50` covers the 32 bytes at `bp` from `pos`. -/
structure MpInv (M0 Ms : Word → BitVec 8) (H bp : Word) (pos : Nat) (Mx : Word → BitVec 8) : Prop where
  io : ∀ x, Sep H 0x80 x 1 → Mx x = M0 x
  ss : ∀ c, 0x68 ≤ c → c < 0x80 → Mx (H + BitVec.ofNat 32 c) = Ms (H + BitVec.ofNat 32 c)
  r0 : memLoad32 Mx (H + BitVec.ofNat 32 0x50) = bp
  r4 : memLoad32 Mx (H + BitVec.ofNat 32 0x54) = 0x20
  r8 : memLoad32 Mx (H + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 pos

theorem MpInv.st32 {M0 Ms Mx : Word → BitVec 8} {H bp : Word} {pos c : Nat} (I : MpInv M0 Ms H bp pos Mx)
    (h1 : 0x5C ≤ c) (h2 : c + 4 ≤ 0x68) (v : Word) :
    MpInv M0 Ms H bp pos (memStore32 Mx (H + BitVec.ofNat 32 c) v) where
  io x hx := by rw [memStore32_get_sep ((hx.symm.subR (c := c) (l := 4) (by omega)).symm), I.io x hx]
  ss c' h3 h4 := by
    rw [memStore32_get_sep (sep_offsets H (c := c) (n := 4) (d := c') (k := 1) (by omega) (by omega) (by omega)),
      I.ss c' h3 h4]
  r0 := by rw [memLoad32_store32_sep (sep_offsets H (by omega) (by omega) (by omega)), I.r0]
  r4 := by rw [memLoad32_store32_sep (sep_offsets H (by omega) (by omega) (by omega)), I.r4]
  r8 := by rw [memLoad32_store32_sep (sep_offsets H (by omega) (by omega) (by omega)), I.r8]

theorem MpInv.st8 {M0 Ms Mx : Word → BitVec 8} {H bp : Word} {pos c : Nat} (I : MpInv M0 Ms H bp pos Mx)
    (h1 : 0x5C ≤ c) (h2 : c < 0x68) (v : BitVec 8) :
    MpInv M0 Ms H bp pos (memStore8 Mx (H + BitVec.ofNat 32 c) v) where
  io x hx := by rw [memStore8_ne (dn_sep1 ((hx.symm.subR (c := c) (l := 1) (by omega)).symm)), I.io x hx]
  ss c' h3 h4 := by
    rw [memStore8_ne (dn_sep1 (sep_offsets H (c := c) (n := 1) (d := c') (k := 1) (by omega) (by omega)
      (by omega))), I.ss c' h3 h4]
  r0 := by rw [memLoad32_store8_sep (sep_offsets H (by omega) (by omega) (by omega)), I.r0]
  r4 := by rw [memLoad32_store8_sep (sep_offsets H (by omega) (by omega) (by omega)), I.r4]
  r8 := by rw [memLoad32_store8_sep (sep_offsets H (by omega) (by omega) (by omega)), I.r8]

theorem MpInv.pos {M0 Ms Mx : Word → BitVec 8} {H bp : Word} {pos : Nat} (I : MpInv M0 Ms H bp pos Mx)
    (pos' : Nat) : MpInv M0 Ms H bp pos' (memStore32 Mx (H + BitVec.ofNat 32 0x58) (BitVec.ofNat 32 pos')) where
  io x hx := by rw [memStore32_get_sep ((hx.symm.subR (c := 0x58) (l := 4) (by omega)).symm), I.io x hx]
  ss c' h3 h4 := by
    rw [memStore32_get_sep (sep_offsets H (c := 0x58) (n := 4) (d := c') (k := 1) (by omega) (by omega)
      (by omega)), I.ss c' h3 h4]
  r0 := by rw [memLoad32_store32_sep (sep_offsets H (by omega) (by omega) (by omega)), I.r0]
  r4 := by rw [memLoad32_store32_sep (sep_offsets H (by omega) (by omega) (by omega)), I.r4]
  r8 := memLoad32_store32_same _ _ _

theorem MpInv.agree {M0 Ms Mx My : Word → BitVec 8} {H bp : Word} {pos : Nat} (I : MpInv M0 Ms H bp pos Mx)
    (h1 : ∀ x, Sep H 0x80 x 1 → My x = Mx x)
    (h2 : ∀ c, 0x50 ≤ c → c < 0x80 → My (H + BitVec.ofNat 32 c) = Mx (H + BitVec.ofNat 32 c)) :
    MpInv M0 Ms H bp pos My where
  io x hx := by rw [h1 x hx, I.io x hx]
  ss c h3 h4 := by rw [h2 c (by omega) h4, I.ss c h3 h4]
  r0 := by rw [← I.r0]; exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h2 _ (by omega) (by omega)
  r4 := by rw [← I.r4]; exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h2 _ (by omega) (by omega)
  r8 := by rw [← I.r8]; exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h2 _ (by omega) (by omega)

theorem magic_at {M : Word → BitVec 8} {self bp k : Word} {pos : Nat} (h0 : memLoad32 M self = bp)
    (h4 : memLoad32 M (self + 4) = 0x20) (h8 : memLoad32 M (self + 8) = BitVec.ofNat 32 pos) (hp : pos + 4 ≤ 32) :
    magicResult M self k = (if memLoad32 M (bp + BitVec.ofNat 32 pos) == k then 0xFFFFFFFF else 2) ∧
      magicMem M self = memStore32 M (self + 8) (BitVec.ofNat 32 (pos + 4)) := by
  have b : bytesResult bp 0x20 (BitVec.ofNat 32 pos) 4 = some (bp + BitVec.ofNat 32 pos, BitVec.ofNat 32 (pos + 4)) :=
    br32 bp pos 4 hp
  simp only [magicResult, magicMem, h0, h4, h8, b, and_true]
  all_goals rfl

theorem u16_at {M : Word → BitVec 8} {self bp : Word} {pos : Nat} (h0 : memLoad32 M self = bp)
    (h4 : memLoad32 M (self + 4) = 0x20) (h8 : memLoad32 M (self + 8) = BitVec.ofNat 32 pos) (hp : pos + 2 ≤ 32) :
    u16Result M self = ((M (bp + BitVec.ofNat 32 pos + 1)).zeroExtend 32 <<< 24 |||
        (M (bp + BitVec.ofNat 32 pos)).zeroExtend 32 <<< 16 : Word) ∧
      u16Mem M self = memStore32 M (self + 8) (BitVec.ofNat 32 (pos + 2)) := by
  have b : bytesResult bp 0x20 (BitVec.ofNat 32 pos) 2 = some (bp + BitVec.ofNat 32 pos, BitVec.ofNat 32 (pos + 2)) :=
    br32 bp pos 2 hp
  simp only [u16Result, u16Mem, h0, h4, h8, b, and_true]
  all_goals rfl

theorem reserved_at {M : Word → BitVec 8} {self bp : Word} {pos : Nat} (h0 : memLoad32 M self = bp)
    (h4 : memLoad32 M (self + 4) = 0x20) (h8 : memLoad32 M (self + 8) = BitVec.ofNat 32 pos) (hp : pos + 2 ≤ 32) :
    reservedResult M self 2 = (if allZero M (bp + BitVec.ofNat 32 pos) 2 then 0xFF else 4) ∧
      reservedMem M self 2 = memStore32 M (self + 8) (BitVec.ofNat 32 (pos + 2)) := by
  have b : bytesResult bp 0x20 (BitVec.ofNat 32 pos) 2 = some (bp + BitVec.ofNat 32 pos, BitVec.ofNat 32 (pos + 2)) :=
    br32 bp pos 2 hp
  simp only [reservedResult, reservedMem, h0, h4, h8, b, and_true]
  all_goals rfl

theorem part_at {M : Word → BitVec 8} {out self bp lo hi : Word} {pos : Nat} (h0 : memLoad32 M self = bp)
    (h4 : memLoad32 M (self + 4) = 0x20) (h8 : memLoad32 M (self + 8) = BitVec.ofNat 32 pos) (hp : pos + 8 ≤ 32) :
    partMem M out self lo hi =
      if partOut lo hi (memLoad32 M (bp + BitVec.ofNat 32 (pos + 4))) then
        memStore8 (memStore8 (memStore32 M (self + 8) (BitVec.ofNat 32 (pos + 8))) (out + 1) 5) out 1
      else
        memStore8 (memStore32 (memStore32 (memStore32 M (self + 8) (BitVec.ofNat 32 (pos + 8)))
          (out + 4) (memLoad32 M (bp + BitVec.ofNat 32 pos))) (out + 8)
          (memLoad32 M (bp + BitVec.ofNat 32 (pos + 4)))) out 0 := by
  have b1 : bytesResult bp 0x20 (BitVec.ofNat 32 pos) 4 = some (bp + BitVec.ofNat 32 pos, BitVec.ofNat 32 (pos + 4)) :=
    br32 bp pos 4 (by omega)
  have b2 : bytesResult bp 0x20 (BitVec.ofNat 32 (pos + 4)) 4 =
      some (bp + BitVec.ofNat 32 (pos + 4), BitVec.ofNat 32 (pos + 8)) := br32 bp (pos + 4) 4 (by omega)
  simp only [partMem, h0, h4, h8, b1, b2]

/-- The registers `parse` keeps without saving them. -/
abbrev mpK : List Nat := [3, 4, 6, 7, 16, 17, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

/-- What `manifestParse_correct` concludes about the machine `m'` it returns
with. -/
abbrev mpPost (m m' : Machine) (sp0 out bp retAddr H : Word) : Prop :=
  Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
    (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
    ∀ x, Sep H 0x80 x 1 → m'.mem x = parseMemV2 m.mem out bp x

set_option hygiene false in
/-- Decides a register fact from `hq : q.val ∈ mpK`. -/
local macro "kdec" : tactic => `(tactic| (revert hq; revert q; decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `manifest::parse`**: for the 32 bytes at `bp`, it writes
`parseMemV2`'s result at `out` and returns with `sp` and the callee-saved
registers restored. It writes nothing else outside the 0x80 bytes of stack
below `sp`, its own frame and its callees'. -/
theorem manifestParse_correct (m : Machine) {sp0 out bp retAddr : Word} (code : MPCode m.mem)
    (hpc : m.pc = MP) (ha0 : reg m a0 = out) (ha1 : reg m a1 = bp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0)
    (hsl : 0x80 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000) (hbp : bp ≠ 0) (hbw : bp.toNat + 32 ≤ 2 ^ 32)
    (hoa : out.toNat % 4 = 0) (how : out.toNat + 28 ≤ 0x40000000)
    (sBS : Sep bp 32 (sp0 + 0xFFFFFF80) 0x80) (sOS : Sep out 28 (sp0 + 0xFFFFFF80) 0x80) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF80) 0x80 x 1 → m'.mem x = parseMemV2 m.mem out bp x := by
  obtain ⟨H, hH⟩ : ∃ H, sp0 + 0xFFFFFF80 = H := ⟨_, rfl⟩
  rw [hH] at sBS sOS ⊢
  suffices hP : ∃ m', mpPost m m' sp0 out bp retAddr H from hP
  have hHn : H.toNat = sp0.toNat - 0x80 := by
    rw [← hH, BitVec.toNat_add, show (0xFFFFFF80 : Word).toNat = 2 ^ 32 - 0x80 from rfl]; have := sp0.isLt; omega
  have hHc : ∀ c, c ≤ 0x80 → (H + BitVec.ofNat 32 c).toNat = H.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hHa : H.toNat % 4 = 0 := by omega
  obtain ⟨G, hG⟩ : ∃ G, H + BitVec.ofNat 32 0x50 = G := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add hHa (by decide)
  have eGk : ∀ k, G + BitVec.ofNat 32 k = H + BitVec.ofNat 32 (0x50 + k) := fun k => by rw [← hG, add_ofNat_assoc]
  have eGS : G + 0x30 = sp0 := by
    rw [show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, eGk, ← hH, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have offs : ∀ {c n e k : Nat}, c + n ≤ e ∨ e + k ≤ c → c + n ≤ 0x80 → e + k ≤ 0x80 →
      Sep (H + BitVec.ofNat 32 c) n (H + BitVec.ofNat 32 e) k := fun h h1 h2 => sep_offsets H h (by omega) (by omega)
  have inH : ∀ {c l : Nat} {x : Word}, Sep H 0x80 x 1 → c + l ≤ 0x80 → Sep (H + BitVec.ofNat 32 c) l x 1 :=
    fun hx h => (hx.symm.subR h).symm
  have hiH : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep H 0x80 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have cd : ∀ {M' : Word → BitVec 8} {c : Word} {code : List Nat}, CodeIn m.mem c code → 0x40000000 ≤ c.toNat →
      c.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep H 0x80 x 1 → M' x = m.mem x) → CodeIn M' c code :=
    fun hc h1 h2 hM i hi' => by rw [hM _ (hiH _ (dn_code_hi h1 h2 hi'))]; exact hc i hi'
  have hMPn : MP.toNat = (img% manifestParseAddress) := by decide
  have cdP : ∀ {M' : Word → BitVec 8}, (∀ x, Sep H 0x80 x 1 → M' x = m.mem x) → CodeIn M' MP manifestParseCode :=
    fun hM => cd code.parse (by rw [hMPn]; decide) (by rw [hMPn]; decide) hM
  have hiC : ∀ {c l : Nat} {a : Word} {len : Nat}, c + l ≤ 0x80 → 0x40000000 ≤ a.toNat → a.toNat + len ≤ 2 ^ 32 →
      Sep (H + BitVec.ofNat 32 c) l a len := fun h h1 h2 => sep_of_le (by rw [hHc _ (by omega)]; omega) h2
  have st0 : St m.mem MP m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm code.parse mp_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = G := by
    simp +decide only [upd, ↓reduceIte]; rw [hsp, ← hG, ← hH, BitVec.add_assoc]; rfl
  have slotO : ∀ o : Word, G + o = H + BitVec.ofNat 32 (0x50 + o.toNat) := fun o => by
    rw [← eGk, ofNat_toNat_self]
  have slotC : ∀ o : Word, o.toNat ≤ 0x2C → Sep (G + o) 4 MP manifestParseCode.length := fun o ho => by
    rw [slotO]; exact hiC (by omega) (by rw [hMPn]; decide) (by rw [hMPn]; decide)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock mpPs) u1 code.parse mpSave_end (saveBlock_ok _ mpPs _ fun q hq => by
      rw [sp1]
      simp only [mpPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨aligned_add hGa (by decide), slotC _ (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem G (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) mpPs = Ms :=
    ⟨_, rfl⟩
  rw [hMs] at u2
  have IMs : ∀ x, Sep H 0x80 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact saveMem_outside mpPs fun q hq => by
      simp only [mpPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [slotO]; exact inH hx (by decide))
  have slots : ∀ r o, (r, o) ∈ mpPs → memLoad32 Ms (G + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp := by
      simp only [mpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot mpPs _ hm (by
      simp only [mpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide),
      upd_ne (by
        simp only [mpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hr]
  have hc2 : CodeIn Ms MP manifestParseCode := cdP IMs
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q q1 => by rw [u2.regs]; exact updz hz q1
  have sp2 : reg m2 sp = G := by rw [u2.regs]; exact sp1
  -- the exits
  have hpsp : ∀ p ∈ mpPs, p.1 ≠ sp := by decide
  have sOC : ∀ {c l : Nat}, c + l ≤ 28 → Sep (out + BitVec.ofNat 32 c) l MP manifestParseCode.length :=
    fun {c l} h => by
      have e : (out + BitVec.ofNat 32 c).toNat = out.toNat + c := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact sep_of_le (by rw [e, hMPn]; omega) (by rw [hMPn]; decide)
  have tailC8 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word}, St Mt MP nn 0xC8 (reg nn) →
      CodeIn Mt MP manifestParseCode → reg nn sp = G → reg nn 8 = out → reg nn a0 = v →
      (∀ c', 0x68 ≤ c' → c' < 0x80 → Mt (H + BitVec.ofNat 32 c') = Ms (H + BitVec.ofNat 32 c')) →
      (∀ q, q.val ∈ mpK → reg nn q = reg m q) →
      ∃ nn', Steps nn nn' ∧ nn'.pc = retAddr ∧ reg nn' sp = sp0 ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg nn' r = reg m r) ∧
        nn'.mem = memStore8 Mt out (v.extractLsb' 0 8) := by
    intro Mt nn v st hct rsp r8 ra0 hsl' hK
    obtain ⟨n1, d1, u1⟩ := st.sb hct mp_c8 (off' := 0xCC) (by decide)
    rw [r8, add_lit_zero, ra0] at u1
    have hct1 : CodeIn (memStore8 Mt out (v.extractLsb' 0 8)) MP manifestParseCode := by
      have := sOC (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this; exact hct.store8 this
    have slotT : ∀ o : Word, 0x18 ≤ o.toNat → o.toNat + 4 ≤ 0x30 →
        memLoad32 (memStore8 Mt out (v.extractLsb' 0 8)) (G + o) = memLoad32 Ms (G + o) := fun o h1 h2 => by
      rw [slotO]; apply memLoad32_congr; intro j hj
      rw [add_ofNat_assoc, memStore8_ne (by
        have := sOS.sub (c := 0) (l := 1) (by decide); rw [add_ofNat_zero] at this
        exact dn_sep1 (this.subR (c := 0x50 + o.toNat + j) (l := 1) (by omega))), hsl' _ (by omega) (by omega)]
    obtain ⟨n2, c2', u2'⟩ := St.block (restoreBlock mpPs) u1 hct1 mpRestore_end
      (restoreBlock_ok (memStore8 Mt out (v.extractLsb' 0 8)) G mpPs (reg nn) rsp hpsp fun q hq => by
        simp only [mpPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hGa (by decide))
    simp only [restoreBlock_run (memStore8 Mt out (v.extractLsb' 0 8)) G mpPs (reg nn) rsp hpsp] at u2'
    have rsp' : restoreRegs (memStore8 Mt out (v.extractLsb' 0 8)) G (reg nn) mpPs sp = G := by
      rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    obtain ⟨n3, d3, u3⟩ := u2'.aluImm hct1 mp_d8 (off' := 0xDA) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hct1 mp_da
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs (memStore8 Mt out (v.extractLsb' 0 8)) G f ps q = f q := by
      intro f ps q hq0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne hq0 (fun e => h p List.mem_cons_self e.symm)]
    have hslot : ∀ r o, (r, o) ∈ mpPs → reg n4 r = reg m r := fun r o hm => by
      rw [regs4]
      simp only [mpPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
        rw [slotT _ (by decide) (by decide)]; exact slots _ _ (by decide)
    have sp4 : reg n4 sp = sp0 := by
      rw [regs4]; simp +decide only [upd, ↓reduceIte, aluEval]; rw [rsp', eGS]
    refine ⟨n4, .cons d1 (c2'.trans (.cons d3 (.single d4))), ?_, sp4, fun q h0 h1 h2 h3 h4 h5 h6 => ?_, ?_⟩
    · rw [pc4, ← regs4, hslot ra 0x2C (by decide), hra, add_lit_zero, hret]
    · rcases (by decide : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ t0 →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ q = sp ∨ q.val = 0 ∨ q.val ∈ mpK) q h0 h1 h2 h3 h4 h5 h6 with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | hv | hL
      · exact hslot _ 0x2C (by decide)
      · exact hslot _ 0x28 (by decide)
      · exact hslot _ 0x24 (by decide)
      · exact hslot _ 0x20 (by decide)
      · exact hslot _ 0x1C (by decide)
      · exact hslot _ 0x18 (by decide)
      · rw [sp4, hsp]
      · obtain rfl : q = 0 := Fin.ext hv
        rw [regs4, hz]; simp [upd]
      · obtain ⟨hv, hs, hps⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ mpPs, p.1 ≠ q) :=
          (by decide : ∀ q : Fin 32, q.val ∈ mpK → q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ mpPs, p.1 ≠ q)) q hL
        rw [regs4, upd_ne hv hs, rr _ _ q hv hps, hK q hL]
    · rw [mem4]

  have finC2 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {v : Word} {e : BitVec 8} {pos : Nat}, Steps m nn →
      St Mt MP nn 0xC2 (reg nn) → MpInv m.mem Ms H bp pos Mt → reg nn sp = G → reg nn 8 = out →
      (∀ q, q.val ∈ mpK → reg nn q = reg m q) → reg nn a0 = v → v.extractLsb' 0 8 = e →
      parseErrV2 m.mem bp = some e → ∃ m', mpPost m m' sp0 out bp retAddr H := by
    intro Mt nn v e pos pre st I rsp r8 hK ra0 hv hpe
    have hct := cdP I.io
    obtain ⟨n1, d1, u1⟩ := st.sb hct mp_c2 (off' := 0xC6) (by decide)
    rw [r8, ra0, hv] at u1
    have hct1 := hct.store8 (v := e) (sOC (c := 1) (l := 1) (by decide))
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hct1 mp_c6 (off' := 0xC8) (by decide)
    obtain ⟨n3, c3, pc3, sp3, K3, mem3⟩ := tailC8 (v := 1) u2.self hct1
      (by rw [u2.regs, upd_ne' (by decide) st.zero, rsp]) (by rw [u2.regs, upd_ne' (by decide) st.zero, r8])
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl)
      (fun c' h1 h2 => by
        rw [memStore8_ne (show H + BitVec.ofNat 32 c' ≠ out + 1 from
          dn_sep1 ((sOS.sub (c := 1) (l := 1) (by decide)).subR (c := c') (l := 1) (by omega))), I.ss c' h1 h2])
      (fun q hq => by rw [u2.regs, upd_ne' (by revert hq; revert q; decide) st.zero, hK q hq])
    refine ⟨n3, pre.trans (.cons d1 (.cons d2 c3)), pc3, sp3, K3, fun x hx => ?_⟩
    rw [mem3, show ((1 : Word).extractLsb' 0 8) = (1 : BitVec 8) by decide]
    simp only [parseMemV2, hpe]
    exact memStore8_congr (memStore8_congr (I.io x hx))
  have finC0 : ∀ {Mt : Word → BitVec 8} {nn : Machine} {pos : Nat}, Steps m nn →
      St Mt MP nn 0xC0 (reg nn) → MpInv m.mem Ms H bp pos Mt → reg nn sp = G → reg nn 8 = out →
      (∀ q, q.val ∈ mpK → reg nn q = reg m q) → parseErrV2 m.mem bp = some 3 →
      ∃ m', mpPost m m' sp0 out bp retAddr H := by
    intro Mt nn pos pre st I rsp r8 hK hpe
    obtain ⟨n1, d1, u1⟩ := st.aluImm (cdP I.io) mp_c0 (off' := 0xC2) (by decide)
    exact finC2 (v := 3) (pre.trans (.single d1)) u1.self I
      (by rw [u1.regs, upd_ne' (by decide) st.zero, rsp]) (by rw [u1.regs, upd_ne' (by decide) st.zero, r8])
      (fun q hq => by rw [u1.regs, upd_ne' (by revert hq; revert q; decide) st.zero, hK q hq])
      (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl) (by decide) hpe
  have fin13A : ∀ {Mt : Word → BitVec 8} {nn : Machine} {pos : Nat}, Steps m nn →
      St Mt MP nn 0x13A (reg nn) → MpInv m.mem Ms H bp pos Mt → reg nn sp = G → reg nn 8 = out →
      (∀ q, q.val ∈ mpK → reg nn q = reg m q) → parseErrV2 m.mem bp = some 7 →
      ∃ m', mpPost m m' sp0 out bp retAddr H := by
    intro Mt nn pos pre st I rsp r8 hK hpe
    have hct := cdP I.io
    obtain ⟨n1, d1, u1⟩ := st.aluImm hct mp_13a (off' := 0x13C) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.jump hct mp_13c (off' := 0xC2) (by decide) (by rw [u1.pc]; decide)
    exact finC2 (v := 7) (pre.trans (.cons d1 (.single d2))) u2.self I
      (by rw [u2.regs, upd_ne' (by decide) st.zero, rsp]) (by rw [u2.regs, upd_ne' (by decide) st.zero, r8])
      (fun q hq => by rw [u2.regs, upd_ne' (by revert hq; revert q; decide) st.zero, hK q hq])
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl) (by decide) hpe
  have finBA : ∀ {Mt : Word → BitVec 8} {nn : Machine} {pos : Nat}, Steps m nn →
      St Mt MP nn 0xBA (reg nn) → MpInv m.mem Ms H bp pos Mt → reg nn sp = G → reg nn 8 = out →
      (∀ q, q.val ∈ mpK → reg nn q = reg m q) → Mt (G + 0xD) = 5 → parseErrV2 m.mem bp = some 5 →
      ∃ m', mpPost m m' sp0 out bp retAddr H := by
    intro Mt nn pos pre st I rsp r8 hK h5 hpe
    have hct := cdP I.io
    obtain ⟨n1, d1, u1⟩ := st.lbu hct mp_ba (off' := 0xBE) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.jump hct mp_be (off' := 0xC2) (by decide) (by rw [u1.pc]; decide)
    have K2 : ∀ q, q ≠ a0 → reg n2 q = reg nn q := fun q h0 => by
      rw [u2.regs, u1.regs, upd_ne' h0 st.zero]
    exact finC2 (v := (Mt (G + 0xD)).zeroExtend 32) (pre.trans (.cons d1 (.single d2))) u2.self I
      (by rw [K2 sp (by decide), rsp]) (by rw [K2 8 (by decide), r8])
      (fun q hq => by rw [K2 q (by revert hq; revert q; decide), hK q hq])
      (by rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp]) (by rw [h5]; rfl) hpe
  -- 0xE: the reader over the 32 bytes at `bp`
  have eG4 : G + 4 = H + BitVec.ofNat 32 0x54 := eGk 4
  have eG8 : G + 8 = H + BitVec.ofNat 32 0x58 := eGk 8
  have eGC : G + 0xC = H + BitVec.ofNat 32 0x5C := eGk 0xC
  have eGD : G + 0xD = H + BitVec.ofNat 32 0x5D := eGk 0xD
  have eG10 : G + 0x10 = H + BitVec.ofNat 32 0x60 := eGk 0x10
  have eG14 : G + 0x14 = H + BitVec.ofNat 32 0x64 := eGk 0x14
  have hG4 : (G + 4).toNat % 4 = 0 := aligned_add hGa (by decide)
  have hG8 : (G + 8).toNat % 4 = 0 := aligned_add hGa (by decide)
  obtain ⟨m3, c3, u3⟩ := St.block mpA u2.self hc2 mpA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, mpA, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp2]
    exact ⟨⟨aligned_add hGa (by decide), slotC _ (by decide)⟩, ⟨hG4, slotC _ (by decide)⟩, hG8, slotC _ (by decide)⟩)

  have R3 : ∀ q, reg m3 q = (runBlock mpA (Ms, reg m2)).2 q := u3.regs
  obtain ⟨Ma, hMa⟩ : ∃ Ma, memStore32 (memStore32 (memStore32 Ms G bp) (G + 4) 0x20) (G + 8) 0 = Ma := ⟨_, rfl⟩
  have eMa : (runBlock mpA (Ms, reg m2)).1 = Ma := by
    simp +decide only [runBlock, BInstr.run, mpA, upd_app, ↓reduceIte]
    rw [sp2, r2 a1 (by decide), ha1, add_lit_zero]; exact hMa
  have u3' : St Ma MP m3 0x24 (reg m3) := ⟨u3.pc, by rw [u3.mem, eMa], fun _ => rfl⟩
  have v3 : reg m3 a0 = G ∧ reg m3 a1 = 0x4C533343 ∧ reg m3 8 = out := by
    simp +decide only [R3, runBlock, BInstr.run, mpA, upd_app, ↓reduceIte]
    rw [sp2, r2 a0 (by decide), ha0, u2.self.zero]
    refine ⟨?_, ?_, ?_⟩ <;> first | exact zw _ | trivial | rfl
  have K3 : ∀ q, q.val ∉ [8, 10, 11] → reg m3 q = reg m2 q := fun q hq => by
    have hd : q ∉ mpA.filterMap BInstr.dst := by
      simp only [mpA, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R3, runBlock_reg _ _ _ q u2.self.zero hd]
  have I0 : MpInv m.mem Ms H bp 0 Ma := {
    io := fun x hx => by
      rw [← hMa, eG8, eG4, ← hG, memStore32_get_sep (inH hx (by decide)), memStore32_get_sep (inH hx (by decide)),
        memStore32_get_sep (inH hx (by decide)), IMs x hx]
    ss := fun c' h1 h2 => by
      rw [← hMa, eG8, eG4, ← hG, memStore32_get_sep (offs (.inl (by omega)) (by decide) (by omega)),
        memStore32_get_sep (offs (.inl (by omega)) (by decide) (by omega)),
        memStore32_get_sep (offs (.inl (by omega)) (by decide) (by omega))]
    r0 := by
      rw [← hMa, eG8, eG4, ← hG, memLoad32_store32_sep (offs (.inr (by decide)) (by decide) (by decide)),
        memLoad32_store32_sep (offs (.inr (by decide)) (by decide) (by decide)), memLoad32_store32_same]
    r4 := by
      rw [← hMa, eG8, eG4, ← hG, memLoad32_store32_sep (offs (.inr (by decide)) (by decide) (by decide)),
        memLoad32_store32_same]
    r8 := by rw [← hMa, eG8, memLoad32_store32_same]; rfl }
  have ld : ∀ {pos : Nat} {Mx : Word → BitVec 8}, MpInv m.mem Ms H bp pos Mx →
      memLoad32 Mx G = bp ∧ memLoad32 Mx (G + 4) = 0x20 ∧ memLoad32 Mx (G + 8) = BitVec.ofNat 32 pos :=
    fun I => by rw [eG4, eG8, ← hG]; exact ⟨I.r0, I.r4, I.r8⟩
  have win : ∀ {c l : Nat} {M' F : Word → BitVec 8}, c + l ≤ 0x50 →
      (∀ x, Sep (H + BitVec.ofNat 32 c) l x 1 → M' x = F x) →
      (∀ x, Sep H 0x80 x 1 → M' x = F x) ∧
        (∀ c', 0x50 ≤ c' → c' < 0x80 → M' (H + BitVec.ofNat 32 c') = F (H + BitVec.ofNat 32 c')) :=
    fun h hM => ⟨fun x hx => hM x (inH hx (by omega)),
      fun c' h1 h2 => hM _ (offs (.inl (by omega)) (by omega) (by omega))⟩
  have bpb : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep H 0x80 x 1 → Mx x = m.mem x) → ∀ i, i < 32 →
      Mx (bp + BitVec.ofNat 32 i) = m.mem (bp + BitVec.ofNat 32 i) :=
    fun hM i hi => hM _ (sBS.sub (c := i) (l := 1) (by omega)).symm
  have bpw : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep H 0x80 x 1 → Mx x = m.mem x) → ∀ i, i + 4 ≤ 32 →
      memLoad32 Mx (bp + BitVec.ofNat 32 i) = mw m.mem bp i :=
    fun hM i hi => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact bpb hM _ (by omega)
  have cdA : ∀ {M' : Word → BitVec 8} {a : Word} {code : List Nat}, CodeIn m.mem a code →
      0x40000000 ≤ a.toNat ∧ a.toNat + code.length ≤ 2 ^ 32 → (∀ x, Sep H 0x80 x 1 → M' x = m.mem x) →
      CodeIn M' a code := fun hc h hM => cd hc h.1 h.2 hM
  have kkS : ∀ {n1 n0 : Machine}, (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 →
      reg n1 r = reg n0 r) → ∀ q, q.val ∈ mpK → reg n1 q = reg n0 q := fun h q hq =>
    h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)
  -- the three `part` calls
  have eU32 : (BitVec.ofNat 32 manifestPartAddress + 0xFFFFCCA6 : Word) = BitVec.ofNat 32 readerU32Address := by
    decide
  have eA4 : (BitVec.ofNat 32 manifestPartAddress + 0xFFFFCCA6 + 0x50 : Word) =
      BitVec.ofNat 32 readerArray4Address := by decide
  have eBy : (BitVec.ofNat 32 manifestPartAddress + 0xFFFFCCA6 + 0x50 + 0xFFFFFF8A : Word) =
      BitVec.ofNat 32 readerBytesAddress := by decide
  have eW80 : G + 0xFFFFFFB0 = H + BitVec.ofNat 32 0 := by rw [← hG, BitVec.add_assoc]; rfl
  have eGC1 : G + 0xC + 1 = H + BitVec.ofNat 32 0x5D := by rw [eGC, BitVec.add_assoc]; rfl
  have eGC4 : G + 0xC + 4 = H + BitVec.ofNat 32 0x60 := by rw [eGC, BitVec.add_assoc]; rfl
  have eGC8 : G + 0xC + 8 = H + BitVec.ofNat 32 0x64 := by rw [eGC, BitVec.add_assoc]; rfl
  have partCall : ∀ {Mt : Word → BitVec 8} {nn : Machine} {pos c : Nat} {imm o lo hi : Word}, Steps m nn →
      St Mt MP nn c (reg nn) → MpInv m.mem Ms H bp pos Mt → pos + 8 ≤ 32 → c % 2 = 0 →
      fetchRel manifestParseCode c = some (.auipc ra imm, 4) →
      fetchRel manifestParseCode (c + 4) = some (.jalr ra ra o, 4) →
      MP + BitVec.ofNat 32 c + imm + o = BitVec.ofNat 32 manifestPartAddress →
      fetchRel manifestParseCode (c + 8) = some (.load .lbu a0 sp 0xC, 4) →
      reg nn sp = G → reg nn a0 = G + 0xC → reg nn a1 = G → reg nn a2 = lo → reg nn a3 = hi →
      ∃ n', Steps m n' ∧ St n'.mem MP n' (c + 12) (reg n') ∧ MpInv m.mem Ms H bp (pos + 8) n'.mem ∧
        (∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg n' r = reg nn r) ∧
        reg n' a0 = (if partOut lo hi (mw m.mem bp (pos + 4)) then 1 else 0) ∧
        (partOut lo hi (mw m.mem bp (pos + 4)) = true → n'.mem (G + 0xD) = 5) ∧
        (partOut lo hi (mw m.mem bp (pos + 4)) = false → memLoad32 n'.mem (G + 0x10) = mw m.mem bp pos ∧
          memLoad32 n'.mem (G + 0x14) = mw m.mem bp (pos + 4)) := by
    intro Mt nn pos c imm o lo hi pre st I hp hc2 h1 h2 hb h3 rsp ra0 ra1 ra2 ra3
    have hct := cdP I.io
    obtain ⟨n1, e1, pc1, mem1, regs1⟩ := st.callRa hct h1 h2 hb (by decide)
    have q1 := PEnv.reg1 regs1 st.zero
    have ldI := ld I
    have sp1 : reg n1 sp = G := by rw [q1 sp (by decide), rsp]
    obtain ⟨n2, e2, pc2, sp2', K2, fr2⟩ := manifestPart_correct n1 _ (MP + BitVec.ofNat 32 (c + 8)) (G + 0xC) G
      lo hi
      (fun i hi' => by rw [mem1]; exact cdA code.part (by decide) I.io i hi')
      (fun i hi' => by rw [mem1, eU32]; exact cdA code.u32 (by decide) I.io i hi')
      (fun i hi' => by rw [mem1, eA4]; exact cdA code.array4 (by decide) I.io i hi')
      (fun i hi' => by rw [mem1, eBy]; exact cdA code.bytes (by decide) I.io i hi')
      (by decide) pc1 (by rw [q1 a0 (by decide), ra0]) (by rw [q1 a1 (by decide), ra1])
      (by rw [q1 a2 (by decide), ra2]) (by rw [q1 a3 (by decide), ra3])
      (by rw [regs1]; simp +decide only [upd_app, ↓reduceIte])
      (even_clear _ (even_at MP (by decide) _ (by omega)))
      (by rw [sp1]; exact hGa) (aligned_add hGa (by decide)) hGa
      (by rw [mem1, ldI.1, ldI.2.1]; exact ⟨hbp, hbw⟩)
      (by rw [sp1, eW80]; exact hiC (by decide) (by decide) (by decide))
      (by rw [eGC]; exact hiC (by decide) (by decide) (by decide))
      (by rw [eG8]; exact hiC (by decide) (by decide) (by decide))
      (by rw [sp1, eW80, ← hG]; exact offs (.inr (by decide)) (by decide) (by decide))
      (by rw [sp1, eW80, eGC]; exact offs (.inr (by decide)) (by decide) (by decide))
      (by rw [mem1, ldI.1, ldI.2.1, sp1, eW80]; exact sBS.subR (by decide))
      (by rw [mem1, ldI.1, ldI.2.1, eG8]; exact sBS.subR (by decide))
    have pa := part_at (M := Mt) (out := G + 0xC) (lo := lo) (hi := hi) ldI.1 ldI.2.1 ldI.2.2 hp
    rw [sp1, eW80, mem1, pa, bpw I.io pos (by omega), bpw I.io (pos + 4) (by omega), eG8, eGC1, eGC4, eGC8, eGC]
      at fr2
    have sp2 : reg n2 sp = G := by rw [sp2', sp1]
    have rd : ∀ c', 0x50 ≤ c' → c' < 0x80 → ∀ F : Word → BitVec 8,
        (∀ x, Sep (H + BitVec.ofNat 32 0) 80 x 1 → n2.mem x = F x) →
        n2.mem (H + BitVec.ofNat 32 c') = F (H + BitVec.ofNat 32 c') :=
      fun c' h1 h2 F hF => hF _ (offs (.inl (by omega)) (by omega) (by omega))
    have rd32 : ∀ c', 0x50 ≤ c' → c' + 4 ≤ 0x80 → ∀ F : Word → BitVec 8,
        (∀ x, Sep (H + BitVec.ofNat 32 0) 80 x 1 → n2.mem x = F x) →
        memLoad32 n2.mem (H + BitVec.ofNat 32 c') = memLoad32 F (H + BitVec.ofNat 32 c') :=
      fun c' h1 h2 F hF => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact rd _ (by omega) (by omega) F hF
    have hn : BitVec.ofNat 32 (c + 8) + 4 = BitVec.ofNat 32 (c + 12) := by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, ofNat_add_ofNat]
    have u2 : St n2.mem MP n2 (c + 8) (reg n2) := ⟨pc2, rfl, fun _ => rfl⟩
    have ex : ∀ (I' : MpInv m.mem Ms H bp (pos + 8) n2.mem), ∃ n', Steps m n' ∧
        St n'.mem MP n' (c + 12) (reg n') ∧ MpInv m.mem Ms H bp (pos + 8) n'.mem ∧
        (∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg n' r = reg nn r) ∧
        reg n' a0 = (n2.mem (G + 0xC)).zeroExtend 32 ∧ n'.mem = n2.mem := fun I' => by
      obtain ⟨n3, e3, u3⟩ := u2.lbu (cdP I'.io) h3 (off' := c + 12) hn
      refine ⟨n3, pre.trans (e1.trans (e2.trans (.single e3))), ⟨u3.pc, rfl, fun _ => rfl⟩,
        by rw [u3.mem]; exact I', fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_,
        ?_, u3.mem⟩
      · rw [u3.regs, upd_ne' h1 u2.zero, K2 r h1 h2 h3 h4 h5 h6 h7, q1 r h0]
      · rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]
    cases hpo : partOut lo hi (mw m.mem bp (pos + 4)) with
    | true =>
      simp only [hpo, ↓reduceIte] at fr2
      have w := win (by decide) fr2
      obtain ⟨n', d', s', I', K', a', me'⟩ :=
        ex ((((I.pos (pos + 8)).st8 (c := 0x5D) (by decide) (by decide) 5).st8 (c := 0x5C) (by decide) (by decide)
          1).agree w.1 w.2)
      refine ⟨n', d', s', I', K', ?_, fun _ => ?_, fun h => absurd h (by decide)⟩
      · rw [a', eGC, rd _ (by decide) (by decide) _ fr2, memStore8_same]; rfl
      · rw [me', eGD, rd _ (by decide) (by decide) _ fr2, memStore8_ne (dn_sep1 (offs (.inl (by decide))
          (by decide) (by decide))), memStore8_same]
    | false =>
      simp only [hpo, Bool.false_eq_true, ↓reduceIte] at fr2
      have w := win (by decide) fr2
      obtain ⟨n', d', s', I', K', a', me'⟩ :=
        ex (((((I.pos (pos + 8)).st32 (c := 0x60) (by decide) (by decide) _).st32 (c := 0x64) (by decide)
          (by decide) _).st8 (c := 0x5C) (by decide) (by decide) 0).agree w.1 w.2)
      refine ⟨n', d', s', I', K', ?_, fun h => absurd h (by decide), fun _ => ⟨?_, ?_⟩⟩
      · rw [a', eGC, rd _ (by decide) (by decide) _ fr2, memStore8_same]; rfl
      · rw [me', eG10, rd32 _ (by decide) (by decide) _ fr2,
          memLoad32_store8_sep (offs (.inl (by decide)) (by decide) (by decide)),
          memLoad32_store32_sep (offs (.inr (by decide)) (by decide) (by decide)), memLoad32_store32_same]
      · rw [me', eG14, rd32 _ (by decide) (by decide) _ fr2,
          memLoad32_store8_sep (offs (.inl (by decide)) (by decide) (by decide)), memLoad32_store32_same]
  -- 0x24: `Reader::magic`
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3'.callRa (cdP I0.io) mp_24 mp_28
    (cb := BitVec.ofNat 32 readerMagicAddress) (by decide) (by decide)
  have r4 := PEnv.reg1 regs4 u3'.zero
  have sp4 : reg m4 sp = G := by rw [r4 sp (by decide), K3 sp (by decide), sp2]
  have ld0 := ld I0
  have eA : (BitVec.ofNat 32 readerMagicAddress + 0xFFFFFFBA : Word) = BitVec.ofNat 32 readerArray4Address := by
    decide
  have eB : (BitVec.ofNat 32 readerMagicAddress + 0xFFFFFFBA + 0xFFFFFF8A : Word) =
      BitVec.ofNat 32 readerBytesAddress := by decide
  have eW48 : G + 0xFFFFFFD0 = H + BitVec.ofNat 32 0x20 := by rw [← hG, BitVec.add_assoc]; rfl
  obtain ⟨m5, c5, pc5, sp5, a05, K5, fr5⟩ := readerMagic_correct m4 _ (MP + BitVec.ofNat 32 (0x24 + 8)) G
    0x4C533343
    (fun i hi => by rw [mem4]; exact cdA code.magic (by decide) I0.io i hi)
    (fun i hi => by rw [mem4, eA]; exact cdA code.array4 (by decide) I0.io i hi)
    (fun i hi => by rw [mem4, eB]; exact cdA code.bytes (by decide) I0.io i hi)
    (by decide) pc4 (by rw [r4 a0 (by decide), v3.1]) (by rw [r4 a1 (by decide), v3.2.1])
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at MP (by decide) _ (by decide)))
    (by rw [sp4]; exact hGa) hGa
    (by rw [mem4, ld0.1, ld0.2.1]; exact ⟨hbp, hbw⟩)
    (by rw [sp4, eW48]; exact hiC (by decide) (by decide) (by decide))
    (by rw [sp4, eW48, eA]; exact hiC (by decide) (by decide) (by decide))
    (by rw [sp4, eW48, eB]; exact hiC (by decide) (by decide) (by decide))
    (by rw [eG8]; exact hiC (by decide) (by decide) (by decide))
    (by rw [eG8, eA]; exact hiC (by decide) (by decide) (by decide))
    (by rw [eG8, eB]; exact hiC (by decide) (by decide) (by decide))
    (by rw [sp4, eW48, ← hG]; exact offs (.inr (by decide)) (by decide) (by decide))
    (by rw [mem4, ld0.1, ld0.2.1, sp4, eW48]; exact sBS.subR (by decide))
    (by rw [mem4, ld0.1, ld0.2.1, eG8]; exact sBS.subR (by decide))
  have mg := magic_at (M := Ma) (k := 0x4C533343) ld0.1 ld0.2.1 ld0.2.2 (by decide)
  rw [mem4, mg.1, bpw I0.io 0 (by decide)] at a05
  rw [sp4, eW48, mem4, mg.2, eG8] at fr5
  have I1 : MpInv m.mem Ms H bp 4 m5.mem := by
    have w := win (by decide) fr5; exact (I0.pos 4).agree w.1 w.2
  have u5 : St m5.mem MP m5 0x2C (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have sp5' : reg m5 sp = G := by rw [sp5, sp4]
  have r8_5 : reg m5 8 = out := by
    rw [K5 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r4 8 (by decide),
      v3.2.2]
  have kk5 : ∀ q, q.val ∈ mpK → reg m5 q = reg m q := fun q hq => by
    rw [kkS K5 q hq, r4 q (by revert hq; revert q; decide), K3 q (by revert hq; revert q; decide),
      r2 q (by revert hq; revert q; decide)]
  have pre5 : Steps m m5 := .cons d1 (c2.trans (c3.trans (c4.trans c5)))
  -- 0x2C: the magic check
  obtain ⟨m6, c6, K6, hb6⟩ := mp_check u5 (cdP I1.io) mp_2c mp_30 mp_34 (T := 0xC2) (by decide)
  have sp6 : reg m6 sp = G := by rw [K6 sp (by decide), sp5']
  have r8_6 : reg m6 8 = out := by rw [K6 8 (by decide), r8_5]
  have kk6 : ∀ q, q.val ∈ mpK → reg m6 q = reg m q := fun q hq => by rw [K6 q (by kdec), kk5 q hq]
  by_cases hm : mw m.mem bp 0 ≠ 0x4C533343
  · have hv : reg m5 a0 = 2 := by rw [a05, beq_eq_false_iff_ne.mpr hm]; rfl
    rcases hb6 with ⟨h, _⟩ | ⟨_, s6⟩
    · rw [hv] at h; exact absurd h (by decide : ¬((2 : Word) &&& 0xFF = 0xFF))
    · exact finC2 (v := 2) (e := 2) (pre5.trans c6) s6 I1 sp6 r8_6 kk6 (by rw [K6 a0 (by decide), hv]) (by decide)
        (by unfold parseErrV2; rw [beq_eq_false_iff_ne.mpr hm]; rfl)
  replace hm := Decidable.of_not_not hm
  have hv5 : reg m5 a0 = 0xFFFFFFFF := by rw [a05, hm]; rfl
  have s6 : St m5.mem MP m6 0x36 (reg m6) := by
    rcases hb6 with ⟨_, s6⟩ | ⟨h, _⟩
    · exact s6
    · rw [hv5] at h; exact (h (by decide)).elim
  -- 0x36: `Reader::u16`
  obtain ⟨m7, d7, u7⟩ := s6.alu (cdP I1.io) mp_36 (off' := 0x38) (by decide)
  have K7 : ∀ q, q ≠ a0 → reg m7 q = reg m6 q := fun q h => by rw [u7.regs]; exact upd_ne' h s6.zero
  have a07 : reg m7 a0 = G := by
    rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s6.zero, sp6]; exact zw G
  obtain ⟨m8, c8, pc8, mem8, regs8⟩ := u7.self.callRa (cdP I1.io) mp_38 mp_3c
    (cb := BitVec.ofNat 32 readerU16Address) (by decide) (by decide)
  have q8 := PEnv.reg1 regs8 u7.self.zero
  have sp8 : reg m8 sp = G := by rw [q8 sp (by decide), K7 sp (by decide), sp6]
  have ld1 := ld I1
  have eU : (BitVec.ofNat 32 readerU16Address + 0x44 : Word) = BitVec.ofNat 32 readerBytesAddress := by decide
  have eW16 : G + 0xFFFFFFF0 = H + BitVec.ofNat 32 0x40 := by rw [← hG, BitVec.add_assoc]; rfl
  obtain ⟨m9, c9, pc9, sp9, a09, K9, fr9⟩ := readerU16_correct m8 _ (MP + BitVec.ofNat 32 (0x38 + 8)) G
    (fun i hi => by rw [mem8]; exact cdA code.u16 (by decide) I1.io i hi)
    (fun i hi => by rw [mem8, eU]; exact cdA code.bytes (by decide) I1.io i hi)
    (by decide) pc8 (by rw [q8 a0 (by decide), a07])
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at MP (by decide) _ (by decide)))
    (by rw [sp8]; exact hGa) hGa
    (by rw [mem8, ld1.1, ld1.2.1]; exact ⟨hbp, hbw⟩)
    (by rw [sp8, eW16]; exact hiC (by decide) (by decide) (by decide))
    (by rw [sp8, eW16, eU]; exact hiC (by decide) (by decide) (by decide))
    (by rw [eG8]; exact hiC (by decide) (by decide) (by decide))
    (by rw [eG8, eU]; exact hiC (by decide) (by decide) (by decide))
    (by rw [sp8, eW16, ← hG]; exact offs (.inr (by decide)) (by decide) (by decide))
    (by rw [mem8, ld1.1, ld1.2.1, sp8, eW16]; exact sBS.subR (by decide))
    (by rw [mem8, ld1.1, ld1.2.1, eG8]; exact sBS.subR (by decide))
  have ug := u16_at (M := m5.mem) ld1.1 ld1.2.1 ld1.2.2 (by decide)
  have e45 : bp + BitVec.ofNat 32 4 + 1 = bp + BitVec.ofNat 32 5 := by rw [BitVec.add_assoc]; rfl
  rw [mem8, ug.1, e45, bpb I1.io 5 (by decide), bpb I1.io 4 (by decide)] at a09
  rw [sp8, eW16, mem8, ug.2, eG8] at fr9
  have I2 : MpInv m.mem Ms H bp 6 m9.mem := by
    have w := win (by decide) fr9; exact (I1.pos 6).agree w.1 w.2
  have kk9 : ∀ q, q.val ∈ mpK → reg m9 q = reg m q := fun q hq => by
    rw [K9 q (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec), q8 q (by kdec), K7 q (by kdec), kk6 q hq]
  have r8_9 : reg m9 8 = out := by
    rw [K9 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), q8 8 (by decide),
      K7 8 (by decide), r8_6]
  have sp9' : reg m9 sp = G := by rw [sp9, sp8]
  have u9 : St m9.mem MP m9 0x40 (reg m9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
  have pre9 : Steps m m9 := pre5.trans (c6.trans (.cons d7 (c8.trans c9)))
  -- 0x40: the version
  obtain ⟨m10, d10, u10⟩ := u9.aluImm (cdP I2.io) mp_40 (off' := 0x44) (by decide)
  obtain ⟨m11, d11, u11⟩ := u10.taken (cdP I2.io) 0x4A mp_44 (by decide) (by
    simp +decide only [upd_app, ↓reduceIte, branchTaken]; rw [a09]
    exact beq_iff_eq.mpr (u16_and1 _ _))
  obtain ⟨m12, d12, u12⟩ := u11.aluImm (cdP I2.io) mp_4a (off' := 0x4C) (by decide)
  obtain ⟨m13, d13, u13⟩ := u12.aluImm (cdP I2.io) mp_4c (off' := 0x4E) (by decide)
  obtain ⟨V, hV⟩ : ∃ V, reg m9 a0 >>> 16 = V := ⟨_, rfl⟩
  have f13 : ∀ q, q ≠ a0 → q ≠ a1 → reg m13 q = reg m9 q := fun q h0 h1 => by
    rw [u13.regs, upd_ne' h1 u12.zero, upd_ne' h0 u11.zero, upd_ne' h1 u9.zero]
  have a013 : reg m13 a0 = V := by
    rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [← hV]; rfl
  have a113 : reg m13 a1 = 2 := by
    rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]
  have pre13 : Steps m m13 := pre9.trans (.cons d10 (.cons d11 (.cons d12 (.single d13))))
  have kk13 : ∀ q, q.val ∈ mpK → reg m13 q = reg m q := fun q hq => by
    rw [f13 q (by kdec) (by kdec), kk9 q hq]
  by_cases hver : V ≠ 2
  · obtain ⟨m14, d14, u14⟩ := u13.self.taken (cdP I2.io) 0xC0 mp_4e (by decide) (by
      simp only [branchTaken]; rw [a013, a113]; exact bne_iff_ne.mpr hver)
    exact finC0 (pre13.trans (.single d14)) u14.self I2 (by rw [u14.regs, f13 sp (by decide) (by decide), sp9'])
      (by rw [u14.regs, f13 8 (by decide) (by decide), r8_9]) (fun q hq => by rw [u14.regs, kk13 q hq])
      (by
        unfold parseErrV2
        rw [a09] at hV
        rw [hm, hV, beq_eq_false_iff_ne.mpr hver]; rfl)
  replace hver := Decidable.of_not_not hver
  obtain ⟨m14, d14, u14⟩ := u13.self.notTaken (cdP I2.io) 0x52 mp_4e (by decide) (by
    simp only [branchTaken]; rw [a013, a113, hver]; rfl)
  have hVe := hV
  rw [a09, hver] at hVe
  have pre14 : Steps m m14 := pre13.trans (.single d14)
  have K14 : ∀ q, q ≠ a0 → q ≠ a1 → reg m14 q = reg m9 q := fun q h0 h1 => by rw [u14.regs, f13 q h0 h1]
  -- 0x52: `Reader::reserved`
  obtain ⟨m15, c15, u15⟩ := St.block mpR u14.self (cdP I2.io) mpR_end ⟨trivial, trivial, trivial⟩
  have R15 : ∀ q, reg m15 q = (runBlock mpR (m9.mem, reg m14)).2 q := u15.regs
  have u15' : St m9.mem MP m15 0x56 (reg m15) := ⟨u15.pc, by rw [u15.mem]; rfl, fun _ => rfl⟩
  have K15 : ∀ q, q ≠ a0 → q ≠ a1 → reg m15 q = reg m9 q := fun q h0 h1 => by
    have z : upd (reg m14) a0 (aluEval .add (reg m14 x0) (reg m14 sp)) 0 = 0 := by
      rw [upd_ne' (by decide) u14.self.zero]; exact u14.self.zero
    rw [R15]; simp only [runBlock, BInstr.run, mpR]; rw [upd_ne' h1 z, upd_ne' h0 u14.self.zero, K14 q h0 h1]
  have a015 : reg m15 a0 = G := by
    rw [R15]; simp +decide only [runBlock, BInstr.run, mpR, upd_app, ↓reduceIte]
    rw [u14.self.zero, K14 sp (by decide) (by decide), sp9']; exact zw G
  have a115 : reg m15 a1 = 2 := by
    rw [R15]; simp +decide only [runBlock, BInstr.run, mpR, upd_app, ↓reduceIte]
  obtain ⟨m16, c16, pc16, mem16, regs16⟩ := u15'.callRa (cdP I2.io) mp_56 mp_5a
    (cb := BitVec.ofNat 32 readerReservedAddress) (by decide) (by decide)
  have q16 := PEnv.reg1 regs16 u15'.zero
  have sp16 : reg m16 sp = G := by rw [q16 sp (by decide), K15 sp (by decide) (by decide), sp9']
  have ld2 := ld I2
  have eR : (BitVec.ofNat 32 readerReservedAddress + 0xFFFFD034 : Word) = BitVec.ofNat 32 readerBytesAddress := by
    decide
  obtain ⟨m17, c17, pc17, sp17, a017, K17, fr17⟩ := readerReserved_correct m16 _ (MP + BitVec.ofNat 32 (0x56 + 8))
    G 2
    (fun i hi => by rw [mem16]; exact cdA code.reserved (by decide) I2.io i hi)
    (fun i hi => by rw [mem16, eR]; exact cdA code.bytes (by decide) I2.io i hi)
    (by decide) pc16 (by rw [q16 a0 (by decide), a015]) (by rw [q16 a1 (by decide), a115]) (by decide)
    (by rw [regs16]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at MP (by decide) _ (by decide)))
    (by rw [sp16]; exact hGa) hGa
    (by rw [mem16, ld2.1, ld2.2.1]; exact ⟨hbp, hbw⟩)
    (by rw [sp16, eW16]; exact hiC (by decide) (by decide) (by decide))
    (by rw [sp16, eW16, eR]; exact hiC (by decide) (by decide) (by decide))
    (by rw [eG8]; exact hiC (by decide) (by decide) (by decide))
    (by rw [eG8, eR]; exact hiC (by decide) (by decide) (by decide))
    (by rw [sp16, eW16, ← hG]; exact offs (.inr (by decide)) (by decide) (by decide))
    (by rw [mem16, ld2.1, ld2.2.1, sp16, eW16]; exact sBS.subR (by decide))
    (by rw [mem16, ld2.1, ld2.2.1, eG8]; exact sBS.subR (by decide))
  have rg := reserved_at (M := m9.mem) ld2.1 ld2.2.1 ld2.2.2 (by decide)
  have az : allZero m9.mem (bp + BitVec.ofNat 32 6) 2 = allZero m.mem (bp + BitVec.ofNat 32 6) 2 :=
    allZero_congr fun i hi => by rw [add_ofNat_assoc]; exact bpb I2.io _ (by omega)
  rw [mem16, rg.1, az] at a017
  rw [sp16, eW16, mem16, rg.2, eG8] at fr17
  have I3 : MpInv m.mem Ms H bp 8 m17.mem := by
    have w := win (by decide) fr17; exact (I2.pos 8).agree w.1 w.2
  have kk17 : ∀ q, q.val ∈ mpK → reg m17 q = reg m q := fun q hq => by
    rw [K17 q (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec), q16 q (by kdec), K15 q (by kdec) (by kdec),
      kk9 q hq]
  have r8_17 : reg m17 8 = out := by
    rw [K17 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), q16 8 (by decide),
      K15 8 (by decide) (by decide), r8_9]
  have sp17' : reg m17 sp = G := by rw [sp17, sp16]
  have u17 : St m17.mem MP m17 0x5E (reg m17) := ⟨by rw [pc17], rfl, fun _ => rfl⟩
  have pre17 : Steps m m17 := pre14.trans (c15.trans (c16.trans c17))
  -- 0x5E: the reserved check
  obtain ⟨m18, c18, K18, hb18⟩ := mp_check u17 (cdP I3.io) mp_5e mp_62 mp_66 (T := 0xC2) (by decide)
  have sp18 : reg m18 sp = G := by rw [K18 sp (by decide), sp17']
  have r8_18 : reg m18 8 = out := by rw [K18 8 (by decide), r8_17]
  have kk18 : ∀ q, q.val ∈ mpK → reg m18 q = reg m q := fun q hq => by rw [K18 q (by kdec), kk17 q hq]
  cases hz : allZero m.mem (bp + BitVec.ofNat 32 6) 2 with
  | false =>
    simp only [hz, Bool.false_eq_true, ↓reduceIte] at a017
    rcases hb18 with ⟨h, _⟩ | ⟨_, s18⟩
    · rw [a017] at h; exact absurd h (by decide : ¬((4 : Word) &&& 0xFF = 0xFF))
    · exact finC2 (v := 4) (e := 4) (pre17.trans c18) s18 I3 sp18 r8_18 kk18 (by rw [K18 a0 (by decide), a017])
        (by decide) (by unfold parseErrV2; rw [hm, hVe, hz]; rfl)
  | true =>
  simp only [hz, ↓reduceIte] at a017
  have s18 : St m17.mem MP m18 0x68 (reg m18) := by
    rcases hb18 with ⟨_, s18⟩ | ⟨h, _⟩
    · exact s18
    · rw [a017] at h; exact (h (by decide)).elim
  have pre18 : Steps m m18 := pre17.trans c18
  -- 0x68: the first `part`
  obtain ⟨m19, c19, u19⟩ := St.block mpP1 s18 (cdP I3.io) mpP1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have R19 : ∀ q, reg m19 q = (runBlock mpP1 (m17.mem, reg m18)).2 q := u19.regs
  have u19' : St m17.mem MP m19 0x74 (reg m19) := ⟨u19.pc, by rw [u19.mem]; rfl, fun _ => rfl⟩
  have K19 : ∀ q, q.val ∉ [10, 11, 12, 13] → reg m19 q = reg m18 q := fun q hq => by
    have hd : q ∉ mpP1.filterMap BInstr.dst := by
      simp only [mpP1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R19, runBlock_reg _ _ _ q s18.zero hd]
  have v19 : reg m19 a0 = G + 0xC ∧ reg m19 a1 = G ∧ reg m19 a2 = 0x25 ∧ reg m19 a3 = 0x1D0000 := by
    simp +decide only [R19, runBlock, BInstr.run, mpP1, upd_app, ↓reduceIte]
    rw [sp18]
    exact ⟨rfl, zw G, trivial⟩
  obtain ⟨m20, d20, s20, I4, K20, a020, e20, l20⟩ := partCall (pos := 8) (pre18.trans c19) u19' I3 (by decide)
    (by decide) mp_74 mp_78 (by decide) mp_7c (by rw [K19 sp (by decide), sp18]) v19.1 v19.2.1 v19.2.2.1
    v19.2.2.2
  have kk20 : ∀ q, q.val ∈ mpK → reg m20 q = reg m q := fun q hq => by
    rw [K20 q (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec), K19 q (by kdec),
      kk18 q hq]
  have sp20 : reg m20 sp = G := by
    rw [K20 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K19 sp (by decide), sp18]
  have r8_20 : reg m20 8 = out := by
    rw [K20 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      K19 8 (by decide), r8_18]
  cases hp1 : partOut 0x25 0x1D0000 (mw m.mem bp (8 + 4)) with
  | true =>
    obtain ⟨m21, d21, u21⟩ := s20.taken (cdP I4.io) 0xBA mp_80 (by decide) (by
      simp only [branchTaken]; rw [a020, s20.zero, hp1]; decide)
    exact finBA (d20.trans (.single d21)) u21.self I4 (by rw [u21.regs, sp20])
      (by rw [u21.regs, r8_20]) (fun q hq => by rw [u21.regs, kk20 q hq]) (e20 hp1)
      (by unfold parseErrV2; rw [hm, hVe, hz]; rw [show (8 + 4 : Nat) = 12 from rfl] at hp1; rw [hp1]; rfl)
  | false =>
  obtain ⟨m21, d21, u21⟩ := s20.notTaken (cdP I4.io) 0x82 mp_80 (by decide) (by
    simp only [branchTaken]; rw [a020, s20.zero, hp1]; decide)
  have L20 := l20 hp1
  have hp1' : partOut 37 0x1D0000 (mw m.mem bp 12) = false := hp1
  -- 0x82: the second `part`
  obtain ⟨m22, c22, u22⟩ := St.block mpP2 u21 (cdP I4.io) mpP2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, mpP2, upd_app, ↓reduceIte, and_true]
    rw [sp20]; exact ⟨aligned_add hGa (by decide), aligned_add hGa (by decide)⟩)
  have R22 : ∀ q, reg m22 q = (runBlock mpP2 (m20.mem, reg m20)).2 q := u22.regs
  have u22' : St m20.mem MP m22 0x90 (reg m22) := ⟨u22.pc, by rw [u22.mem]; rfl, fun _ => rfl⟩
  have K22 : ∀ q, q.val ∉ [9, 20, 10, 11, 12, 13] → reg m22 q = reg m20 q := fun q hq => by
    have hd : q ∉ mpP2.filterMap BInstr.dst := by
      simp only [mpP2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R22, runBlock_reg _ _ _ q s20.zero hd]
  have v22 : reg m22 a0 = G + 0xC ∧ reg m22 a1 = G ∧ reg m22 a2 = 0x31 ∧ reg m22 a3 = 0x4000 ∧
      reg m22 9 = mw m.mem bp 8 ∧ reg m22 20 = mw m.mem bp 12 := by
    simp +decide only [R22, runBlock, BInstr.run, mpP2, upd_app, ↓reduceIte]
    rw [sp20, L20.1, L20.2]
    exact ⟨rfl, zw G, trivial, trivial, rfl, rfl⟩
  obtain ⟨m23, d23, s23, I5, K23, a023, e23, l23⟩ := partCall (pos := 16) ((d20.trans (.single d21)).trans c22) u22'
    I4 (by decide) (by decide) mp_90 mp_94 (by decide) mp_98 (by rw [K22 sp (by decide), sp20]) v22.1 v22.2.1
    v22.2.2.1 v22.2.2.2.1
  have kk23 : ∀ q, q.val ∈ mpK → reg m23 q = reg m q := fun q hq => by
    rw [K23 q (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec), K22 q (by kdec),
      kk20 q hq]
  have K23' : ∀ q, q.val ∈ [8, 2, 9, 20] → reg m23 q = reg m22 q := fun q hq =>
    K23 q (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec)
  have sp23 : reg m23 sp = G := by rw [K23' sp (by decide), K22 sp (by decide), sp20]
  have r8_23 : reg m23 8 = out := by rw [K23' 8 (by decide), K22 8 (by decide), r8_20]
  have s1_23 : reg m23 9 = mw m.mem bp 8 := by rw [K23' 9 (by decide), v22.2.2.2.2.1]
  have s4_23 : reg m23 20 = mw m.mem bp 12 := by rw [K23' 20 (by decide), v22.2.2.2.2.2]
  cases hp2 : partOut 0x31 0x4000 (mw m.mem bp (16 + 4)) with
  | true =>
    obtain ⟨m24, d24, u24⟩ := s23.taken (cdP I5.io) 0xBA mp_9c (by decide) (by
      simp only [branchTaken]; rw [a023, s23.zero, hp2]; decide)
    have hp2' : partOut 49 0x4000 (mw m.mem bp 20) = true := hp2
    exact finBA (d23.trans (.single d24)) u24.self I5 (by rw [u24.regs, sp23])
      (by rw [u24.regs, r8_23]) (fun q hq => by rw [u24.regs, kk23 q hq]) (e23 hp2)
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2']; rfl)
  | false =>
  obtain ⟨m24, d24, u24⟩ := s23.notTaken (cdP I5.io) 0x9E mp_9c (by decide) (by
    simp only [branchTaken]; rw [a023, s23.zero, hp2]; decide)
  have L23 := l23 hp2
  have hp2' : partOut 49 0x4000 (mw m.mem bp 20) = false := hp2
  -- 0x9E: the third `part`
  obtain ⟨m25, c25, u25⟩ := St.block mpP3 u24 (cdP I5.io) mpP3_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, mpP3, upd_app, ↓reduceIte, and_true]
    rw [sp23]; exact ⟨aligned_add hGa (by decide), aligned_add hGa (by decide)⟩)
  have R25 : ∀ q, reg m25 q = (runBlock mpP3 (m23.mem, reg m23)).2 q := u25.regs
  have u25' : St m23.mem MP m25 0xAC (reg m25) := ⟨u25.pc, by rw [u25.mem]; rfl, fun _ => rfl⟩
  have K25 : ∀ q, q.val ∉ [18, 19, 10, 11, 12, 13] → reg m25 q = reg m23 q := fun q hq => by
    have hd : q ∉ mpP3.filterMap BInstr.dst := by
      simp only [mpP3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
      revert hq; revert q; decide
    rw [R25, runBlock_reg _ _ _ q s23.zero hd]
  have v25 : reg m25 a0 = G + 0xC ∧ reg m25 a1 = G ∧ reg m25 a2 = 0x12 ∧ reg m25 a3 = 0x60000 ∧
      reg m25 18 = mw m.mem bp 16 ∧ reg m25 19 = mw m.mem bp 20 := by
    simp +decide only [R25, runBlock, BInstr.run, mpP3, upd_app, ↓reduceIte]
    rw [sp23, L23.1, L23.2]
    exact ⟨rfl, zw G, trivial, trivial, rfl, rfl⟩
  obtain ⟨m26, d26, s26, I6, K26, a026, e26, l26⟩ := partCall (pos := 24) ((d23.trans (.single d24)).trans c25) u25'
    I5 (by decide) (by decide) mp_ac mp_b0 (by decide) mp_b4 (by rw [K25 sp (by decide), sp23]) v25.1 v25.2.1
    v25.2.2.1 v25.2.2.2.1
  have kk26 : ∀ q, q.val ∈ mpK → reg m26 q = reg m q := fun q hq => by
    rw [K26 q (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec), K25 q (by kdec),
      kk23 q hq]
  have K26' : ∀ q, q.val ∈ [8, 2, 9, 20, 18, 19] → reg m26 q = reg m25 q := fun q hq =>
    K26 q (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec) (by kdec)
  have sp26 : reg m26 sp = G := by rw [K26' sp (by decide), K25 sp (by decide), sp23]
  have r8_26 : reg m26 8 = out := by rw [K26' 8 (by decide), K25 8 (by decide), r8_23]
  have s1_26 : reg m26 9 = mw m.mem bp 8 := by rw [K26' 9 (by decide), K25 9 (by decide), s1_23]
  have s4_26 : reg m26 20 = mw m.mem bp 12 := by rw [K26' 20 (by decide), K25 20 (by decide), s4_23]
  have s2_26 : reg m26 18 = mw m.mem bp 16 := by rw [K26' 18 (by decide), v25.2.2.2.2.1]
  have s3_26 : reg m26 19 = mw m.mem bp 20 := by rw [K26' 19 (by decide), v25.2.2.2.2.2]
  cases hp3 : partOut 0x12 0x60000 (mw m.mem bp (24 + 4)) with
  | true =>
    obtain ⟨m27, d27, u27⟩ := s26.notTaken (cdP I6.io) 0xBA mp_b8 (by decide) (by
      simp only [branchTaken]; rw [a026, s26.zero, hp3]; decide)
    have hp3' : partOut 18 0x60000 (mw m.mem bp 28) = true := hp3
    exact finBA (d26.trans (.single d27)) u27.self I6 (by rw [u27.regs, sp26])
      (by rw [u27.regs, r8_26]) (fun q hq => by rw [u27.regs, kk26 q hq]) (e26 hp3)
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3']; rfl)
  | false =>
  obtain ⟨m27, d27, u27⟩ := s26.taken (cdP I6.io) 0xDC mp_b8 (by decide) (by
    simp only [branchTaken]; rw [a026, s26.zero, hp3]; decide)
  have L26 := l26 hp3
  have hp3' : partOut 18 0x60000 (mw m.mem bp 28) = false := hp3
  -- 0xDC: the layout checks
  have hct6 := cdP I6.io
  have ld6 := ld I6
  have z26 := s26.zero
  have ok26 : ∀ {nn : Machine}, (∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg nn q = reg m26 q) →
      reg nn sp = G ∧ reg nn 8 = out ∧ (∀ q, q.val ∈ mpK → reg nn q = reg m q) ∧ reg nn 9 = mw m.mem bp 8 ∧
        reg nn 20 = mw m.mem bp 12 ∧ reg nn 18 = mw m.mem bp 16 ∧ reg nn 19 = mw m.mem bp 20 := fun K =>
    ⟨by rw [K sp (by decide), sp26], by rw [K 8 (by decide), r8_26], fun q hq => by rw [K q (by kdec), kk26 q hq],
      by rw [K 9 (by decide), s1_26], by rw [K 20 (by decide), s4_26], by rw [K 18 (by decide), s2_26],
      by rw [K 19 (by decide), s3_26]⟩
  have P27 : Steps m m27 := d26.trans (.single d27)
  obtain ⟨n1, e1, t1⟩ := St.block mpL1 u27 hct6 mpL1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, mpL1, upd_app, ↓reduceIte, and_true]
    rw [sp26]; exact ⟨hG4, hG8⟩)
  have t1' : St m26.mem MP n1 0xE0 (reg n1) := ⟨t1.pc, by rw [t1.mem]; rfl, fun _ => rfl⟩
  have K1 : ∀ q, q.val ∉ [10, 11] → reg n1 q = reg m26 q := fun q hq => by
    have hd : q ∉ mpL1.filterMap BInstr.dst := by
      simp only [mpL1, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [t1.regs, runBlock_reg _ _ _ q z26 hd]
  have v1 : reg n1 a0 = 0x20 ∧ reg n1 a1 = BitVec.ofNat 32 32 := by
    simp +decide only [t1.regs, runBlock, BInstr.run, mpL1, upd_app, ↓reduceIte]; rw [sp26]; exact ⟨ld6.2.1, ld6.2.2⟩
  obtain ⟨n2, e2, t2⟩ := t1'.notTaken hct6 0xE4 mp_e0 (by decide) (by
    simp only [branchTaken]; rw [v1.1, v1.2]; decide)
  obtain ⟨n3, e3, t3⟩ := St.block mpL2 t2 hct6 mpL2_end ⟨trivial, trivial⟩
  have t3' : St m26.mem MP n3 0xE6 (reg n3) := ⟨t3.pc, by rw [t3.mem]; rfl, fun _ => rfl⟩
  have K3 : ∀ q, q.val ∉ [13] → reg n3 q = reg n1 q := fun q hq => by
    have hd : q ∉ mpL2.filterMap BInstr.dst := by
      simp only [mpL2, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [t3.regs, runBlock_reg _ _ _ q t1'.zero hd]
  have a3_3 : reg n3 a3 = 0x10000 := by simp +decide only [t3.regs, runBlock, BInstr.run, mpL2, upd_app, ↓reduceIte]
  have W3 : ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg n3 q = reg m26 q := fun q hq => by
    rw [K3 q (by kdec), K1 q (by kdec)]
  have o3 := ok26 W3
  have P3 : Steps m n3 := P27.trans (e1.trans (.cons e2 e3))
  by_cases h7 : mw m.mem bp 8 ≠ 0x10000
  · obtain ⟨n4, e4, t4⟩ := t3'.taken hct6 0x13A mp_e6 (by decide) (by
      simp only [branchTaken]; rw [o3.2.2.2.1, a3_3]; exact bne_iff_ne.mpr h7)
    exact fin13A (P3.trans (.single e4)) t4.self I6 (by rw [t4.regs, o3.1]) (by rw [t4.regs, o3.2.1])
      (fun q hq => by rw [t4.regs, o3.2.2.1 q hq])
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3', beq_eq_false_iff_ne.mpr h7]; rfl)
  replace h7 := Decidable.of_not_not h7
  obtain ⟨n4, e4, t4⟩ := t3'.notTaken hct6 0xEA mp_e6 (by decide) (by
    simp only [branchTaken]; rw [o3.2.2.2.1, a3_3, h7]; decide)
  -- 0xEA: the image's length
  obtain ⟨n5, e5, t5⟩ := St.block mpL3 t4 hct6 mpL3_end ⟨trivial, trivial, trivial, trivial⟩
  have t5' : St m26.mem MP n5 0xF2 (reg n5) := ⟨t5.pc, by rw [t5.mem]; rfl, fun _ => rfl⟩
  have K5 : ∀ q, q.val ∉ [10, 11] → reg n5 q = reg n3 q := fun q hq => by
    have hd : q ∉ mpL3.filterMap BInstr.dst := by
      simp only [mpL3, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [t5.regs, runBlock_reg _ _ _ q t3'.zero hd]
  have v5 : reg n5 a0 = 6 ∧ reg n5 a1 = 0xFFFEFFFF := by
    simp +decide only [t5.regs, runBlock, BInstr.run, mpL3, upd_app, ↓reduceIte]
  have W5 : ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg n5 q = reg m26 q := fun q hq => by
    rw [K5 q (by kdec), W3 q hq]
  have o5 := ok26 W5
  have a3_5 : reg n5 a3 = 0x10000 := by rw [K5 a3 (by decide), a3_3]
  have P5 : Steps m n5 := P3.trans (.cons e4 e5)
  cases h6a : (0xFFFEFFFF : Word).ult (mw m.mem bp 12) with
  | true =>
    obtain ⟨n6, e6, t6⟩ := t5'.taken hct6 0xC2 mp_f2 (by decide) (by
      simp only [branchTaken]; rw [v5.2, o5.2.2.2.2.1]; exact h6a)
    exact finC2 (v := 6) (e := 6) (P5.trans (.single e6)) t6.self I6 (by rw [t6.regs, o5.1])
      (by rw [t6.regs, o5.2.1]) (fun q hq => by rw [t6.regs, o5.2.2.1 q hq]) (by rw [t6.regs, v5.1]) (by decide)
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3', h7, h6a]; rfl)
  | false =>
  obtain ⟨n6, e6, t6⟩ := t5'.notTaken hct6 0xF6 mp_f2 (by decide) (by
    simp only [branchTaken]; rw [v5.2, o5.2.2.2.2.1]; exact h6a)
  -- 0xF6: the first slot's end
  obtain ⟨n7, e7, t7⟩ := St.block mpL4 t6 hct6 mpL4_end ⟨trivial, trivial⟩
  have t7' : St m26.mem MP n7 0xFA (reg n7) := ⟨t7.pc, by rw [t7.mem]; rfl, fun _ => rfl⟩
  have K7 : ∀ q, q.val ∉ [14] → reg n7 q = reg n5 q := fun q hq => by
    have hd : q ∉ mpL4.filterMap BInstr.dst := by
      simp only [mpL4, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [t7.regs, runBlock_reg _ _ _ q t5'.zero hd]
  have a4_7 : reg n7 a4 = mw m.mem bp 20 + mw m.mem bp 16 := by
    simp +decide only [t7.regs, runBlock, BInstr.run, mpL4, upd_app, ↓reduceIte]
    rw [o5.2.2.2.2.2.2, o5.2.2.2.2.2.1]; rfl
  have W7 : ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg n7 q = reg m26 q := fun q hq => by
    rw [K7 q (by kdec), W5 q hq]
  have o7 := ok26 W7
  have P7 : Steps m n7 := P5.trans (.cons e6 e7)
  cases h6b : (mw m.mem bp 20 + mw m.mem bp 16).ult (mw m.mem bp 20) with
  | true =>
    obtain ⟨n8, e8, t8⟩ := t7'.taken hct6 0xC2 mp_fa (by decide) (by
      simp only [branchTaken]; rw [a4_7, o7.2.2.2.2.2.2]; exact h6b)
    exact finC2 (v := 6) (e := 6) (P7.trans (.single e8)) t8.self I6 (by rw [t8.regs, o7.1])
      (by rw [t8.regs, o7.2.1]) (fun q hq => by rw [t8.regs, o7.2.2.1 q hq])
      (by rw [t8.regs, K7 a0 (by decide), v5.1]) (by decide)
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3', h7, h6a, h6b]; rfl)
  | false =>
  obtain ⟨n8, e8, t8⟩ := t7'.notTaken hct6 0xFE mp_fa (by decide) (by
    simp only [branchTaken]; rw [a4_7, o7.2.2.2.2.2.2]; exact h6b)
  -- 0xFE: the second slot's end
  obtain ⟨n9, e9, t9⟩ := St.block mpL5 t8 hct6 mpL5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, mpL5, upd_app, ↓reduceIte, and_true]
    rw [o7.1]; exact ⟨aligned_add hGa (by decide), aligned_add hGa (by decide)⟩)
  have t9' : St m26.mem MP n9 0x106 (reg n9) := ⟨t9.pc, by rw [t9.mem]; rfl, fun _ => rfl⟩
  have K9 : ∀ q, q.val ∉ [11, 12, 15] → reg n9 q = reg n7 q := fun q hq => by
    have hd : q ∉ mpL5.filterMap BInstr.dst := by
      simp only [mpL5, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [t9.regs, runBlock_reg _ _ _ q t7'.zero hd]
  have v9 : reg n9 a1 = mw m.mem bp 24 ∧ reg n9 a2 = mw m.mem bp 28 ∧
      reg n9 a5 = mw m.mem bp 28 + mw m.mem bp 24 := by
    simp +decide only [t9.regs, runBlock, BInstr.run, mpL5, upd_app, ↓reduceIte]
    rw [o7.1, L26.1, L26.2]; exact ⟨rfl, rfl, rfl⟩
  have W9 : ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg n9 q = reg m26 q := fun q hq => by
    rw [K9 q (by kdec), W7 q hq]
  have o9 := ok26 W9
  have P9 : Steps m n9 := P7.trans (.cons e8 e9)
  cases h6c : (mw m.mem bp 28 + mw m.mem bp 24).ult (mw m.mem bp 28) with
  | true =>
    obtain ⟨n10, e10, t10⟩ := t9'.taken hct6 0xC2 mp_106 (by decide) (by
      simp only [branchTaken]; rw [v9.2.2, v9.2.1]; exact h6c)
    exact finC2 (v := 6) (e := 6) (P9.trans (.single e10)) t10.self I6 (by rw [t10.regs, o9.1])
      (by rw [t10.regs, o9.2.1]) (fun q hq => by rw [t10.regs, o9.2.2.1 q hq])
      (by rw [t10.regs, K9 a0 (by decide), K7 a0 (by decide), v5.1]) (by decide)
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3', h7, h6a, h6b, h6c]; rfl)
  | false =>
  obtain ⟨n10, e10, t10⟩ := t9'.notTaken hct6 0x10A mp_106 (by decide) (by
    simp only [branchTaken]; rw [v9.2.2, v9.2.1]; exact h6c)
  -- 0x10A: the slots' order
  obtain ⟨n11, e11, t11⟩ := St.block mpL6 t10 hct6 mpL6_end ⟨trivial, trivial⟩
  have t11' : St m26.mem MP n11 0x10C (reg n11) := ⟨t11.pc, by rw [t11.mem]; rfl, fun _ => rfl⟩
  have K11 : ∀ q, q.val ∉ [13] → reg n11 q = reg n9 q := fun q hq => by
    have hd : q ∉ mpL6.filterMap BInstr.dst := by
      simp only [mpL6, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [t11.regs, runBlock_reg _ _ _ q t9'.zero hd]
  have a3_11 : reg n11 a3 = 0x10000 + mw m.mem bp 12 := by
    simp +decide only [t11.regs, runBlock, BInstr.run, mpL6, upd_app, ↓reduceIte]
    rw [K9 a3 (by decide), K7 a3 (by decide), a3_5, o9.2.2.2.2.1]; rfl
  have W11 : ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg n11 q = reg m26 q := fun q hq => by
    rw [K11 q (by kdec), W9 q hq]
  have o11 := ok26 W11
  have P11 : Steps m n11 := P9.trans (.cons e10 e11)
  cases h7b : (mw m.mem bp 16).ult (0x10000 + mw m.mem bp 12) with
  | true =>
    obtain ⟨n12, e12, t12⟩ := t11'.taken hct6 0x13A mp_10c (by decide) (by
      simp only [branchTaken]; rw [o11.2.2.2.2.2.1, a3_11]; exact h7b)
    exact fin13A (P11.trans (.single e12)) t12.self I6 (by rw [t12.regs, o11.1]) (by rw [t12.regs, o11.2.1])
      (fun q hq => by rw [t12.regs, o11.2.2.1 q hq])
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3', h7, h6a, h6b, h6c, h7b]; rfl)
  | false =>
  obtain ⟨n12, e12, t12⟩ := t11'.notTaken hct6 0x110 mp_10c (by decide) (by
    simp only [branchTaken]; rw [o11.2.2.2.2.2.1, a3_11]; exact h7b)
  have a1_11 : reg n11 a1 = mw m.mem bp 24 := by rw [K11 a1 (by decide), v9.1]
  have a4_11 : reg n11 a4 = mw m.mem bp 20 + mw m.mem bp 16 := by
    rw [K11 a4 (by decide), K9 a4 (by decide), a4_7]
  cases h7c : (mw m.mem bp 24).ult (mw m.mem bp 20 + mw m.mem bp 16) with
  | true =>
    obtain ⟨n13, e13, t13⟩ := t12.taken hct6 0x13A mp_110 (by decide) (by
      simp only [branchTaken]; rw [a1_11, a4_11]; exact h7c)
    exact fin13A (P11.trans (.cons e12 (.single e13))) t13.self I6 (by rw [t13.regs, o11.1])
      (by rw [t13.regs, o11.2.1]) (fun q hq => by rw [t13.regs, o11.2.2.1 q hq])
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3', h7, h6a, h6b, h6c, h7b, h7c]; rfl)
  | false =>
  obtain ⟨n13, e13, t13⟩ := t12.notTaken hct6 0x114 mp_110 (by decide) (by
    simp only [branchTaken]; rw [a1_11, a4_11]; exact h7c)
  -- 0x114: the end of flash
  obtain ⟨n14, e14, t14⟩ := St.block mpL7 t13 hct6 mpL7_end ⟨trivial, trivial, trivial⟩
  have t14' : St m26.mem MP n14 0x11A (reg n14) := ⟨t14.pc, by rw [t14.mem]; rfl, fun _ => rfl⟩
  have K14 : ∀ q, q.val ∉ [10, 13] → reg n14 q = reg n11 q := fun q hq => by
    have hd : q ∉ mpL7.filterMap BInstr.dst := by
      simp only [mpL7, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [t14.regs, runBlock_reg _ _ _ q t11'.zero hd]
  have v14 : reg n14 a0 = 7 ∧ reg n14 a3 = 0x1E0000 := by
    simp +decide only [t14.regs, runBlock, BInstr.run, mpL7, upd_app, ↓reduceIte]
  have a5_14 : reg n14 a5 = mw m.mem bp 28 + mw m.mem bp 24 := by
    rw [K14 a5 (by decide), K11 a5 (by decide), v9.2.2]
  have W14 : ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg n14 q = reg m26 q := fun q hq => by
    rw [K14 q (by kdec), W11 q hq]
  have o14 := ok26 W14
  have P14 : Steps m n14 := P11.trans (.cons e12 (.cons e13 e14))
  cases h7d : (0x1E0000 : Word).ult (mw m.mem bp 28 + mw m.mem bp 24) with
  | true =>
    obtain ⟨n15, e15, t15⟩ := t14'.taken hct6 0xC2 mp_11a (by decide) (by
      simp only [branchTaken]; rw [v14.2, a5_14]; exact h7d)
    exact finC2 (v := 7) (e := 7) (P14.trans (.single e15)) t15.self I6 (by rw [t15.regs, o14.1])
      (by rw [t15.regs, o14.2.1]) (fun q hq => by rw [t15.regs, o14.2.2.1 q hq]) (by rw [t15.regs, v14.1])
      (by decide)
      (by unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3', h7, h6a, h6b, h6c, h7b, h7c, h7d]; rfl)
  | false =>
  obtain ⟨n15, e15, t15⟩ := t14'.notTaken hct6 0x11E mp_11a (by decide) (by
    simp only [branchTaken]; rw [v14.2, a5_14]; exact h7d)
  have hnone : parseErrV2 m.mem bp = none := by
    unfold parseErrV2; rw [hm, hVe, hz, hp1', hp2', hp3', h7, h6a, h6b, h6c, h7b, h7c, h7d]; rfl
  -- 0x11E: the result
  have a1_14 : reg n14 a1 = mw m.mem bp 24 := by rw [K14 a1 (by decide), a1_11]
  have a2_14 : reg n14 a2 = mw m.mem bp 28 := by rw [K14 a2 (by decide), K11 a2 (by decide), v9.2.1]
  obtain ⟨Mo, hMo⟩ : ∃ Mo, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 m26.mem
      (out + BitVec.ofNat 32 4) 0x10000) (out + BitVec.ofNat 32 8) (mw m.mem bp 12))
      (out + BitVec.ofNat 32 0xC) (mw m.mem bp 16)) (out + BitVec.ofNat 32 0x10) (mw m.mem bp 20))
      (out + BitVec.ofNat 32 0x14) (mw m.mem bp 24)) (out + BitVec.ofNat 32 0x18) (mw m.mem bp 28) = Mo := ⟨_, rfl⟩
  obtain ⟨n16, e16, t16⟩ := St.block mpOk t15 hct6 mpOk_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, mpOk, upd_app, ↓reduceIte, and_true, true_and]
    rw [o14.2.1]
    exact ⟨⟨aligned_add hoa (by decide), sOC (c := 4) (l := 4) (by decide)⟩,
      ⟨aligned_add hoa (by decide), sOC (c := 8) (l := 4) (by decide)⟩,
      ⟨aligned_add hoa (by decide), sOC (c := 0xC) (l := 4) (by decide)⟩,
      ⟨aligned_add hoa (by decide), sOC (c := 0x10) (l := 4) (by decide)⟩,
      ⟨aligned_add hoa (by decide), sOC (c := 0x14) (l := 4) (by decide)⟩,
      aligned_add hoa (by decide), sOC (c := 0x18) (l := 4) (by decide)⟩)
  have eMo : (runBlock mpOk (m26.mem, reg n14)).1 = Mo := by
    simp +decide only [runBlock, BInstr.run, mpOk, upd_app, ↓reduceIte]
    rw [o14.2.1, o14.2.2.2.2.1, o14.2.2.2.2.2.1, o14.2.2.2.2.2.2, a1_14, a2_14]; exact hMo
  have hcto : CodeIn Mo MP manifestParseCode := by
    rw [← hMo]
    exact (((((hct6.store32 (sOC (c := 4) (l := 4) (by decide))).store32 (sOC (c := 8) (l := 4) (by decide))).store32
      (sOC (c := 0xC) (l := 4) (by decide))).store32 (sOC (c := 0x10) (l := 4) (by decide))).store32
      (sOC (c := 0x14) (l := 4) (by decide))).store32 (sOC (c := 0x18) (l := 4) (by decide))
  have t16' : St Mo MP n16 0x134 (reg n16) := ⟨t16.pc, by rw [t16.mem, eMo], fun _ => rfl⟩
  have K16 : ∀ q, q.val ∉ [10, 13] → reg n16 q = reg n14 q := fun q hq => by
    have hd : q ∉ mpOk.filterMap BInstr.dst := by
      simp only [mpOk, List.filterMap_cons, List.filterMap_nil, BInstr.dst]; revert hq; revert q; decide
    rw [t16.regs, runBlock_reg _ _ _ q t14'.zero hd]
  have a0_16 : reg n16 a0 = 0 := by
    simp +decide only [t16.regs, runBlock, BInstr.run, mpOk, upd_app, ↓reduceIte]
    rw [t14'.zero]; rfl
  have W16 : ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg n16 q = reg m26 q := fun q hq => by
    rw [K16 q (by kdec), W14 q hq]
  have o16 := ok26 W16
  obtain ⟨n17, e17, t17⟩ := t16'.jump hcto mp_134 (off' := 0xC8) (by decide) (by rw [t16'.pc]; decide)
  have sOH : ∀ {k c' : Nat}, k + 4 ≤ 28 → 0x68 ≤ c' → c' < 0x80 →
      Sep (out + BitVec.ofNat 32 k) 4 (H + BitVec.ofNat 32 c') 1 :=
    fun h h1 h2 => (sOS.sub h).subR (by omega)
  obtain ⟨nn, cn, pcn, spn, Kn, memn⟩ := tailC8 (v := 0) t17.self hcto (by rw [t17.regs, o16.1])
    (by rw [t17.regs, o16.2.1]) (by rw [t17.regs, a0_16])
    (fun c' h1 h2 => by
      rw [← hMo, memStore32_get_sep (sOH (by decide) h1 h2), memStore32_get_sep (sOH (by decide) h1 h2),
        memStore32_get_sep (sOH (by decide) h1 h2), memStore32_get_sep (sOH (by decide) h1 h2),
        memStore32_get_sep (sOH (by decide) h1 h2), memStore32_get_sep (sOH (by decide) h1 h2), I6.ss c' h1 h2])
    (fun q hq => by rw [t17.regs, o16.2.2.1 q hq])
  refine ⟨nn, P14.trans (.cons e15 (e16.trans (.cons e17 cn))), pcn, spn, Kn, fun x hx => ?_⟩
  rw [memn, show ((0 : Word).extractLsb' 0 8) = (0 : BitVec 8) by decide, ← hMo]
  simp only [parseMemV2, hnone]
  exact memStore8_congr (memStore32_congr (memStore32_congr (memStore32_congr (memStore32_congr
    (memStore32_congr (memStore32_congr (I6.io x hx)))))))

end C3.RV32.Cur
