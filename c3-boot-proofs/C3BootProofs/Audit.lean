import C3BootProofs.Theorems.TrustRoot
import C3BootProofs.Theorems.Formats
import C3BootProofs.Proofs.Crc32
import C3BootProofs.Proofs.Reader
import C3BootProofs.Proofs.ReaderArray
import C3BootProofs.Proofs.ReaderU32
import C3BootProofs.Proofs.Part
import C3BootProofs.Proofs.Reserved
import C3BootProofs.Proofs.Parse

/-!
# Audit

Each theorem's axioms are pinned, so a proof that comes to depend on
`sorryAx` or a new axiom fails the build. The non-vacuity theorem shows that
the trace theorems' hypotheses can hold together with a jump.
-/

namespace C3

/-- Admissible traces with a jump exist, so `rollback` and `boots_safe` are
not vacuous. -/
theorem exists_admissible_jump :
    ∃ (es : List Event) (j : Nat) (hj : j < es.length) (slot : Slot) (l : Nat),
      Admissible es ∧ (es[j]'hj).jump = some (slot, l) := by
  let d : Device := ⟨Fuses.ofNat 0, State.default, fun _ => some 1⟩
  have h : ∃ slot l, accepted d.slots (level d.fuses) slot = some l :=
    ⟨.a, 1, by decide⟩
  obtain ⟨d', slot, l, hs⟩ := availability d h
  refine ⟨[⟨d, d', some (slot, l)⟩], 0, by simp, slot, l, ⟨?_, ?_⟩, rfl⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact hs
  · intro i hi
    simp at hi

/-- A trace whose slot results come from flash contents that pass the
trust-root checks can jump, so `trust_root_monotone`'s hypotheses can hold
together. The verifier here accepts every signature; the differential test
exercises the signature rules. -/
theorem exists_trust_root_jump :
    ∃ (es : List Event) (flash : Nat → Slot → Option (Contents Nat Unit Unit)),
      Admissible es ∧
      (∀ (j : Nat) (hj : j < es.length),
        (es[j]'hj).before.slots = slotsOf (fun _ _ _ => true) [0, 1] (flash j)) ∧
      ∃ (j : Nat) (hj : j < es.length) (slot : Slot) (l : Nat),
        (es[j]'hj).jump = some (slot, l) := by
  let c : Contents Nat Unit Unit := ⟨[], ⟨0, (), [⟨0, ()⟩, ⟨1, ()⟩]⟩, 0, true⟩
  let fl : Slot → Option (Contents Nat Unit Unit) := fun _ => some c
  let d : Device := ⟨Fuses.ofNat 0, State.default, slotsOf (fun _ _ _ => true) [0, 1] fl⟩
  have h : ∃ slot l, accepted d.slots (level d.fuses) slot = some l := ⟨.a, 0, by decide⟩
  obtain ⟨d', slot, l, hs⟩ := availability d h
  refine ⟨[⟨d, d', some (slot, l)⟩], fun _ => fl, ⟨?_, ?_⟩, ?_, 0, by simp, slot, l, rfl⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact hs
  · intro i hi
    simp at hi
  · intro j hj
    have : j = 0 := by simp at hj; omega
    subst this
    rfl

/-- The bytes of a header with one flash code segment. -/
def flashHeaderBytes : Bytes :=
  [67, 51, 73, 77, 1, 0, 5, 0, 0, 1, 0, 0, 0, 0, 0, 66, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 66, 0, 0, 1, 0, 0, 0, 1, 0]

/-- A header with one flash code segment decodes, so the image-header
theorems are not vacuous. -/
theorem exists_flash_header :
    ∃ (bytes : Bytes) (n : Nat) (h : ImageHeader), decodeImageHeader bytes n = some h ∧
      ∃ s ∈ h.segments, s.kind.isFlash = true := by
  have hd : decodeImageHeader flashHeaderBytes 0x20000 =
      some ⟨0, 0x42000000, 0x20000, [⟨.flashCode, 0x42000000, 0x10000, 0x10000⟩]⟩ := by
    decide +kernel
  exact ⟨_, _, _, hd, ⟨.flashCode, 0x42000000, 0x10000, 0x10000⟩, by simp, rfl⟩

/-- A machine with `crc32`'s bytes at the address the image loads them
meets `crc32_correct`'s hypotheses, so the theorem is not vacuous. -/
theorem exists_crc32_machine :
    ∃ (m : RV32.Machine) (base retAddr : RV32.Word), RV32.CodeAt m base Image.crc32Code ∧
      m.pc = base ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let base : RV32.Word := BitVec.ofNat 32 Image.crc32Address
  refine ⟨⟨fun _ => 0, base, fun a => RV32.byteAt Image.crc32Code (a - base).toNat⟩, base, 0,
    ?_, rfl, rfl, by decide⟩
  intro i hi
  have hi' : i < 2 ^ 32 := Nat.lt_trans hi (by decide)
  show RV32.byteAt Image.crc32Code (base + BitVec.ofNat 32 i - base).toNat = _
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']

/-- A machine with `Reader::bytes`'s bytes at the address the image loads
them, and a result and reader in data memory, meets `readerBytes_correct`'s
hypotheses. -/
theorem exists_readerBytes_machine :
    ∃ (m : RV32.Machine) (base retAddr out self n : RV32.Word),
      RV32.CodeAt m base Image.readerBytesCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = self ∧ RV32.reg m RV32.a2 = n ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ out.toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      RV32.Sep out 8 base Image.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base Image.readerBytesCode.length := by
  let base : RV32.Word := BitVec.ofNat 32 Image.readerBytesAddress
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else 0
  refine ⟨⟨regs, base, fun a => RV32.byteAt Image.readerBytesCode (a - base).toNat⟩, base, 0,
    0x3FCC5000, 0x3FCC5100, 0, ?_, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by unfold RV32.Sep; decide, by unfold RV32.Sep; decide⟩
  intro i hi
  have hi' : i < 2 ^ 32 := Nat.lt_trans hi (by decide)
  show RV32.byteAt Image.readerBytesCode (base + BitVec.ofNat 32 i - base).toNat = _
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']

/-- The reader the `Reader::array::<4>` witness uses: a 16-byte slice at
`0x3FCC6000`, at position 0. -/
def witnessReader : List Nat := [0x00, 0x60, 0xCC, 0x3F, 16, 0, 0, 0, 0, 0, 0, 0]

/-- Memory with `Reader::array::<4>` and `Reader::bytes` where the image
loads them and the witness reader at `0x3FCC5100`. -/
def witnessMem (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 Image.readerArray4Address).toNat < 70 then
    RV32.byteAt Image.readerArray4Code (a - BitVec.ofNat 32 Image.readerArray4Address).toNat
  else if (a - BitVec.ofNat 32 Image.readerBytesAddress).toNat < 38 then
    RV32.byteAt Image.readerBytesCode (a - BitVec.ofNat 32 Image.readerBytesAddress).toNat
  else if (a - 0x3FCC5100).toNat < 12 then RV32.byteAt witnessReader (a - 0x3FCC5100).toNat
  else 0

/-- A machine that calls `Reader::array::<4>` on the witness reader, with
the stack at `0x3FCC8000`, meets `readerArray4_correct`'s hypotheses. -/
theorem exists_readerArray4_machine :
    ∃ (m : RV32.Machine) (base bbase retAddr out self : RV32.Word),
      RV32.CodeAt m base Image.readerArray4Code ∧ RV32.CodeAt m bbase Image.readerBytesCode ∧
      bbase = base + 0xFFFFFF96 ∧ base.toNat % 2 = 0 ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = self ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧
      self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 base Image.readerArray4Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 bbase Image.readerBytesCode.length ∧
      RV32.Sep out 8 base Image.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 base Image.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 bbase Image.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 ∧
      RV32.Sep out 8 (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.readerArray4Address, witnessMem⟩,
    BitVec.ofNat 32 Image.readerArray4Address, BitVec.ofNat 32 Image.readerBytesAddress, 0,
    0x3FCC5000, 0x3FCC5100, ?_, ?_, by decide, by decide, rfl, rfl, rfl, rfl, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RV32.CodeAt; decide +kernel
  · unfold RV32.CodeAt; decide +kernel
  · decide +kernel
  all_goals (unfold RV32.Sep; decide +kernel)

/-- `witnessMem` with `Reader::u32` added where the image loads it. -/
def witnessMemU32 (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 Image.readerU32Address).toNat < 80 then
    RV32.byteAt Image.readerU32Code (a - BitVec.ofNat 32 Image.readerU32Address).toNat
  else witnessMem a

/-- A machine that calls `Reader::u32` on the witness reader meets
`readerU32_correct`'s hypotheses. -/
theorem exists_readerU32_machine :
    ∃ (m : RV32.Machine) (base retAddr out self : RV32.Word),
      RV32.CodeAt m base Image.readerU32Code ∧
      RV32.CodeAt m (base + 0xFFFFFEFE) Image.readerArray4Code ∧
      RV32.CodeAt m (base + 0xFFFFFEFE + 0xFFFFFF96) Image.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = self ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 base Image.readerU32Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0xFFFFFEFE) Image.readerArray4Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0xFFFFFEFE + 0xFFFFFF96)
        Image.readerBytesCode.length ∧
      RV32.Sep out 8 base Image.readerU32Code.length ∧
      RV32.Sep (self + 8) 4 base Image.readerU32Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xFFFFFEFE) Image.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xFFFFFEFE + 0xFFFFFF96) Image.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep out 8 (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.readerU32Address, witnessMemU32⟩,
    BitVec.ofNat 32 Image.readerU32Address, 0, 0x3FCC5000, 0x3FCC5100, ?_, ?_, ?_, by decide, rfl,
    rfl, rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; decide +kernel)
    | (unfold RV32.Sep; decide +kernel)
    | decide +kernel

/-- `witnessMemU32` with `Reader::magic` and its load helper, `Reader::u16`,
`Reader::version_1`, and `Reader::reserved` added where the image loads
them. -/
def witnessMemChecks (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 Image.readerMagicAddress).toNat < Image.readerMagicCode.length then
    RV32.byteAt Image.readerMagicCode (a - BitVec.ofNat 32 Image.readerMagicAddress).toNat
  else if (a - BitVec.ofNat 32 Image.magicLoadAddress).toNat < Image.magicLoadCode.length then
    RV32.byteAt Image.magicLoadCode (a - BitVec.ofNat 32 Image.magicLoadAddress).toNat
  else if (a - BitVec.ofNat 32 Image.readerU16Address).toNat < Image.readerU16Code.length then
    RV32.byteAt Image.readerU16Code (a - BitVec.ofNat 32 Image.readerU16Address).toNat
  else if (a - BitVec.ofNat 32 Image.readerVersion1Address).toNat < Image.readerVersion1Code.length then
    RV32.byteAt Image.readerVersion1Code (a - BitVec.ofNat 32 Image.readerVersion1Address).toNat
  else if (a - BitVec.ofNat 32 Image.readerReservedAddress).toNat < Image.readerReservedCode.length then
    RV32.byteAt Image.readerReservedCode (a - BitVec.ofNat 32 Image.readerReservedAddress).toNat
  else witnessMemU32 a

/-- The registers of a call on the witness reader with the stack at
`0x3FCC8000`, with `a1` set to `a1v`. -/
def witnessRegs (a1v : RV32.Word) (r : Fin 32) : RV32.Word :=
  if r = RV32.a0 then 0x3FCC5100 else if r = RV32.a1 then a1v
  else if r = RV32.sp then 0x3FCC8000 else 0

/-- A machine that calls `Reader::magic` on the witness reader meets
`readerMagic_correct`'s hypotheses. -/
theorem exists_readerMagic_machine :
    ∃ (m : RV32.Machine) (base retAddr self k : RV32.Word),
      RV32.CodeAt m base Image.readerMagicCode ∧
      RV32.CodeAt m (base + 0x1AC) Image.readerArray4Code ∧
      RV32.CodeAt m (base + 0x1AC + 0xFFFFFF96) Image.readerBytesCode ∧
      RV32.CodeAt m (base + 0x163CA) Image.magicLoadCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧ RV32.reg m RV32.a1 = k ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 base Image.readerMagicCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x1AC) Image.readerArray4Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x1AC + 0xFFFFFF96)
        Image.readerBytesCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x163CA) Image.magicLoadCode.length ∧
      RV32.Sep (self + 8) 4 base Image.readerMagicCode.length ∧
      RV32.Sep (self + 8) 4 (base + 0x1AC) Image.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0x1AC + 0xFFFFFF96) Image.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 (base + 0x163CA) Image.magicLoadCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 0x4C533343, BitVec.ofNat 32 Image.readerMagicAddress, witnessMemChecks⟩,
    BitVec.ofNat 32 Image.readerMagicAddress, 0, 0x3FCC5100, 0x4C533343, ?_, ?_, ?_, ?_, by decide, rfl,
    rfl, rfl, rfl, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; decide +kernel)
    | (unfold RV32.Sep; decide +kernel)
    | decide +kernel

/-- A machine that calls `Reader::u16` on the witness reader meets
`readerU16_correct`'s hypotheses. -/
theorem exists_readerU16_machine :
    ∃ (m : RV32.Machine) (base retAddr self : RV32.Word),
      RV32.CodeAt m base Image.readerU16Code ∧
      RV32.CodeAt m (base + 0xFFFFFFDA) Image.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 base Image.readerU16Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 (base + 0xFFFFFFDA) Image.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base Image.readerU16Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xFFFFFFDA) Image.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 0, BitVec.ofNat 32 Image.readerU16Address, witnessMemChecks⟩,
    BitVec.ofNat 32 Image.readerU16Address, 0, 0x3FCC5100, ?_, ?_, by decide, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; decide +kernel)
    | (unfold RV32.Sep; decide +kernel)
    | decide +kernel

/-- A machine that calls `Reader::version_1` on the witness reader meets
`readerVersion1_correct`'s hypotheses. -/
theorem exists_readerVersion1_machine :
    ∃ (m : RV32.Machine) (base retAddr self : RV32.Word),
      RV32.CodeAt m base Image.readerVersion1Code ∧
      RV32.CodeAt m (base + 0x126) Image.readerU16Code ∧
      RV32.CodeAt m (base + 0x126 + 0xFFFFFFDA) Image.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 base Image.readerVersion1Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 (base + 0x126) Image.readerU16Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 (base + 0x126 + 0xFFFFFFDA)
        Image.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base Image.readerVersion1Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0x126) Image.readerU16Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0x126 + 0xFFFFFFDA) Image.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 0, BitVec.ofNat 32 Image.readerVersion1Address, witnessMemChecks⟩,
    BitVec.ofNat 32 Image.readerVersion1Address, 0, 0x3FCC5100, ?_, ?_, ?_, by decide, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; decide +kernel)
    | (unfold RV32.Sep; decide +kernel)
    | decide +kernel

/-- A machine that calls `Reader::reserved` for 2 bytes on the witness
reader meets `readerReserved_correct`'s hypotheses. -/
theorem exists_readerReserved_machine :
    ∃ (m : RV32.Machine) (base retAddr self n : RV32.Word),
      RV32.CodeAt m base Image.readerReservedCode ∧
      RV32.CodeAt m (base + 0x9C) Image.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧ RV32.reg m RV32.a1 = n ∧
      n ≠ 0 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 base Image.readerReservedCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 (base + 0x9C) Image.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base Image.readerReservedCode.length ∧
      RV32.Sep (self + 8) 4 (base + 0x9C) Image.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 2, BitVec.ofNat 32 Image.readerReservedAddress, witnessMemChecks⟩,
    BitVec.ofNat 32 Image.readerReservedAddress, 0, 0x3FCC5100, 2, ?_, ?_, by decide, rfl, rfl, rfl,
    by decide, rfl, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; decide +kernel)
    | (unfold RV32.Sep; decide +kernel)
    | decide +kernel


/-- `witnessMemU32` with `manifest::part` and its save and restore helpers added
where the image loads them. -/
def witnessMemPart (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 Image.manifestPartAddress).toNat < 106 then
    RV32.byteAt Image.manifestPartCode (a - BitVec.ofNat 32 Image.manifestPartAddress).toNat
  else if (a - BitVec.ofNat 32 Image.partSaveAddress).toNat < 12 then
    RV32.byteAt Image.partSaveCode (a - BitVec.ofNat 32 Image.partSaveAddress).toNat
  else if (a - BitVec.ofNat 32 Image.partRestoreAddress).toNat < 14 then
    RV32.byteAt Image.partRestoreCode (a - BitVec.ofNat 32 Image.partRestoreAddress).toNat
  else witnessMemU32 a

/-- A machine that calls `manifest::part` on the witness reader with the
image's bounds meets `manifestPart_correct`'s hypotheses. -/
theorem exists_manifestPart_machine :
    ∃ (m : RV32.Machine) (base retAddr out self lo hi : RV32.Word),
      RV32.CodeAt m base Image.manifestPartCode ∧
      RV32.CodeAt m (base + 0x12BCE) Image.partSaveCode ∧
      RV32.CodeAt m (base + 0x12A2C) Image.partRestoreCode ∧
      RV32.CodeAt m (base + 0xFFFFC94E) Image.readerU32Code ∧
      RV32.CodeAt m (base + 0xFFFFC94E + 0xFFFFFEFE) Image.readerArray4Code ∧
      RV32.CodeAt m (base + 0xFFFFC94E + 0xFFFFFEFE + 0xFFFFFF96) Image.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = self ∧ RV32.reg m RV32.a2 = lo ∧
      RV32.reg m RV32.a3 = hi ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFB0) 80 (RV32.partWindow base) RV32.partWindowLen ∧
      RV32.Sep out 12 (RV32.partWindow base) RV32.partWindowLen ∧
      RV32.Sep (self + 8) 4 (RV32.partWindow base) RV32.partWindowLen ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFB0) 80 ∧
      RV32.Sep out 12 (RV32.reg m RV32.sp + 0xFFFFFFB0) 80 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFB0) 80 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100
    else if r = RV32.a2 then 37 else if r = RV32.a3 then 0x1D0000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.manifestPartAddress, witnessMemPart⟩,
    BitVec.ofNat 32 Image.manifestPartAddress, 0, 0x3FCC5000, 0x3FCC5100, 37, 0x1D0000,
    ?_, ?_, ?_, ?_, ?_, ?_, by decide, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, ?_, RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; decide +kernel)
    | (unfold RV32.Sep; decide +kernel)
    | decide +kernel


/-- `witnessMemChecks` with `manifest::parse`, its helpers, and `part` and its
helpers added where the image loads them. -/
def witnessMemParse (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 Image.manifestParseAddress).toNat < Image.manifestParseCode.length then
    RV32.byteAt Image.manifestParseCode (a - BitVec.ofNat 32 Image.manifestParseAddress).toNat
  else if (a - BitVec.ofNat 32 Image.parseSaveAddress).toNat < Image.parseSaveCode.length then
    RV32.byteAt Image.parseSaveCode (a - BitVec.ofNat 32 Image.parseSaveAddress).toNat
  else if (a - BitVec.ofNat 32 Image.parseRestoreAddress).toNat < Image.parseRestoreCode.length then
    RV32.byteAt Image.parseRestoreCode (a - BitVec.ofNat 32 Image.parseRestoreAddress).toNat
  else if (a - BitVec.ofNat 32 Image.manifestPartAddress).toNat < 106 then
    RV32.byteAt Image.manifestPartCode (a - BitVec.ofNat 32 Image.manifestPartAddress).toNat
  else if (a - BitVec.ofNat 32 Image.partSaveAddress).toNat < 12 then
    RV32.byteAt Image.partSaveCode (a - BitVec.ofNat 32 Image.partSaveAddress).toNat
  else if (a - BitVec.ofNat 32 Image.partRestoreAddress).toNat < 14 then
    RV32.byteAt Image.partRestoreCode (a - BitVec.ofNat 32 Image.partRestoreAddress).toNat
  else witnessMemChecks a

/-- A machine that calls `manifest::parse` on 40 bytes at `0x3FCC6000`, with
the result at `0x3FCC5000` and the stack at `0x3FCC8000`, meets
`manifestParse_correct`'s hypotheses. -/
theorem exists_manifestParse_machine :
    ∃ (m : RV32.Machine) (P retAddr out bp R G : RV32.Word),
      RV32.PCode m.mem P ∧ m.pc = P ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = bp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x40 ∧
      RV32.PEnv P R G bp out := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.manifestParseAddress, witnessMemParse⟩,
    BitVec.ofNat 32 Image.manifestParseAddress, 0, 0x3FCC5000, 0x3FCC6000, 0x3FCC7F70, 0x3FCC7FC0,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, by decide, by decide,
    ⟨by decide, by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩⟩
  all_goals (unfold RV32.CodeIn; decide +kernel)

end C3

/-- info: 'C3.efuse_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.efuse_monotone

/-- info: 'C3.rollback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.rollback

/-- info: 'C3.boots_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.boots_safe

/-- info: 'C3.availability' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.availability

/-- info: 'C3.exists_admissible_jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_admissible_jump

/-- info: 'C3.trust_root_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.trust_root_monotone

/-- info: 'C3.exists_trust_root_jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_trust_root_jump

/-- info: 'C3.mapped_pages_signed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.mapped_pages_signed

/-- info: 'C3.exists_flash_header' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.exists_flash_header

/-- info: 'C3.RV32.crc32_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.crc32_correct

/-- info: 'C3.RV32.crc32_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.crc32_spec

/-- info: 'C3.exists_crc32_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_crc32_machine

/-- info: 'C3.RV32.readerBytes_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readerBytes_correct

/-- info: 'C3.RV32.bytesResult_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bytesResult_eq

/-- info: 'C3.exists_readerBytes_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_readerBytes_machine

/-- info: 'C3.RV32.readerArray4_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readerArray4_correct

/-- info: 'C3.exists_readerArray4_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_readerArray4_machine

/-- info: 'C3.RV32.readerU32_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readerU32_correct

/-- info: 'C3.exists_readerU32_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_readerU32_machine

/-- info: 'C3.RV32.save_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.save_run

/-- info: 'C3.RV32.restore_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.restore_run

/-- info: 'C3.RV32.St.callSave' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.St.callSave

/-- info: 'C3.RV32.St.callRestore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.St.callRestore

/-- info: 'C3.RV32.part_call_u32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.part_call_u32

/-- info: 'C3.RV32.manifestPart_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.manifestPart_correct

/-- info: 'C3.exists_manifestPart_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_manifestPart_machine

/-- info: 'C3.RV32.magicLoad_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.magicLoad_correct

/-- info: 'C3.RV32.readerMagic_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readerMagic_correct

/-- info: 'C3.exists_readerMagic_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_readerMagic_machine

/-- info: 'C3.RV32.readerU16_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readerU16_correct

/-- info: 'C3.exists_readerU16_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_readerU16_machine

/-- info: 'C3.RV32.readerVersion1_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readerVersion1_correct

/-- info: 'C3.exists_readerVersion1_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_readerVersion1_machine

/-- info: 'C3.RV32.reserved_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.reserved_loop

/-- info: 'C3.RV32.readerReserved_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readerReserved_correct

/-- info: 'C3.exists_readerReserved_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_readerReserved_machine

/-- info: 'C3.RV32.manifestParse_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.manifestParse_correct

/-- info: 'C3.exists_manifestParse_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_manifestParse_machine
