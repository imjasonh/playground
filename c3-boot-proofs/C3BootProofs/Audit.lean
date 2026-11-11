import C3BootProofs.Theorems.TrustRoot
import C3BootProofs.Theorems.Formats
import C3BootProofs.Proofs.Crc32
import C3BootProofs.Proofs.Reader
import C3BootProofs.Proofs.ReaderArray
import C3BootProofs.Proofs.ReaderU32
import C3BootProofs.Proofs.Part
import C3BootProofs.Proofs.Reserved
import C3BootProofs.Proofs.Parse
import C3BootProofs.Proofs.ParseSpec
import C3BootProofs.Proofs.ImageHelpers
import C3BootProofs.Proofs.Block
import C3BootProofs.Proofs.ImageCalls
import C3BootProofs.Proofs.ImageTop
import C3BootProofs.Proofs.ImageSpecSegs
import C3BootProofs.Proofs.Memset
import C3BootProofs.Proofs.FieldSub
import C3BootProofs.Proofs.FieldArith
import C3BootProofs.Proofs.FieldSubInnerMain
import C3BootProofs.Proofs.FieldWideMulMain

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
      RV32.CodeAt m (base + 0xFFFFFADE) Image.readerArray4Code ∧
      RV32.CodeAt m (base + 0xFFFFFADE + 0xFFFFFF96) Image.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = self ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 base Image.readerU32Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0xFFFFFADE) Image.readerArray4Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0xFFFFFADE + 0xFFFFFF96)
        Image.readerBytesCode.length ∧
      RV32.Sep out 8 base Image.readerU32Code.length ∧
      RV32.Sep (self + 8) 4 base Image.readerU32Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xFFFFFADE) Image.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xFFFFFADE + 0xFFFFFF96) Image.readerBytesCode.length ∧
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
      RV32.CodeAt m (base + 0x16804) Image.magicLoadCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧ RV32.reg m RV32.a1 = k ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 base Image.readerMagicCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x1AC) Image.readerArray4Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x1AC + 0xFFFFFF96)
        Image.readerBytesCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x16804) Image.magicLoadCode.length ∧
      RV32.Sep (self + 8) 4 base Image.readerMagicCode.length ∧
      RV32.Sep (self + 8) 4 (base + 0x1AC) Image.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0x1AC + 0xFFFFFF96) Image.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 (base + 0x16804) Image.magicLoadCode.length ∧
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
      RV32.CodeAt m (base + 0x12BB6) Image.partSaveCode ∧
      RV32.CodeAt m (base + 0x129F4) Image.partRestoreCode ∧
      RV32.CodeAt m (base + 0xFFFFC94C) Image.readerU32Code ∧
      RV32.CodeAt m (base + 0xFFFFC94C + 0xFFFFFADE) Image.readerArray4Code ∧
      RV32.CodeAt m (base + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96) Image.readerBytesCode ∧
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

/-- `witnessMemParse` with `Reader::u8`, `Segment::physical`, and `memcpy`'s
stub and body added where the image loads them. -/
def witnessMemImage (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 Image.readerU8Address).toNat < Image.readerU8Code.length then
    RV32.byteAt Image.readerU8Code (a - BitVec.ofNat 32 Image.readerU8Address).toNat
  else if (a - BitVec.ofNat 32 Image.segmentPhysicalAddress).toNat < Image.segmentPhysicalCode.length then
    RV32.byteAt Image.segmentPhysicalCode (a - BitVec.ofNat 32 Image.segmentPhysicalAddress).toNat
  else if (a - BitVec.ofNat 32 Image.memcpyStubAddress).toNat < Image.memcpyStubCode.length then
    RV32.byteAt Image.memcpyStubCode (a - BitVec.ofNat 32 Image.memcpyStubAddress).toNat
  else if (a - BitVec.ofNat 32 Image.memcpyBodyAddress).toNat < Image.memcpyBodyCode.length then
    RV32.byteAt Image.memcpyBodyCode (a - BitVec.ofNat 32 Image.memcpyBodyAddress).toNat
  else witnessMemParse a

/-- A machine that calls `Reader::u8` on the witness reader meets
`readerU8_correct`'s hypotheses. -/
theorem exists_readerU8_machine :
    ∃ (m : RV32.Machine) (base retAddr self : RV32.Word),
      RV32.CodeAt m base Image.readerU8Code ∧ RV32.CodeAt m (base + 0xD6) Image.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 base Image.readerU8Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 (base + 0xD6) Image.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base Image.readerU8Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xD6) Image.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 0, BitVec.ofNat 32 Image.readerU8Address, witnessMemImage⟩,
    BitVec.ofNat 32 Image.readerU8Address, 0, 0x3FCC5100, ?_, ?_, by decide, rfl, rfl,
    rfl, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; decide +kernel)
    | (unfold RV32.Sep; decide +kernel)
    | decide +kernel

/-- A machine that calls `Segment::physical` for a flash-data segment meets
`segmentPhysical_correct`'s hypotheses. -/
theorem exists_segmentPhysical_machine :
    ∃ (m : RV32.Machine) (base retAddr out addr : RV32.Word) (k : BitVec 8),
      RV32.CodeAt m base Image.segmentPhysicalCode ∧ base.toNat % 2 = 0 ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = addr ∧ RV32.reg m RV32.a2 = k.zeroExtend 32 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ out.toNat % 4 = 0 ∧
      RV32.Sep out 8 base Image.segmentPhysicalCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3C010000 else if r = RV32.a2 then 1 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.segmentPhysicalAddress, witnessMemImage⟩,
    BitVec.ofNat 32 Image.segmentPhysicalAddress, 0, 0x3FCC5000, 0x3C010000, 1, ?_, by decide, rfl, rfl, rfl,
    rfl, rfl, by decide, by decide, RV32.sep_of_le (by decide) (by decide)⟩
  unfold RV32.CodeAt; decide +kernel

set_option maxRecDepth 20000 in
/-- A machine that calls `memcpy` for 256 bytes between word-aligned buffers
meets `memcpy_aligned`'s hypotheses. -/
theorem exists_memcpy_machine :
    ∃ (m : RV32.Machine) (stub retAddr dst src : RV32.Word) (w : Nat),
      RV32.CodeAt m stub Image.memcpyStubCode ∧ RV32.CodeAt m (stub + 8) Image.memcpyBodyCode ∧
      stub.toNat % 2 = 0 ∧ m.pc = stub ∧ RV32.reg m RV32.a0 = dst ∧ RV32.reg m RV32.a1 = src ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 (4 * w) ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ 4 ≤ w ∧ dst.toNat + 4 * w < 2 ^ 32 ∧
      BitVec.ofNat 32 (4 * w) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * w) ∧
      dst.toNat % 4 = 0 ∧ src.toNat % 4 = 0 ∧ RV32.Sep dst (4 * w) src (4 * w) ∧
      RV32.Sep dst (4 * w) (stub + 8) Image.memcpyBodyCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x100 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.memcpyStubAddress, witnessMemImage⟩,
    BitVec.ofNat 32 Image.memcpyStubAddress, 0, 0x3FCC5000, 0x3FCC6000, 64, ?_, ?_, by decide, rfl, rfl,
    rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩
  all_goals (unfold RV32.CodeAt; decide +kernel)

/-- `witnessMemImage` with `image::parse`, its restore helper, and the region
tables added where the image loads them. -/
def witnessMemImageParse (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 Image.imageParseAddress).toNat < Image.imageParseCode.length then
    RV32.byteAt Image.imageParseCode (a - BitVec.ofNat 32 Image.imageParseAddress).toNat
  else if (a - BitVec.ofNat 32 Image.imageRestoreAddress).toNat < Image.imageRestoreCode.length then
    RV32.byteAt Image.imageRestoreCode (a - BitVec.ofNat 32 Image.imageRestoreAddress).toNat
  else if (a - BitVec.ofNat 32 Image.regionEndsAddress).toNat < Image.regionEndsData.length then
    RV32.byteAt Image.regionEndsData (a - BitVec.ofNat 32 Image.regionEndsAddress).toNat
  else if (a - BitVec.ofNat 32 Image.regionStartsAddress).toNat < Image.regionStartsData.length then
    RV32.byteAt Image.regionStartsData (a - BitVec.ofNat 32 Image.regionStartsAddress).toNat
  else witnessMemImage a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- A machine that calls `image::parse` on 256 bytes at `0x3FCC6000`, with the
result at `0x3FCC5000` and the stack at `0x3FCC7F60`, meets
`imageParse_correct`'s hypotheses. -/
theorem exists_imageParse_machine :
    ∃ (m : RV32.Machine) (P R G ptr len out ilen : RV32.Word),
      RV32.ICode m.mem P ∧ RV32.IEnv P R G ptr len out ∧ m.pc = P ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = ptr ∧ RV32.reg m RV32.a2 = len ∧ RV32.reg m RV32.a3 = ilen ∧
      RV32.reg m RV32.sp = G + 0x160 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.a2 then 0x100 else if r = RV32.a3 then 0x20000
    else if r = RV32.sp then 0x3FCC7F60 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.imageParseAddress, witnessMemImageParse⟩,
    BitVec.ofNat 32 Image.imageParseAddress, 0x3FCC7DD0, 0x3FCC7E00, 0x3FCC6000, 0x100, 0x3FCC5000, 0x20000,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, ⟨by decide, by decide⟩,
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), by decide⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals (unfold RV32.CodeIn; decide +kernel)

/-- `witnessMemImageParse` with `memset` and the functions the P-256 field
multiplication runs added where the image loads them. -/
def witnessMemField (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 Image.memsetAddress).toNat < Image.memsetCode.length then
    RV32.byteAt Image.memsetCode (a - BitVec.ofNat 32 Image.memsetAddress).toNat
  else if (a - BitVec.ofNat 32 Image.borrowingSubAddress).toNat < Image.borrowingSubCode.length then
    RV32.byteAt Image.borrowingSubCode (a - BitVec.ofNat 32 Image.borrowingSubAddress).toNat
  else if (a - BitVec.ofNat 32 Image.subInnerAddress).toNat < Image.subInnerCode.length then
    RV32.byteAt Image.subInnerCode (a - BitVec.ofNat 32 Image.subInnerAddress).toNat
  else if (a - BitVec.ofNat 32 Image.subInnerSaveAddress).toNat < Image.subInnerSaveCode.length then
    RV32.byteAt Image.subInnerSaveCode (a - BitVec.ofNat 32 Image.subInnerSaveAddress).toNat
  else if (a - BitVec.ofNat 32 Image.subInnerRestoreAddress).toNat < Image.subInnerRestoreCode.length then
    RV32.byteAt Image.subInnerRestoreCode (a - BitVec.ofNat 32 Image.subInnerRestoreAddress).toNat
  else if (a - BitVec.ofNat 32 Image.wideMulAddress).toNat < Image.wideMulCode.length then
    RV32.byteAt Image.wideMulCode (a - BitVec.ofNat 32 Image.wideMulAddress).toNat
  else if (a - BitVec.ofNat 32 Image.wideMulSaveAddress).toNat < Image.wideMulSaveCode.length then
    RV32.byteAt Image.wideMulSaveCode (a - BitVec.ofNat 32 Image.wideMulSaveAddress).toNat
  else if (a - BitVec.ofNat 32 Image.wideMulRestoreAddress).toNat < Image.wideMulRestoreCode.length then
    RV32.byteAt Image.wideMulRestoreCode (a - BitVec.ofNat 32 Image.wideMulRestoreAddress).toNat
  else if (a - BitVec.ofNat 32 Image.fieldMulAddress).toNat < Image.fieldMulCode.length then
    RV32.byteAt Image.fieldMulCode (a - BitVec.ofNat 32 Image.fieldMulAddress).toNat
  else witnessMemImageParse a

set_option maxRecDepth 20000 in
/-- A machine that calls `memset` to zero 32 bytes at a word-aligned address
meets `memset_aligned`'s hypotheses. -/
theorem exists_memset_machine :
    ∃ (m : RV32.Machine) (base retAddr dst b : RV32.Word) (w : Nat),
      RV32.CodeAt m base Image.memsetCode ∧ base.toNat % 2 = 0 ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = dst ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 (4 * w) ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ 4 ≤ w ∧ dst.toNat + 4 * w < 2 ^ 32 ∧
      BitVec.ofNat 32 (4 * w) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * w) ∧ dst.toNat % 4 = 0 ∧
      RV32.Sep dst (4 * w) base Image.memsetCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a2 then 0x20 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.memsetAddress, witnessMemField⟩,
    BitVec.ofNat 32 Image.memsetAddress, 0, 0x3FCC5000, 0, 8, ?_, by decide, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide)⟩
  unfold RV32.CodeAt; decide +kernel

/-- A machine that calls `borrowing_sub` with a borrow mask meets
`borrowingSub_correct`'s hypotheses. -/
theorem exists_borrowingSub_machine :
    ∃ (m : RV32.Machine) (base retAddr l r b : RV32.Word),
      RV32.CodeAt m base Image.borrowingSubCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = l ∧
      RV32.reg m RV32.a1 = r ∧ RV32.reg m RV32.a2 = b ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base Image.borrowingSubCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 5 else if r = RV32.a1 then 7 else if r = RV32.a2 then 0xFFFFFFFF
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.borrowingSubAddress, witnessMemField⟩,
    BitVec.ofNat 32 Image.borrowingSubAddress, 0, 5, 7, 0xFFFFFFFF, ?_, rfl, rfl, rfl, rfl, rfl, by decide,
    by decide, RV32.sep_of_le (by decide) (by decide)⟩
  unfold RV32.CodeAt; decide +kernel

/-- The P-256 modulus as `sub_inner`'s second operand holds it, as bytes. -/
def pLimbBytes : List Nat :=
  [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF, 0, 0, 0, 0]

/-- `witnessMemField` with the modulus at `0x3FCC6100`. -/
def witnessMemSub (a : RV32.Word) : BitVec 8 :=
  if (a - 0x3FCC6100).toNat < 36 then RV32.byteAt pLimbBytes (a - 0x3FCC6100).toNat else witnessMemField a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- A machine that calls `sub_inner` with the result at `0x3FCC5000`, the
operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at `0x3FCC8000`
meets `subInner_correct`'s hypotheses. -/
theorem exists_subInner_machine :
    ∃ (m : RV32.Machine) (P sp0 out lp rp retAddr : RV32.Word), RV32.SIEnv m.mem P sp0 out lp rp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = lp ∧ RV32.reg m RV32.a2 = rp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.subInnerAddress, witnessMemSub⟩, BitVec.ofNat 32 Image.subInnerAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), ⟨by decide, by decide, by decide⟩, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals first
    | (unfold RV32.CodeIn; decide +kernel)
    | decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- A machine that calls `widening_mul_fixed::<8, 8>` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC8000` meets `wideMul_correct`'s hypotheses. -/
theorem exists_wideMul_machine :
    ∃ (m : RV32.Machine) (P sp0 out ap bp retAddr : RV32.Word), RV32.WMEnv m.mem P sp0 out ap bp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.wideMulAddress, witnessMemField⟩, BitVec.ofNat 32 Image.wideMulAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
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

/-- info: 'C3.decodeManifest_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.decodeManifest_bytes

/-- info: 'C3.decodeManifest_parse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.decodeManifest_parse

/-- info: 'C3.manifestParse_decodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.manifestParse_decodes

/-- info: 'C3.RV32.readerU8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readerU8_correct

/-- info: 'C3.RV32.segmentPhysical_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.segmentPhysical_correct

/-- info: 'C3.RV32.memcpy_aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.memcpy_aligned

/-- info: 'C3.exists_readerU8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_readerU8_machine

/-- info: 'C3.exists_segmentPhysical_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_segmentPhysical_machine

/-- info: 'C3.exists_memcpy_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_memcpy_machine

/-- info: 'C3.RV32.St.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.St.block

/-- info: 'C3.RV32.image_epilogue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.image_epilogue

/-- info: 'C3.RV32.ip_magic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ip_magic

/-- info: 'C3.RV32.ip_version' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ip_version

/-- info: 'C3.RV32.ip_u16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ip_u16

/-- info: 'C3.RV32.ip_u8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ip_u8

/-- info: 'C3.RV32.ip_reserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ip_reserved

/-- info: 'C3.RV32.ip_u32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ip_u32

/-- info: 'C3.RV32.ip_physical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ip_physical

/-- info: 'C3.RV32.ip_memcpy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ip_memcpy

/-- info: 'C3.RV32.imageParse_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.imageParse_correct

/-- info: 'C3.exists_imageParse_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_imageParse_machine

/-- info: 'C3.imgW_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.imgW_rel

/-- info: 'C3.imageParse_decodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.imageParse_decodes

/-- info: 'C3.imgW_pages_signed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.imgW_pages_signed

/-- info: 'C3.RV32.memset_aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.memset_aligned

/-- info: 'C3.exists_memset_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_memset_machine

/-- info: 'C3.RV32.borrowingSub_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.borrowingSub_correct

/-- info: 'C3.RV32.bsubB_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bsubB_eq

/-- info: 'C3.exists_borrowingSub_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_borrowingSub_machine

/-- info: 'C3.RV32.addBack_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.addBack_val

/-- info: 'C3.RV32.bchain_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bchain_val

/-- info: 'C3.RV32.sub_fin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sub_fin

/-- info: 'C3.RV32.subInner_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.subInner_correct

/-- info: 'C3.exists_subInner_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_subInner_machine

/-- info: 'C3.RV32.wideMul_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.wideMul_correct

/-- info: 'C3.exists_wideMul_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_wideMul_machine
