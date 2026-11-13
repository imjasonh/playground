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
import C3BootProofs.Proofs.Sha256Loop
import C3BootProofs.Proofs.P384Add
import C3BootProofs.Proofs.P384Double
import C3BootProofs.Proofs.P384Sub
import C3BootProofs.Proofs.FeReduce
import C3BootProofs.Proofs.FeMul
import C3BootProofs.Proofs.FeSqInner
import C3BootProofs.Proofs.FeSquare
import C3BootProofs.Proofs.FlashRead
import C3BootProofs.Proofs.SelectI64
import C3BootProofs.Proofs.FeAdd
import C3BootProofs.Proofs.FeSub
import C3BootProofs.Proofs.WideMul12x2
import C3BootProofs.Proofs.WideMul8x2
import C3BootProofs.Proofs.EdDouble
import C3BootProofs.Proofs.FePow2k
import C3BootProofs.Proofs.Sha512Compress
import C3BootProofs.Proofs.P384PtDouble
import C3BootProofs.Proofs.P384PtAdd
import C3BootProofs.Proofs.CondNeg12
import C3BootProofs.Proofs.CondNeg8
import C3BootProofs.Proofs.FromI64
import C3BootProofs.Proofs.RegionMem
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
import C3BootProofs.Proofs.FieldMul
import C3BootProofs.Proofs.FieldDouble
import C3BootProofs.Proofs.PointAdd
import C3BootProofs.Proofs.Sha256Compress
import C3BootProofs.Proofs.MemsetAny
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.ShaOneShot
import C3BootProofs.Proofs.MontMul12Main
import C3BootProofs.Proofs.SqrMont12Main
import C3BootProofs.Image.BootloaderV0

/-!
# Audit

Each theorem's axioms are pinned, so a proof that comes to depend on
`sorryAx` or a new axiom fails the build. The non-vacuity theorem shows that
the trace theorems' hypotheses can hold together with a jump.
-/

namespace C3

/-- Closes `CodeIn (regionMem rs) base code` from the regions' bounds. -/
macro "code_in" : tactic =>
  `(tactic| exact RV32.regionMem_codeIn_of_any (by decide +kernel) (by decide +kernel))

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
    ∃ (m : RV32.Machine) (base retAddr : RV32.Word), RV32.CodeAt m base ImageV0.crc32Code ∧
      m.pc = base ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let base : RV32.Word := BitVec.ofNat 32 ImageV0.crc32Address
  refine ⟨⟨fun _ => 0, base, fun a => RV32.byteAt ImageV0.crc32Code (a - base).toNat⟩, base, 0,
    ?_, rfl, rfl, by decide⟩
  intro i hi
  have hi' : i < 2 ^ 32 := Nat.lt_trans hi (by decide)
  show RV32.byteAt ImageV0.crc32Code (base + BitVec.ofNat 32 i - base).toNat = _
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']

/-- A machine with `Reader::bytes`'s bytes at the address the image loads
them, and a result and reader in data memory, meets `readerBytes_correct`'s
hypotheses. -/
theorem exists_readerBytes_machine :
    ∃ (m : RV32.Machine) (base retAddr out self n : RV32.Word),
      RV32.CodeAt m base ImageV0.readerBytesCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = self ∧ RV32.reg m RV32.a2 = n ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ out.toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      RV32.Sep out 8 base ImageV0.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base ImageV0.readerBytesCode.length := by
  let base : RV32.Word := BitVec.ofNat 32 ImageV0.readerBytesAddress
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else 0
  refine ⟨⟨regs, base, fun a => RV32.byteAt ImageV0.readerBytesCode (a - base).toNat⟩, base, 0,
    0x3FCC5000, 0x3FCC5100, 0, ?_, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by unfold RV32.Sep; decide, by unfold RV32.Sep; decide⟩
  intro i hi
  have hi' : i < 2 ^ 32 := Nat.lt_trans hi (by decide)
  show RV32.byteAt ImageV0.readerBytesCode (base + BitVec.ofNat 32 i - base).toNat = _
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi']

/-- The reader the `Reader::array::<4>` witness uses: a 16-byte slice at
`0x3FCC6000`, at position 0. -/
def witnessReader : List Nat := [0x00, 0x60, 0xCC, 0x3F, 16, 0, 0, 0, 0, 0, 0, 0]

/-- Memory with `Reader::array::<4>` and `Reader::bytes` where the image
loads them and the witness reader at `0x3FCC5100`. -/
def witnessMem : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

/-- A machine that calls `Reader::array::<4>` on the witness reader, with
the stack at `0x3FCC8000`, meets `readerArray4_correct`'s hypotheses. -/
theorem exists_readerArray4_machine :
    ∃ (m : RV32.Machine) (base bbase retAddr out self : RV32.Word),
      RV32.CodeAt m base ImageV0.readerArray4Code ∧ RV32.CodeAt m bbase ImageV0.readerBytesCode ∧
      bbase = base + 0xFFFFFF96 ∧ base.toNat % 2 = 0 ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = self ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧
      self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 base ImageV0.readerArray4Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 bbase ImageV0.readerBytesCode.length ∧
      RV32.Sep out 8 base ImageV0.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 base ImageV0.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 bbase ImageV0.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 ∧
      RV32.Sep out 8 (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.readerArray4Address, witnessMem⟩,
    BitVec.ofNat 32 ImageV0.readerArray4Address, BitVec.ofNat 32 ImageV0.readerBytesAddress, 0,
    0x3FCC5000, 0x3FCC5100, ?_, ?_, by decide, by decide, rfl, rfl, rfl, rfl, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RV32.CodeAt; code_in
  · unfold RV32.CodeAt; code_in
  · decide +kernel
  all_goals (first | exact RV32.sep_of_le (by decide) (by decide) | exact (RV32.sep_of_le (by decide) (by decide)).symm | (unfold RV32.Sep; decide +kernel))

/-- `witnessMem` with `Reader::u32` added where the image loads it. -/
def witnessMemU32 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.readerU32Address, ImageV0.readerU32Code),
    (ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

/-- A machine that calls `Reader::u32` on the witness reader meets
`readerU32_correct`'s hypotheses. -/
theorem exists_readerU32_machine :
    ∃ (m : RV32.Machine) (base retAddr out self : RV32.Word),
      RV32.CodeAt m base ImageV0.readerU32Code ∧
      RV32.CodeAt m (base + 0xFFFFFADE) ImageV0.readerArray4Code ∧
      RV32.CodeAt m (base + 0xFFFFFADE + 0xFFFFFF96) ImageV0.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = self ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 base ImageV0.readerU32Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0xFFFFFADE) ImageV0.readerArray4Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0xFFFFFADE + 0xFFFFFF96)
        ImageV0.readerBytesCode.length ∧
      RV32.Sep out 8 base ImageV0.readerU32Code.length ∧
      RV32.Sep (self + 8) 4 base ImageV0.readerU32Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xFFFFFADE) ImageV0.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xFFFFFADE + 0xFFFFFF96) ImageV0.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep out 8 (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.readerU32Address, witnessMemU32⟩,
    BitVec.ofNat 32 ImageV0.readerU32Address, 0, 0x3FCC5000, 0x3FCC5100, ?_, ?_, ?_, by decide, rfl,
    rfl, rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; code_in)
    | (first | exact RV32.sep_of_le (by decide) (by decide) | exact (RV32.sep_of_le (by decide) (by decide)).symm | (unfold RV32.Sep; decide +kernel))
    | decide +kernel

/-- `witnessMemU32` with `Reader::magic` and its load helper, `Reader::u16`,
`Reader::version_1`, and `Reader::reserved` added where the image loads
them. -/
def witnessMemChecks : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.readerMagicAddress, ImageV0.readerMagicCode),
    (ImageV0.magicLoadAddress, ImageV0.magicLoadCode),
    (ImageV0.readerU16Address, ImageV0.readerU16Code),
    (ImageV0.readerVersion1Address, ImageV0.readerVersion1Code),
    (ImageV0.readerReservedAddress, ImageV0.readerReservedCode),
    (ImageV0.readerU32Address, ImageV0.readerU32Code),
    (ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

/-- The registers of a call on the witness reader with the stack at
`0x3FCC8000`, with `a1` set to `a1v`. -/
def witnessRegs (a1v : RV32.Word) (r : Fin 32) : RV32.Word :=
  if r = RV32.a0 then 0x3FCC5100 else if r = RV32.a1 then a1v
  else if r = RV32.sp then 0x3FCC8000 else 0

/-- A machine that calls `Reader::magic` on the witness reader meets
`readerMagic_correct`'s hypotheses. -/
theorem exists_readerMagic_machine :
    ∃ (m : RV32.Machine) (base retAddr self k : RV32.Word),
      RV32.CodeAt m base ImageV0.readerMagicCode ∧
      RV32.CodeAt m (base + 0x1AC) ImageV0.readerArray4Code ∧
      RV32.CodeAt m (base + 0x1AC + 0xFFFFFF96) ImageV0.readerBytesCode ∧
      RV32.CodeAt m (base + 0x16804) ImageV0.magicLoadCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧ RV32.reg m RV32.a1 = k ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 base ImageV0.readerMagicCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x1AC) ImageV0.readerArray4Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x1AC + 0xFFFFFF96)
        ImageV0.readerBytesCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 (base + 0x16804) ImageV0.magicLoadCode.length ∧
      RV32.Sep (self + 8) 4 base ImageV0.readerMagicCode.length ∧
      RV32.Sep (self + 8) 4 (base + 0x1AC) ImageV0.readerArray4Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0x1AC + 0xFFFFFF96) ImageV0.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 (base + 0x16804) ImageV0.magicLoadCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFD0) 48 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 0x4C533343, BitVec.ofNat 32 ImageV0.readerMagicAddress, witnessMemChecks⟩,
    BitVec.ofNat 32 ImageV0.readerMagicAddress, 0, 0x3FCC5100, 0x4C533343, ?_, ?_, ?_, ?_, by decide, rfl,
    rfl, rfl, rfl, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; code_in)
    | (first | exact RV32.sep_of_le (by decide) (by decide) | exact (RV32.sep_of_le (by decide) (by decide)).symm | (unfold RV32.Sep; decide +kernel))
    | decide +kernel

/-- A machine that calls `Reader::u16` on the witness reader meets
`readerU16_correct`'s hypotheses. -/
theorem exists_readerU16_machine :
    ∃ (m : RV32.Machine) (base retAddr self : RV32.Word),
      RV32.CodeAt m base ImageV0.readerU16Code ∧
      RV32.CodeAt m (base + 0xFFFFFFDA) ImageV0.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 base ImageV0.readerU16Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 (base + 0xFFFFFFDA) ImageV0.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base ImageV0.readerU16Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xFFFFFFDA) ImageV0.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 0, BitVec.ofNat 32 ImageV0.readerU16Address, witnessMemChecks⟩,
    BitVec.ofNat 32 ImageV0.readerU16Address, 0, 0x3FCC5100, ?_, ?_, by decide, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; code_in)
    | (first | exact RV32.sep_of_le (by decide) (by decide) | exact (RV32.sep_of_le (by decide) (by decide)).symm | (unfold RV32.Sep; decide +kernel))
    | decide +kernel

/-- A machine that calls `Reader::version_1` on the witness reader meets
`readerVersion1_correct`'s hypotheses. -/
theorem exists_readerVersion1_machine :
    ∃ (m : RV32.Machine) (base retAddr self : RV32.Word),
      RV32.CodeAt m base ImageV0.readerVersion1Code ∧
      RV32.CodeAt m (base + 0x126) ImageV0.readerU16Code ∧
      RV32.CodeAt m (base + 0x126 + 0xFFFFFFDA) ImageV0.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 base ImageV0.readerVersion1Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 (base + 0x126) ImageV0.readerU16Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 (base + 0x126 + 0xFFFFFFDA)
        ImageV0.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base ImageV0.readerVersion1Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0x126) ImageV0.readerU16Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0x126 + 0xFFFFFFDA) ImageV0.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFE0) 32 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 0, BitVec.ofNat 32 ImageV0.readerVersion1Address, witnessMemChecks⟩,
    BitVec.ofNat 32 ImageV0.readerVersion1Address, 0, 0x3FCC5100, ?_, ?_, ?_, by decide, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; code_in)
    | (first | exact RV32.sep_of_le (by decide) (by decide) | exact (RV32.sep_of_le (by decide) (by decide)).symm | (unfold RV32.Sep; decide +kernel))
    | decide +kernel

/-- A machine that calls `Reader::reserved` for 2 bytes on the witness
reader meets `readerReserved_correct`'s hypotheses. -/
theorem exists_readerReserved_machine :
    ∃ (m : RV32.Machine) (base retAddr self n : RV32.Word),
      RV32.CodeAt m base ImageV0.readerReservedCode ∧
      RV32.CodeAt m (base + 0x9C) ImageV0.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧ RV32.reg m RV32.a1 = n ∧
      n ≠ 0 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 base ImageV0.readerReservedCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 (base + 0x9C) ImageV0.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base ImageV0.readerReservedCode.length ∧
      RV32.Sep (self + 8) 4 (base + 0x9C) ImageV0.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 2, BitVec.ofNat 32 ImageV0.readerReservedAddress, witnessMemChecks⟩,
    BitVec.ofNat 32 ImageV0.readerReservedAddress, 0, 0x3FCC5100, 2, ?_, ?_, by decide, rfl, rfl, rfl,
    by decide, rfl, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; code_in)
    | (first | exact RV32.sep_of_le (by decide) (by decide) | exact (RV32.sep_of_le (by decide) (by decide)).symm | (unfold RV32.Sep; decide +kernel))
    | decide +kernel


/-- `witnessMemU32` with `manifest::part` and its save and restore helpers added
where the image loads them. -/
def witnessMemPart : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.manifestPartAddress, ImageV0.manifestPartCode),
    (ImageV0.partSaveAddress, ImageV0.partSaveCode),
    (ImageV0.partRestoreAddress, ImageV0.partRestoreCode),
    (ImageV0.readerU32Address, ImageV0.readerU32Code),
    (ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

/-- A machine that calls `manifest::part` on the witness reader with the
image's bounds meets `manifestPart_correct`'s hypotheses. -/
theorem exists_manifestPart_machine :
    ∃ (m : RV32.Machine) (base retAddr out self lo hi : RV32.Word),
      RV32.CodeAt m base ImageV0.manifestPartCode ∧
      RV32.CodeAt m (base + 0x12BB6) ImageV0.partSaveCode ∧
      RV32.CodeAt m (base + 0x129F4) ImageV0.partRestoreCode ∧
      RV32.CodeAt m (base + 0xFFFFC94C) ImageV0.readerU32Code ∧
      RV32.CodeAt m (base + 0xFFFFC94C + 0xFFFFFADE) ImageV0.readerArray4Code ∧
      RV32.CodeAt m (base + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96) ImageV0.readerBytesCode ∧
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
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.manifestPartAddress, witnessMemPart⟩,
    BitVec.ofNat 32 ImageV0.manifestPartAddress, 0, 0x3FCC5000, 0x3FCC5100, 37, 0x1D0000,
    ?_, ?_, ?_, ?_, ?_, ?_, by decide, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide, ?_, RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; code_in)
    | (first | exact RV32.sep_of_le (by decide) (by decide) | exact (RV32.sep_of_le (by decide) (by decide)).symm | (unfold RV32.Sep; decide +kernel))
    | decide +kernel


/-- `witnessMemChecks` with `manifest::parse`, its helpers, and `part` and its
helpers added where the image loads them. -/
def witnessMemParse : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.manifestParseAddress, ImageV0.manifestParseCode),
    (ImageV0.parseSaveAddress, ImageV0.parseSaveCode),
    (ImageV0.parseRestoreAddress, ImageV0.parseRestoreCode),
    (ImageV0.manifestPartAddress, ImageV0.manifestPartCode),
    (ImageV0.partSaveAddress, ImageV0.partSaveCode),
    (ImageV0.partRestoreAddress, ImageV0.partRestoreCode),
    (ImageV0.readerMagicAddress, ImageV0.readerMagicCode),
    (ImageV0.magicLoadAddress, ImageV0.magicLoadCode),
    (ImageV0.readerU16Address, ImageV0.readerU16Code),
    (ImageV0.readerVersion1Address, ImageV0.readerVersion1Code),
    (ImageV0.readerReservedAddress, ImageV0.readerReservedCode),
    (ImageV0.readerU32Address, ImageV0.readerU32Code),
    (ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

set_option maxRecDepth 100000 in
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
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.manifestParseAddress, witnessMemParse⟩,
    BitVec.ofNat 32 ImageV0.manifestParseAddress, 0, 0x3FCC5000, 0x3FCC6000, 0x3FCC7F70, 0x3FCC7FC0,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, by decide, by decide,
    ⟨by decide, by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩⟩
  all_goals code_in

/-- `witnessMemParse` with `Reader::u8`, `Segment::physical`, and `memcpy`'s
stub and body added where the image loads them. -/
def witnessMemImage : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.readerU8Address, ImageV0.readerU8Code),
    (ImageV0.segmentPhysicalAddress, ImageV0.segmentPhysicalCode),
    (ImageV0.memcpyStubAddress, ImageV0.memcpyStubCode),
    (ImageV0.memcpyBodyAddress, ImageV0.memcpyBodyCode),
    (ImageV0.manifestParseAddress, ImageV0.manifestParseCode),
    (ImageV0.parseSaveAddress, ImageV0.parseSaveCode),
    (ImageV0.parseRestoreAddress, ImageV0.parseRestoreCode),
    (ImageV0.manifestPartAddress, ImageV0.manifestPartCode),
    (ImageV0.partSaveAddress, ImageV0.partSaveCode),
    (ImageV0.partRestoreAddress, ImageV0.partRestoreCode),
    (ImageV0.readerMagicAddress, ImageV0.readerMagicCode),
    (ImageV0.magicLoadAddress, ImageV0.magicLoadCode),
    (ImageV0.readerU16Address, ImageV0.readerU16Code),
    (ImageV0.readerVersion1Address, ImageV0.readerVersion1Code),
    (ImageV0.readerReservedAddress, ImageV0.readerReservedCode),
    (ImageV0.readerU32Address, ImageV0.readerU32Code),
    (ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

set_option maxRecDepth 100000 in
/-- A machine that calls `Reader::u8` on the witness reader meets
`readerU8_correct`'s hypotheses. -/
theorem exists_readerU8_machine :
    ∃ (m : RV32.Machine) (base retAddr self : RV32.Word),
      RV32.CodeAt m base ImageV0.readerU8Code ∧ RV32.CodeAt m (base + 0xD6) ImageV0.readerBytesCode ∧
      base.toNat % 2 = 0 ∧ m.pc = base ∧ RV32.reg m RV32.a0 = self ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ self.toNat % 4 = 0 ∧
      (RV32.memLoad32 m.mem self ≠ 0 ∧
        (RV32.memLoad32 m.mem self).toNat + (RV32.memLoad32 m.mem (self + 4)).toNat ≤ 2 ^ 32) ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 base ImageV0.readerU8Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 (base + 0xD6) ImageV0.readerBytesCode.length ∧
      RV32.Sep (self + 8) 4 base ImageV0.readerU8Code.length ∧
      RV32.Sep (self + 8) 4 (base + 0xD6) ImageV0.readerBytesCode.length ∧
      RV32.Sep self 12 (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat
        (RV32.reg m RV32.sp + 0xFFFFFFF0) 16 ∧
      RV32.Sep (RV32.memLoad32 m.mem self) (RV32.memLoad32 m.mem (self + 4)).toNat (self + 8) 4 := by
  refine ⟨⟨witnessRegs 0, BitVec.ofNat 32 ImageV0.readerU8Address, witnessMemImage⟩,
    BitVec.ofNat 32 ImageV0.readerU8Address, 0, 0x3FCC5100, ?_, ?_, by decide, rfl, rfl,
    rfl, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (unfold RV32.CodeAt; code_in)
    | (first | exact RV32.sep_of_le (by decide) (by decide) | exact (RV32.sep_of_le (by decide) (by decide)).symm | (unfold RV32.Sep; decide +kernel))
    | decide +kernel

/-- A machine that calls `Segment::physical` for a flash-data segment meets
`segmentPhysical_correct`'s hypotheses. -/
theorem exists_segmentPhysical_machine :
    ∃ (m : RV32.Machine) (base retAddr out addr : RV32.Word) (k : BitVec 8),
      RV32.CodeAt m base ImageV0.segmentPhysicalCode ∧ base.toNat % 2 = 0 ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = addr ∧ RV32.reg m RV32.a2 = k.zeroExtend 32 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ out.toNat % 4 = 0 ∧
      RV32.Sep out 8 base ImageV0.segmentPhysicalCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3C010000 else if r = RV32.a2 then 1 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.segmentPhysicalAddress, witnessMemImage⟩,
    BitVec.ofNat 32 ImageV0.segmentPhysicalAddress, 0, 0x3FCC5000, 0x3C010000, 1, ?_, by decide, rfl, rfl, rfl,
    rfl, rfl, by decide, by decide, RV32.sep_of_le (by decide) (by decide)⟩
  unfold RV32.CodeAt; code_in

set_option maxRecDepth 20000 in
/-- A machine that calls `memcpy` for 256 bytes between word-aligned buffers
meets `memcpy_aligned`'s hypotheses. -/
theorem exists_memcpy_machine :
    ∃ (m : RV32.Machine) (stub retAddr dst src : RV32.Word) (w : Nat),
      RV32.CodeAt m stub ImageV0.memcpyStubCode ∧ RV32.CodeAt m (stub + 8) ImageV0.memcpyBodyCode ∧
      stub.toNat % 2 = 0 ∧ m.pc = stub ∧ RV32.reg m RV32.a0 = dst ∧ RV32.reg m RV32.a1 = src ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 (4 * w) ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ 4 ≤ w ∧ dst.toNat + 4 * w < 2 ^ 32 ∧
      BitVec.ofNat 32 (4 * w) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * w) ∧
      dst.toNat % 4 = 0 ∧ src.toNat % 4 = 0 ∧ RV32.Sep dst (4 * w) src (4 * w) ∧
      RV32.Sep dst (4 * w) (stub + 8) ImageV0.memcpyBodyCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x100 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.memcpyStubAddress, witnessMemImage⟩,
    BitVec.ofNat 32 ImageV0.memcpyStubAddress, 0, 0x3FCC5000, 0x3FCC6000, 64, ?_, ?_, by decide, rfl, rfl,
    rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩
  all_goals (unfold RV32.CodeAt; code_in)

/-- `witnessMemImage` with `image::parse`, its restore helper, and the region
tables added where the image loads them. -/
def witnessMemImageParse : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.imageParseAddress, ImageV0.imageParseCode),
    (ImageV0.imageRestoreAddress, ImageV0.imageRestoreCode),
    (ImageV0.regionEndsAddress, ImageV0.regionEndsData),
    (ImageV0.regionStartsAddress, ImageV0.regionStartsData),
    (ImageV0.readerU8Address, ImageV0.readerU8Code),
    (ImageV0.segmentPhysicalAddress, ImageV0.segmentPhysicalCode),
    (ImageV0.memcpyStubAddress, ImageV0.memcpyStubCode),
    (ImageV0.memcpyBodyAddress, ImageV0.memcpyBodyCode),
    (ImageV0.manifestParseAddress, ImageV0.manifestParseCode),
    (ImageV0.parseSaveAddress, ImageV0.parseSaveCode),
    (ImageV0.parseRestoreAddress, ImageV0.parseRestoreCode),
    (ImageV0.manifestPartAddress, ImageV0.manifestPartCode),
    (ImageV0.partSaveAddress, ImageV0.partSaveCode),
    (ImageV0.partRestoreAddress, ImageV0.partRestoreCode),
    (ImageV0.readerMagicAddress, ImageV0.readerMagicCode),
    (ImageV0.magicLoadAddress, ImageV0.magicLoadCode),
    (ImageV0.readerU16Address, ImageV0.readerU16Code),
    (ImageV0.readerVersion1Address, ImageV0.readerVersion1Code),
    (ImageV0.readerReservedAddress, ImageV0.readerReservedCode),
    (ImageV0.readerU32Address, ImageV0.readerU32Code),
    (ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

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
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.imageParseAddress, witnessMemImageParse⟩,
    BitVec.ofNat 32 ImageV0.imageParseAddress, 0x3FCC7DD0, 0x3FCC7E00, 0x3FCC6000, 0x100, 0x3FCC5000, 0x20000,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, ⟨by decide, by decide⟩,
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), by decide⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals code_in

/-- `witnessMemImageParse` with `memset` and the functions the P-256 field
multiplication runs added where the image loads them. -/
def witnessMemField : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.memsetAddress, ImageV0.memsetCode),
    (ImageV0.borrowingSubAddress, ImageV0.borrowingSubCode),
    (ImageV0.subInnerAddress, ImageV0.subInnerCode),
    (ImageV0.subInnerSaveAddress, ImageV0.subInnerSaveCode),
    (ImageV0.subInnerRestoreAddress, ImageV0.subInnerRestoreCode),
    (ImageV0.wideMulAddress, ImageV0.wideMulCode),
    (ImageV0.wideMulSaveAddress, ImageV0.wideMulSaveCode),
    (ImageV0.wideMulRestoreAddress, ImageV0.wideMulRestoreCode),
    (ImageV0.fieldMulAddress, ImageV0.fieldMulCode),
    (ImageV0.imageParseAddress, ImageV0.imageParseCode),
    (ImageV0.imageRestoreAddress, ImageV0.imageRestoreCode),
    (ImageV0.regionEndsAddress, ImageV0.regionEndsData),
    (ImageV0.regionStartsAddress, ImageV0.regionStartsData),
    (ImageV0.readerU8Address, ImageV0.readerU8Code),
    (ImageV0.segmentPhysicalAddress, ImageV0.segmentPhysicalCode),
    (ImageV0.memcpyStubAddress, ImageV0.memcpyStubCode),
    (ImageV0.memcpyBodyAddress, ImageV0.memcpyBodyCode),
    (ImageV0.manifestParseAddress, ImageV0.manifestParseCode),
    (ImageV0.parseSaveAddress, ImageV0.parseSaveCode),
    (ImageV0.parseRestoreAddress, ImageV0.parseRestoreCode),
    (ImageV0.manifestPartAddress, ImageV0.manifestPartCode),
    (ImageV0.partSaveAddress, ImageV0.partSaveCode),
    (ImageV0.partRestoreAddress, ImageV0.partRestoreCode),
    (ImageV0.readerMagicAddress, ImageV0.readerMagicCode),
    (ImageV0.magicLoadAddress, ImageV0.magicLoadCode),
    (ImageV0.readerU16Address, ImageV0.readerU16Code),
    (ImageV0.readerVersion1Address, ImageV0.readerVersion1Code),
    (ImageV0.readerReservedAddress, ImageV0.readerReservedCode),
    (ImageV0.readerU32Address, ImageV0.readerU32Code),
    (ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

set_option maxRecDepth 20000 in
/-- A machine that calls `memset` to zero 32 bytes at a word-aligned address
meets `memset_aligned`'s hypotheses. -/
theorem exists_memset_machine :
    ∃ (m : RV32.Machine) (base retAddr dst b : RV32.Word) (w : Nat),
      RV32.CodeAt m base ImageV0.memsetCode ∧ base.toNat % 2 = 0 ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = dst ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 (4 * w) ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ 4 ≤ w ∧ dst.toNat + 4 * w < 2 ^ 32 ∧
      BitVec.ofNat 32 (4 * w) &&& 0xFFFFFFFC = BitVec.ofNat 32 (4 * w) ∧ dst.toNat % 4 = 0 ∧
      RV32.Sep dst (4 * w) base ImageV0.memsetCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a2 then 0x20 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.memsetAddress, witnessMemField⟩,
    BitVec.ofNat 32 ImageV0.memsetAddress, 0, 0x3FCC5000, 0, 8, ?_, by decide, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide)⟩
  unfold RV32.CodeAt; code_in

set_option maxRecDepth 20000 in
/-- A machine that calls `memset` to fill 21 bytes from an odd address, so
that every loop runs, meets `memset_correct`'s hypotheses. -/
theorem exists_memsetAny_machine :
    ∃ (m : RV32.Machine) (base retAddr dst b : RV32.Word) (n : Nat),
      RV32.CodeAt m base ImageV0.memsetCode ∧ base.toNat % 2 = 0 ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = dst ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ dst.toNat + n < 2 ^ 32 ∧
      RV32.Sep dst n base ImageV0.memsetCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5001 else if r = RV32.a1 then 0xAB else if r = RV32.a2 then 21 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.memsetAddress, witnessMemField⟩,
    BitVec.ofNat 32 ImageV0.memsetAddress, 0, 0x3FCC5001, 0xAB, 21, ?_, by decide, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, RV32.sep_of_le (by decide) (by decide)⟩
  unfold RV32.CodeAt; code_in

set_option maxRecDepth 20000 in
/-- A machine that calls `memcpy` for 23 bytes from an address 3 bytes past
a 4-byte boundary to an odd address, so that the misaligned path runs,
meets `memcpy_correct`'s hypotheses. -/
theorem exists_memcpyAny_machine :
    ∃ (m : RV32.Machine) (stub retAddr dst src : RV32.Word) (N : Nat),
      RV32.CodeAt m stub ImageV0.memcpyStubCode ∧ stub.toNat % 2 = 0 ∧ m.pc = stub ∧
      RV32.reg m RV32.a0 = dst ∧ RV32.reg m RV32.a1 = src ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 N ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.McEnv m.mem (stub + 8) dst src (RV32.reg m RV32.sp + 0xFFFFFFF0) N := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5001 else if r = RV32.a1 then 0x3FCC6003 else if r = RV32.a2 then 23
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.memcpyStubAddress, witnessMemImage⟩,
    BitVec.ofNat 32 ImageV0.memcpyStubAddress, 0, 0x3FCC5001, 0x3FCC6003, 23, ?_, by decide, rfl, rfl,
    rfl, rfl, rfl, by decide,
    ⟨?_, RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), by decide, by decide, by decide, by decide⟩⟩
  all_goals (first | (unfold RV32.CodeAt; code_in) | code_in)

/-- A machine that calls `borrowing_sub` with a borrow mask meets
`borrowingSub_correct`'s hypotheses. -/
theorem exists_borrowingSub_machine :
    ∃ (m : RV32.Machine) (base retAddr l r b : RV32.Word),
      RV32.CodeAt m base ImageV0.borrowingSubCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = l ∧
      RV32.reg m RV32.a1 = r ∧ RV32.reg m RV32.a2 = b ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base ImageV0.borrowingSubCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 5 else if r = RV32.a1 then 7 else if r = RV32.a2 then 0xFFFFFFFF
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.borrowingSubAddress, witnessMemField⟩,
    BitVec.ofNat 32 ImageV0.borrowingSubAddress, 0, 5, 7, 0xFFFFFFFF, ?_, rfl, rfl, rfl, rfl, rfl, by decide,
    by decide, RV32.sep_of_le (by decide) (by decide)⟩
  unfold RV32.CodeAt; code_in

/-- The P-256 modulus as `sub_inner`'s second operand holds it, as bytes. -/
def pLimbBytes : List Nat :=
  [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF, 0, 0, 0, 0]

/-- Memory with the current image's P-256 field and point functions,
`borrowing_sub`, `memset`, `memcpy`, and the curve constant `b` where the
image loads them, the P-256 modulus at `0x3FCC6100`, and zeros elsewhere. -/
def witnessMemP256 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.subInnerAddress, Image.subInnerCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.wideMulAddress, Image.wideMulCode),
    (Image.fieldMulAddress, Image.fieldMulCode),
    (Image.fieldAddAddress, Image.fieldAddCode),
    (Image.fieldSubAddress, Image.fieldSubCode),
    (Image.fieldDoubleAddress, Image.fieldDoubleCode),
    (Image.pointAddAddress, Image.pointAddCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.curveBAddress, Image.curveBData),
    (0x3FCC6100, pLimbBytes)]

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
  refine ⟨⟨regs, BitVec.ofNat 32 Image.subInnerAddress, witnessMemP256⟩, BitVec.ofNat 32 Image.subInnerAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      ⟨by decide, by decide, by decide⟩, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals first
    | code_in
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
  refine ⟨⟨regs, BitVec.ofNat 32 Image.wideMulAddress, witnessMemP256⟩, BitVec.ofNat 32 Image.wideMulAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `FieldElement::multiply` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC8000` meets `fieldMul_correct`'s hypotheses. -/
theorem exists_fieldMul_machine :
    ∃ (m : RV32.Machine) (P sp0 res ap bp retAddr : RV32.Word), RV32.FMEnv m.mem P sp0 res ap bp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.fieldMulAddress, witnessMemP256⟩, BitVec.ofNat 32 Image.fieldMulAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

/-- `witnessMemField` with the field addition, subtraction, and doubling and
the point addition added where the image loads them. -/
def witnessMemPoint : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(ImageV0.fieldAddAddress, ImageV0.fieldAddCode),
    (ImageV0.fieldSubAddress, ImageV0.fieldSubCode),
    (ImageV0.fieldDoubleAddress, ImageV0.fieldDoubleCode),
    (ImageV0.pointAddAddress, ImageV0.pointAddCode),
    (ImageV0.curveBAddress, ImageV0.curveBData),
    (ImageV0.memsetAddress, ImageV0.memsetCode),
    (ImageV0.borrowingSubAddress, ImageV0.borrowingSubCode),
    (ImageV0.subInnerAddress, ImageV0.subInnerCode),
    (ImageV0.subInnerSaveAddress, ImageV0.subInnerSaveCode),
    (ImageV0.subInnerRestoreAddress, ImageV0.subInnerRestoreCode),
    (ImageV0.wideMulAddress, ImageV0.wideMulCode),
    (ImageV0.wideMulSaveAddress, ImageV0.wideMulSaveCode),
    (ImageV0.wideMulRestoreAddress, ImageV0.wideMulRestoreCode),
    (ImageV0.fieldMulAddress, ImageV0.fieldMulCode),
    (ImageV0.imageParseAddress, ImageV0.imageParseCode),
    (ImageV0.imageRestoreAddress, ImageV0.imageRestoreCode),
    (ImageV0.regionEndsAddress, ImageV0.regionEndsData),
    (ImageV0.regionStartsAddress, ImageV0.regionStartsData),
    (ImageV0.readerU8Address, ImageV0.readerU8Code),
    (ImageV0.segmentPhysicalAddress, ImageV0.segmentPhysicalCode),
    (ImageV0.memcpyStubAddress, ImageV0.memcpyStubCode),
    (ImageV0.memcpyBodyAddress, ImageV0.memcpyBodyCode),
    (ImageV0.manifestParseAddress, ImageV0.manifestParseCode),
    (ImageV0.parseSaveAddress, ImageV0.parseSaveCode),
    (ImageV0.parseRestoreAddress, ImageV0.parseRestoreCode),
    (ImageV0.manifestPartAddress, ImageV0.manifestPartCode),
    (ImageV0.partSaveAddress, ImageV0.partSaveCode),
    (ImageV0.partRestoreAddress, ImageV0.partRestoreCode),
    (ImageV0.readerMagicAddress, ImageV0.readerMagicCode),
    (ImageV0.magicLoadAddress, ImageV0.magicLoadCode),
    (ImageV0.readerU16Address, ImageV0.readerU16Code),
    (ImageV0.readerVersion1Address, ImageV0.readerVersion1Code),
    (ImageV0.readerReservedAddress, ImageV0.readerReservedCode),
    (ImageV0.readerU32Address, ImageV0.readerU32Code),
    (ImageV0.readerArray4Address, ImageV0.readerArray4Code),
    (ImageV0.readerBytesAddress, ImageV0.readerBytesCode),
    (0x3FCC5100, witnessReader)]

/-- `witnessMemPoint` with `sha2::sha256::compress256`, its helpers, and the
round constants added where the image loads them. -/
def witnessMemSha (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 ImageV0.shaIndexAddress).toNat < ImageV0.shaIndexCode.length then
    RV32.byteAt ImageV0.shaIndexCode (a - BitVec.ofNat 32 ImageV0.shaIndexAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaSigma1PartAddress).toNat < ImageV0.shaSigma1PartCode.length then
    RV32.byteAt ImageV0.shaSigma1PartCode (a - BitVec.ofNat 32 ImageV0.shaSigma1PartAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaKAddress).toNat < ImageV0.shaKData.length then
    RV32.byteAt ImageV0.shaKData (a - BitVec.ofNat 32 ImageV0.shaKAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.sha256CompressAddress).toNat < ImageV0.sha256CompressCode.length then
    RV32.byteAt ImageV0.sha256CompressCode (a - BitVec.ofNat 32 ImageV0.sha256CompressAddress).toNat
  else witnessMemPoint a

set_option maxRecDepth 200000 in
theorem witnessMemSha_compress :
    RV32.CodeIn witnessMemSha (BitVec.ofNat 32 ImageV0.sha256CompressAddress) ImageV0.sha256CompressCode := by
  intro i hi
  have hlen : ImageV0.sha256CompressCode.length = 11156 := rfl
  have hlenI : ImageV0.shaIndexCode.length = 22 := rfl
  have hlen97 : ImageV0.shaSigma1PartCode.length = 26 := rfl
  have hlenK : ImageV0.shaKData.length = 256 := rfl
  have ha : (BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i).toNat = 0x403b32ea + i := by
    have : (BitVec.ofNat 32 ImageV0.sha256CompressAddress).toNat = 0x403b32ea := rfl
    rw [BitVec.toNat_add, this, BitVec.toNat_ofNat]; omega
  have dI : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaIndexAddress).toNat < ImageV0.shaIndexCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaIndexAddress).toNat = 0x403b5e7e from rfl, hlenI]; omega
  have d97 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaSigma1PartAddress).toNat < ImageV0.shaSigma1PartCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaSigma1PartAddress).toNat = 0x403bf386 from rfl, hlen97]; omega
  have dK : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaKAddress).toNat < ImageV0.shaKData.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaKAddress).toNat = 0x3fcc4ebc from rfl, hlenK]; omega
  have eq_i : (BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.sha256CompressAddress).toNat = i := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  unfold witnessMemSha
  rw [ite_eq_right_of_eq_false _ _ (eq_false dI), ite_eq_right_of_eq_false _ _ (eq_false d97),
    ite_eq_right_of_eq_false _ _ (eq_false dK), eq_i, ite_eq_left_of_eq_true _ _ (eq_true hi)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `sha2::sha256::compress256` on 2 blocks (`n = 2`) with
the state at `0x3FCC5000`, the blocks at `0x3FCC6000`, and the stack at
`0x3FCC8000` meets `sha256Compress_correct`'s hypotheses. -/
theorem exists_sha256Compress_machine :
    ∃ (m : RV32.Machine) (P sp0 stp bp retAddr : RV32.Word) (n : Nat),
      RV32.SCEnv m.mem P sp0 stp bp n ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = stp ∧ RV32.reg m RV32.a1 = bp ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ 0 < n := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 2
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.sha256CompressAddress, witnessMemSha⟩,
    BitVec.ofNat 32 ImageV0.sha256CompressAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, 2,
    ⟨by decide, witnessMemSha_compress, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      (RV32.sep_of_le (by decide) (by decide)).symm⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide⟩
  all_goals (unfold RV32.CodeIn; decide +kernel)

/-- The hasher of the empty message: an empty buffer, the initial hash value
as the image stores it, and a block count of zero. -/
def emptyHasherBytes : List Nat := List.replicate 64 0 ++ ImageV0.shaIVData ++ List.replicate 8 0

/-- `witnessMemSha` with an empty hasher at `0x3FCC5000`, and `update`, its
save and restore helpers, and its block loop added where the image loads
them. -/
def witnessMemUpd (a : RV32.Word) : BitVec 8 :=
  if (a - 0x3FCC5000).toNat < 0x68 then RV32.byteAt emptyHasherBytes (a - 0x3FCC5000).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaUpdateAddress).toNat < ImageV0.shaUpdateCode.length then
    RV32.byteAt ImageV0.shaUpdateCode (a - BitVec.ofNat 32 ImageV0.shaUpdateAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaUpdateSaveAddress).toNat < ImageV0.shaUpdateSaveCode.length then
    RV32.byteAt ImageV0.shaUpdateSaveCode (a - BitVec.ofNat 32 ImageV0.shaUpdateSaveAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaUpdateRestoreAddress).toNat < ImageV0.shaUpdateRestoreCode.length then
    RV32.byteAt ImageV0.shaUpdateRestoreCode (a - BitVec.ofNat 32 ImageV0.shaUpdateRestoreAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaUpdateBlocksAddress).toNat < ImageV0.shaUpdateBlocksCode.length then
    RV32.byteAt ImageV0.shaUpdateBlocksCode (a - BitVec.ofNat 32 ImageV0.shaUpdateBlocksAddress).toNat
  else witnessMemSha a

set_option maxRecDepth 200000 in
theorem witnessMemUpd_compress :
    RV32.CodeIn witnessMemUpd (BitVec.ofNat 32 ImageV0.sha256CompressAddress) ImageV0.sha256CompressCode := by
  intro i hi
  have hlen : ImageV0.sha256CompressCode.length = 11156 := rfl
  have ha : (BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i).toNat = 0x403b32ea + i := by
    have : (BitVec.ofNat 32 ImageV0.sha256CompressAddress).toNat = 0x403b32ea := rfl
    rw [BitVec.toNat_add, this, BitVec.toNat_ofNat]; omega
  have dH : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i - 0x3FCC5000).toNat < 0x68) := by
    rw [BitVec.toNat_sub, ha, show (0x3FCC5000 : RV32.Word).toNat = 0x3FCC5000 from rfl]; omega
  have dU : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaUpdateAddress).toNat < ImageV0.shaUpdateCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaUpdateAddress).toNat = 0x403a6624 from rfl,
      show ImageV0.shaUpdateCode.length = 168 from rfl]; omega
  have dS : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaUpdateSaveAddress).toNat < ImageV0.shaUpdateSaveCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaUpdateSaveAddress).toNat = 0x403bf24a from rfl,
      show ImageV0.shaUpdateSaveCode.length = 12 from rfl]; omega
  have dR : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaUpdateRestoreAddress).toNat < ImageV0.shaUpdateRestoreCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaUpdateRestoreAddress).toNat = 0x403bf088 from rfl,
      show ImageV0.shaUpdateRestoreCode.length = 14 from rfl]; omega
  have dB : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaUpdateBlocksAddress).toNat < ImageV0.shaUpdateBlocksCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaUpdateBlocksAddress).toNat = 0x403a66cc from rfl,
      show ImageV0.shaUpdateBlocksCode.length = 26 from rfl]; omega
  unfold witnessMemUpd
  rw [ite_eq_right_of_eq_false _ _ (eq_false dH), ite_eq_right_of_eq_false _ _ (eq_false dU),
    ite_eq_right_of_eq_false _ _ (eq_false dS), ite_eq_right_of_eq_false _ _ (eq_false dR),
    ite_eq_right_of_eq_false _ _ (eq_false dB)]
  exact witnessMemSha_compress i hi

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `update` with 100 bytes at `0x3FCC6000`, the empty
hasher at `0x3FCC5000`, and the stack at `0x3FCC8000` meets
`shaUpdate_correct`'s hypotheses. -/
theorem exists_shaUpdate_machine :
    ∃ (m : RV32.Machine) (S D sp0 retAddr : RV32.Word) (n : Nat) (msg : List Nat),
      RV32.UpdEnv m.mem S D sp0 n ∧ m.pc = BitVec.ofNat 32 ImageV0.shaUpdateAddress ∧
      RV32.reg m RV32.a0 = S ∧ RV32.reg m RV32.a1 = D ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.HasherAt m.mem S msg ∧ n < 2 ^ 31 ∧ msg.length + n < 2 ^ 32 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.shaUpdateAddress, witnessMemUpd⟩,
    0x3FCC5000, 0x3FCC6000, 0x3FCC8000, 0, 100, [],
    ⟨?_, ?_, ?_, ?_, witnessMemUpd_compress, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      by decide, by decide, (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl, ⟨by decide, ?_, rfl, ?_, ?_, ?_⟩, by decide, by decide⟩
  all_goals first
    | (unfold RV32.CodeIn; decide +kernel)
    | decide +kernel

/-- `witnessMemUpd` with `finalize`, its save and restore helpers, the
zeroing `from_fn`, the block closure, and the big-endian store helper added
where the image loads them. -/
def witnessMemFin (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 ImageV0.shaFinalizeAddress).toNat < ImageV0.shaFinalizeCode.length then
    RV32.byteAt ImageV0.shaFinalizeCode (a - BitVec.ofNat 32 ImageV0.shaFinalizeAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaFinalizeSaveAddress).toNat < ImageV0.shaFinalizeSaveCode.length then
    RV32.byteAt ImageV0.shaFinalizeSaveCode (a - BitVec.ofNat 32 ImageV0.shaFinalizeSaveAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaFinalizeRestoreAddress).toNat < ImageV0.shaFinalizeRestoreCode.length then
    RV32.byteAt ImageV0.shaFinalizeRestoreCode (a - BitVec.ofNat 32 ImageV0.shaFinalizeRestoreAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaZero32Address).toNat < ImageV0.shaZero32Code.length then
    RV32.byteAt ImageV0.shaZero32Code (a - BitVec.ofNat 32 ImageV0.shaZero32Address).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaFinalizeBlockAddress).toNat < ImageV0.shaFinalizeBlockCode.length then
    RV32.byteAt ImageV0.shaFinalizeBlockCode (a - BitVec.ofNat 32 ImageV0.shaFinalizeBlockAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaStoreBeAddress).toNat < ImageV0.shaStoreBeCode.length then
    RV32.byteAt ImageV0.shaStoreBeCode (a - BitVec.ofNat 32 ImageV0.shaStoreBeAddress).toNat
  else witnessMemUpd a

set_option maxRecDepth 200000 in
theorem witnessMemFin_compress :
    RV32.CodeIn witnessMemFin (BitVec.ofNat 32 ImageV0.sha256CompressAddress) ImageV0.sha256CompressCode := by
  intro i hi
  have hlen : ImageV0.sha256CompressCode.length = 11156 := rfl
  have ha : (BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i).toNat = 0x403b32ea + i := by
    have : (BitVec.ofNat 32 ImageV0.sha256CompressAddress).toNat = 0x403b32ea := rfl
    rw [BitVec.toNat_add, this, BitVec.toNat_ofNat]; omega
  have d1 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaFinalizeAddress).toNat < ImageV0.shaFinalizeCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaFinalizeAddress).toNat = 0x403a64e0 from rfl,
      show ImageV0.shaFinalizeCode.length = 280 from rfl]; omega
  have d2 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaFinalizeSaveAddress).toNat < ImageV0.shaFinalizeSaveCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaFinalizeSaveAddress).toNat = 0x403bee66 from rfl,
      show ImageV0.shaFinalizeSaveCode.length = 16 from rfl]; omega
  have d3 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaFinalizeRestoreAddress).toNat < ImageV0.shaFinalizeRestoreCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaFinalizeRestoreAddress).toNat = 0x403bee56 from rfl,
      show ImageV0.shaFinalizeRestoreCode.length = 16 from rfl]; omega
  have d4 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaZero32Address).toNat < ImageV0.shaZero32Code.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaZero32Address).toNat = 0x403acdaa from rfl,
      show ImageV0.shaZero32Code.length = 42 from rfl]; omega
  have d5 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaFinalizeBlockAddress).toNat < ImageV0.shaFinalizeBlockCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaFinalizeBlockAddress).toNat = 0x403a65f8 from rfl,
      show ImageV0.shaFinalizeBlockCode.length = 44 from rfl]; omega
  have d6 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaStoreBeAddress).toNat < ImageV0.shaStoreBeCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaStoreBeAddress).toNat = 0x403bef56 from rfl,
      show ImageV0.shaStoreBeCode.length = 32 from rfl]; omega
  unfold witnessMemFin
  rw [ite_eq_right_of_eq_false _ _ (eq_false d1), ite_eq_right_of_eq_false _ _ (eq_false d2),
    ite_eq_right_of_eq_false _ _ (eq_false d3), ite_eq_right_of_eq_false _ _ (eq_false d4),
    ite_eq_right_of_eq_false _ _ (eq_false d5), ite_eq_right_of_eq_false _ _ (eq_false d6)]
  exact witnessMemUpd_compress i hi

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `finalize` with the empty hasher at `0x3FCC5000`,
the output at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`shaFinalize_correct`'s hypotheses. -/
theorem exists_shaFinalize_machine :
    ∃ (m : RV32.Machine) (S out sp0 retAddr : RV32.Word) (msg : List Nat),
      RV32.FinEnv m.mem S out sp0 ∧ m.pc = BitVec.ofNat 32 ImageV0.shaFinalizeAddress ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = S ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.HasherAt m.mem S msg := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC5000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.shaFinalizeAddress, witnessMemFin⟩,
    0x3FCC5000, 0x3FCC6000, 0x3FCC8000, 0, [],
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, witnessMemFin_compress, ?_, ?_, ?_, by decide, by decide, by decide,
      by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, by decide, rfl, ⟨by decide, ?_, rfl, ?_, ?_, ?_⟩⟩
  all_goals first
    | (unfold RV32.CodeIn; decide +kernel)
    | decide +kernel

/-- `witnessMemFin` with `sha256`, its outlined initializer, and the initial
hash value added where the image loads them. -/
def witnessMemOne (a : RV32.Word) : BitVec 8 :=
  if (a - BitVec.ofNat 32 ImageV0.sha256FnAddress).toNat < ImageV0.sha256FnCode.length then
    RV32.byteAt ImageV0.sha256FnCode (a - BitVec.ofNat 32 ImageV0.sha256FnAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaInitAddress).toNat < ImageV0.shaInitCode.length then
    RV32.byteAt ImageV0.shaInitCode (a - BitVec.ofNat 32 ImageV0.shaInitAddress).toNat
  else if (a - BitVec.ofNat 32 ImageV0.shaIVAddress).toNat < ImageV0.shaIVData.length then
    RV32.byteAt ImageV0.shaIVData (a - BitVec.ofNat 32 ImageV0.shaIVAddress).toNat
  else witnessMemFin a

set_option maxRecDepth 200000 in
theorem witnessMemOne_compress :
    RV32.CodeIn witnessMemOne (BitVec.ofNat 32 ImageV0.sha256CompressAddress) ImageV0.sha256CompressCode := by
  intro i hi
  have hlen : ImageV0.sha256CompressCode.length = 11156 := rfl
  have ha : (BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i).toNat = 0x403b32ea + i := by
    have : (BitVec.ofNat 32 ImageV0.sha256CompressAddress).toNat = 0x403b32ea := rfl
    rw [BitVec.toNat_add, this, BitVec.toNat_ofNat]; omega
  have d1 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.sha256FnAddress).toNat < ImageV0.sha256FnCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.sha256FnAddress).toNat = 0x403a6748 from rfl,
      show ImageV0.sha256FnCode.length = 88 from rfl]; omega
  have d2 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaInitAddress).toNat < ImageV0.shaInitCode.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaInitAddress).toNat = 0x403bf262 from rfl,
      show ImageV0.shaInitCode.length = 22 from rfl]; omega
  have d3 : ¬ ((BitVec.ofNat 32 ImageV0.sha256CompressAddress + BitVec.ofNat 32 i -
      BitVec.ofNat 32 ImageV0.shaIVAddress).toNat < ImageV0.shaIVData.length) := by
    rw [BitVec.toNat_sub, ha, show (BitVec.ofNat 32 ImageV0.shaIVAddress).toNat = 0x3fcc42a8 from rfl,
      show ImageV0.shaIVData.length = 32 from rfl]; omega
  unfold witnessMemOne
  rw [ite_eq_right_of_eq_false _ _ (eq_false d1), ite_eq_right_of_eq_false _ _ (eq_false d2),
    ite_eq_right_of_eq_false _ _ (eq_false d3)]
  exact witnessMemFin_compress i hi

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `sha256` on 3 bytes at `0x3FCC6100`, with the
output at `0x3FCC6000` and the stack at `0x3FCC8000`, meets
`sha256Fn_correct`'s hypotheses. -/
theorem exists_sha256Fn_machine :
    ∃ (m : RV32.Machine) (out D sp0 retAddr : RV32.Word) (n : Nat),
      RV32.Sha256Env m.mem out D sp0 n ∧ m.pc = BitVec.ofNat 32 ImageV0.sha256FnAddress ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = D ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ n < 2 ^ 31 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC6100 else if r = RV32.a2 then 3
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 ImageV0.sha256FnAddress, witnessMemOne⟩,
    0x3FCC6000, 0x3FCC6100, 0x3FCC8000, 0, 3,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, witnessMemOne_compress, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide⟩
  all_goals first
    | (unfold RV32.CodeIn; decide +kernel)
    | decide +kernel

/-- A 12-limb modulus of 3, as bytes: its low limb times `0x55555555` is
`-1` modulo `2^32`. -/
def montModBytes : List Nat := 3 :: List.replicate 47 0

/-- Memory with the current image's `mul_montgomery_form::<12>`,
`square_montgomery_form::<12>`, `Uint<12>::select`, `borrowing_sub`,
`memset`, and `memcpy` where the image loads them, the modulus at
`0x3FCC6600`, and zeros elsewhere. -/
def witnessMemMont : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.mulMont12Address, Image.mulMont12Code),
    (Image.sqMont12Address, Image.sqMont12Code),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (0x3FCC6600, montModBytes)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `mul_montgomery_form::<12>` with the result at
`0x3FCC6000`, the operands at `0x3FCC6400` and `0x3FCC6500`, the modulus 3
at `0x3FCC6600`, `k = 0x55555555`, and the stack at `0x3FCC8000` meets
`mulMont12_correct`'s hypotheses. -/
theorem exists_mulMont12_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp yp np K retAddr : RV32.Word),
      RV32.MMEnv m.mem P sp0 out xp yp np ∧ m.pc = P ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.a2 = yp ∧ RV32.reg m RV32.a3 = np ∧ RV32.reg m RV32.a4 = K ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      (K.toNat * (RV32.memLoad32 m.mem np).toNat + 1) % 2 ^ 32 = 0 ∧
      RV32.accV m.mem yp 12 < RV32.accV m.mem np 12 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC6400 else if r = RV32.a2 then 0x3FCC6500
    else if r = RV32.a3 then 0x3FCC6600 else if r = RV32.a4 then 0x55555555
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.mulMont12Address, witnessMemMont⟩, BitVec.ofNat 32 Image.mulMont12Address,
    0x3FCC8000, 0x3FCC6000, 0x3FCC6400, 0x3FCC6500, 0x3FCC6600, 0x55555555, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, ?_, ?_⟩
  all_goals first
    | code_in
    | decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `square_montgomery_form::<12>` with the result at
`0x3FCC6000`, the operand at `0x3FCC6400`, the modulus 3 at `0x3FCC6600`,
`k = 0x55555555`, and the stack at `0x3FCC8000` meets `sqrMont12_correct`'s
hypotheses. -/
theorem exists_sqrMont12_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp np K retAddr : RV32.Word),
      RV32.SQEnv m.mem P sp0 out xp np ∧ m.pc = P ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.a2 = np ∧ RV32.reg m RV32.a3 = K ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      (K.toNat * (RV32.memLoad32 m.mem np).toNat + 1) % 2 ^ 32 = 0 ∧
      RV32.accV m.mem xp 12 < RV32.accV m.mem np 12 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC6400 else if r = RV32.a2 then 0x3FCC6600
    else if r = RV32.a3 then 0x55555555 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.sqMont12Address, witnessMemMont⟩, BitVec.ofNat 32 Image.sqMont12Address,
    0x3FCC8000, 0x3FCC6000, 0x3FCC6400, 0x3FCC6600, 0x55555555, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, ?_, ?_⟩
  all_goals first
    | code_in
    | decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls the point addition with `lhs` at `0x3FCC5000`, `rhs`
at `0x3FCC6000`, and the stack at `0x3FCC8000` meets `pointAdd_correct`'s
hypotheses, the coordinates' bounds included. -/
theorem exists_pointAdd_machine :
    ∃ (m : RV32.Machine) (P sp0 lhs rhs retAddr : RV32.Word), RV32.PAEnv m.mem P sp0 lhs rhs ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = lhs ∧ RV32.reg m RV32.a1 = rhs ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.limbVal (RV32.wordsAt m.mem lhs 8) < RV32.p256 ∧
      RV32.limbVal (RV32.wordsAt m.mem (lhs + 0x20) 8) < RV32.p256 ∧
      RV32.limbVal (RV32.wordsAt m.mem (lhs + 0x40) 8) < RV32.p256 ∧
      RV32.limbVal (RV32.wordsAt m.mem rhs 8) < RV32.p256 ∧
      RV32.limbVal (RV32.wordsAt m.mem (rhs + 0x20) 8) < RV32.p256 ∧
      RV32.limbVal (RV32.wordsAt m.mem (rhs + 0x40) 8) < RV32.p256 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.pointAddAddress, witnessMemP256⟩, BitVec.ofNat 32 Image.pointAddAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide +kernel,
      by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, by decide, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  all_goals code_in

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `field_impl::sub` with the result at `0x3FCC5000`, the
operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at `0x3FCC8000`
meets `fieldSub_correct`'s hypotheses. -/
theorem exists_fieldSub_machine :
    ∃ (m : RV32.Machine) (P sp0 res ap bp retAddr : RV32.Word), RV32.FSEnv m.mem P sp0 res ap bp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.fieldSubAddress, witnessMemP256⟩, BitVec.ofNat 32 Image.fieldSubAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `field_impl::add` with the result at `0x3FCC5000`, the
operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at `0x3FCC8000`
meets `fieldAdd_correct`'s hypotheses. -/
theorem exists_fieldAdd_machine :
    ∃ (m : RV32.Machine) (P sp0 res ap bp retAddr : RV32.Word), RV32.FAEnv m.mem P sp0 res ap bp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.fieldAddAddress, witnessMemP256⟩, BitVec.ofNat 32 Image.fieldAddAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `FieldElement::double` with the result at
`0x3FCC5000`, the operand at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `fieldDouble_correct`'s hypotheses. -/
theorem exists_fieldDouble_machine :
    ∃ (m : RV32.Machine) (P sp0 res ap retAddr : RV32.Word), RV32.FDEnv m.mem P sp0 res ap ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.fieldDoubleAddress, witnessMemP256⟩, BitVec.ofNat 32 Image.fieldDoubleAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩⟩,
    rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

/-- Memory with the current image's compact `compress256`, `RangeFrom::index`,
`memcpy`, and round constants where the image loads them, and zeros
elsewhere. -/
def witnessMemKC : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.sha256CompressAddress, Image.sha256CompressCode),
    (Image.rangeFromIndexAddress, Image.rangeFromIndexCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.shaKAddress, Image.shaKData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls the compact `compress256` on 2 blocks (`n = 2`) with
the state at `0x3FCC5000`, the blocks at `0x3FCC6000`, and the stack at
`0x3FCC8000` meets `kcCompress_correct`'s hypotheses. -/
theorem exists_kcCompress_machine :
    ∃ (m : RV32.Machine) (P sp0 stp bp retAddr : RV32.Word) (n : Nat),
      RV32.KCEnv m.mem P sp0 stp bp n ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = stp ∧ RV32.reg m RV32.a1 = bp ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ 0 < n := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 2
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.sha256CompressAddress, witnessMemKC⟩,
    BitVec.ofNat 32 Image.sha256CompressAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, 2,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      (RV32.sep_of_le (by decide) (by decide)).symm, RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide⟩
  all_goals code_in

/-- Memory with the current image's P-384 field addition, its callees, and the
modulus where the image loads them, and zeros elsewhere. -/
def witnessMemP384Add : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p384AddAddress, Image.p384AddCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384ModulusAddress, Image.p384ModulusData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `ConstMontyForm<p384::FieldParams, 12>::add` with the
result at `0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and
the stack at `0x3FCC8000` meets `p384Add_correct`'s hypotheses. -/
theorem exists_p384Add_machine :
    ∃ (m : RV32.Machine) (P sp0 out lp rp retAddr : RV32.Word), RV32.P3Env m.mem P sp0 out lp rp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = lp ∧ RV32.reg m RV32.a2 = rp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384AddAddress, witnessMemP384Add⟩, BitVec.ofNat 32 Image.p384AddAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

/-- Memory with the current image's P-384 field subtraction, its callees, and the
modulus where the image loads them, and zeros elsewhere. -/
def witnessMemP384Sub : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p384SubAddress, Image.p384SubCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384ModulusAddress, Image.p384ModulusData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `ConstMontyForm<p384::FieldParams, 12>::sub` with the
result at `0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and
the stack at `0x3FCC8000` meets `p384Sub_correct`'s hypotheses. -/
theorem exists_p384Sub_machine :
    ∃ (m : RV32.Machine) (P sp0 out lp rp retAddr : RV32.Word), RV32.PSEnv m.mem P sp0 out lp rp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = lp ∧ RV32.reg m RV32.a2 = rp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384SubAddress, witnessMemP384Sub⟩, BitVec.ofNat 32 Image.p384SubAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

/-- Memory with the current image's P-384 field doubling, its callees, and
the modulus where the image loads them, and zeros elsewhere. -/
def witnessMemP384Double : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p384DoubleAddress, Image.p384DoubleCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384ModulusAddress, Image.p384ModulusData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls P-384's `FieldElement::double` with the result at `0x3FCC5000`, the operand at `0x3FCC6000`, and the stack at
`0x3FCC8000` meets `p384Double_correct`'s hypotheses. -/
theorem exists_p384Double_machine :
    ∃ (m : RV32.Machine) (P sp0 out sf retAddr : RV32.Word), RV32.PDEnv m.mem P sp0 out sf ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = sf ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384DoubleAddress, witnessMemP384Double⟩,
    BitVec.ofNat 32 Image.p384DoubleAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

/-- Memory with the current image's `FieldElement2625::reduce` where the image
loads it, and zeros elsewhere. -/
def witnessMemFeReduce : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.feReduceAddress, Image.feReduceCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `FieldElement2625::reduce` with the result at
`0x3FCC5000`, the limbs at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`feReduce_correct`'s hypotheses. -/
theorem exists_feReduce_machine :
    ∃ (m : RV32.Machine) (P sp0 out zp retAddr : RV32.Word), RV32.FREnv m.mem P sp0 out zp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = zp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.feReduceAddress, witnessMemFeReduce⟩,
    BitVec.ofNat 32 Image.feReduceAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, by decide, rfl⟩
  code_in

/-- Memory with the current image's `<&FieldElement2625 as Mul>::mul` and
`reduce` where the image loads them, and zeros elsewhere. -/
def witnessMemFeMul : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.feMulAddress, Image.feMulCode),
    (Image.feReduceAddress, Image.feReduceCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `<&FieldElement2625 as Mul>::mul` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC8000` meets `feMul_correct`'s hypotheses. -/
theorem exists_feMul_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp yp retAddr : RV32.Word), RV32.FeMEnv m.mem P sp0 out xp yp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.a2 = yp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.feMulAddress, witnessMemFeMul⟩,
    BitVec.ofNat 32 Image.feMulAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  · code_in
  · code_in

/-- Memory with the current image's `FieldElement2625::square_inner` where the
image loads it, and zeros elsewhere. -/
def witnessMemFeSqInner : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.feSquareInnerAddress, Image.feSquareInnerCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `FieldElement2625::square_inner` with the result at
`0x3FCC6000`, the operand at `0x3FCC5000`, and the stack at `0x3FCC8000` meets
`feSqInner_correct`'s hypotheses. -/
theorem exists_feSqInner_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word), RV32.FeSqEnv m.mem P sp0 out xp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC5000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.feSquareInnerAddress, witnessMemFeSqInner⟩,
    BitVec.ofNat 32 Image.feSquareInnerAddress, 0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0,
    ⟨by decide, ?_, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, by decide, rfl⟩
  code_in

/-- Memory with the current image's `FieldElement2625::square`,
`square_inner`, and `reduce` where the image loads them, and zeros elsewhere. -/
def witnessMemFeSquare : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.feSquareAddress, Image.feSquareCode),
    (Image.feSquareInnerAddress, Image.feSquareInnerCode),
    (Image.feReduceAddress, Image.feReduceCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `FieldElement2625::square` with the result at
`0x3FCC5000`, the operand at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`feSquare_correct`'s hypotheses. -/
theorem exists_feSquare_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word), RV32.FeSquareEnv m.mem P sp0 out xp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.feSquareAddress, witnessMemFeSquare⟩,
    BitVec.ofNat 32 Image.feSquareAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, by decide, rfl⟩
  · code_in
  · code_in
  · code_in

def witnessMemFlashRead : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.flashReadAddress, Image.flashReadCode),
    (Image.romFlashReadWordsAddress, Image.romFlashReadWordsCode),
    (Image.memsetAddress, Image.memsetCode),
    (0x40000130, RV32.romStubCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `flash::read` for 0x40 bytes of flash at 0x10000 into
`0x3FCC5000`, with its stack at `0x3FCC7150` and the ROM stub that always
fails at 0x40000130, meets `flashRead_correct`'s hypotheses, `RomRead`
included. -/
theorem exists_flashRead_machine :
    ∃ (m : RV32.Machine) (P G addr out len retAddr : RV32.Word) (flash : Nat → BitVec 8) (R : Nat)
      (romBase : RV32.Word) (romCode : List Nat), RV32.RomRead flash R romBase romCode ∧
      RV32.FRdEnv m.mem P G out len R romBase romCode ∧ m.pc = P ∧ RV32.reg m RV32.a0 = addr ∧
      RV32.reg m RV32.a1 = out ∧ RV32.reg m RV32.a2 = len ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + BitVec.ofNat 32 (0x150 + R) := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x10000 else if r = RV32.a1 then 0x3FCC5000 else if r = RV32.a2 then 0x40
    else if r = RV32.sp then 0x3FCC7150 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.flashReadAddress, witnessMemFlashRead⟩,
    BitVec.ofNat 32 Image.flashReadAddress, 0x3FCC7000, 0x10000, 0x3FCC5000, 0x40, 0, fun _ => 0, 0,
    0x40000130, RV32.romStubCode, RV32.romStub_read _,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide), ?_,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  · code_in
  · code_in
  · code_in
  · code_in

def witnessMemSelectI64 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.selectI64Address, Image.selectI64Code)]

set_option maxRecDepth 200000 in
/-- A machine that calls `Choice::select_i64` with the stack at `0x3FCC8000`
meets `selectI64_correct`'s hypotheses. -/
theorem exists_selectI64_machine :
    ∃ (m : RV32.Machine) (P retAddr : RV32.Word), RV32.CodeIn m.mem P Image.selectI64Code ∧ m.pc = P ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFF) 1 P Image.selectI64Code.length := by
  let regs : Fin 32 → RV32.Word := fun r => if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.selectI64Address, witnessMemSelectI64⟩,
    BitVec.ofNat 32 Image.selectI64Address, 0, ?_, rfl, rfl, by decide,
    RV32.sep_of_le (by decide) (by decide)⟩
  code_in

def witnessMemFeAdd : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.feAddAddress, Image.feAddCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `<&FieldElement2625 as Add>::add` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC7050` meets `feAdd_correct`'s hypotheses. -/
theorem exists_feAdd_machine :
    ∃ (m : RV32.Machine) (P G out xp yp retAddr : RV32.Word), RV32.FeAddEnv m.mem P G out xp yp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.a2 = yp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x50 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC7050 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.feAddAddress, witnessMemFeAdd⟩,
    BitVec.ofNat 32 Image.feAddAddress, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  · code_in
  · code_in
  · code_in

def witnessMemFeSub : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.feSubAddress, Image.feSubCode),
    (Image.feReduceAddress, Image.feReduceCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `<&FieldElement2625 as Sub>::sub` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC70B0` meets `feSub_correct`'s hypotheses. -/
theorem exists_feSub_machine :
    ∃ (m : RV32.Machine) (P G out xp yp retAddr : RV32.Word), RV32.FeSubEnv m.mem P G out xp yp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.a2 = yp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0xB0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC70B0 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.feSubAddress, witnessMemFeSub⟩,
    BitVec.ofNat 32 Image.feSubAddress, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  · code_in
  · code_in

def witnessMemWideMul12x2 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.wideMul12x2Address, Image.wideMul12x2Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `widening_mul_fixed::<12, 2>` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC7070` meets `wideMul12x2_correct`'s hypotheses. -/
theorem exists_wideMul12x2_machine :
    ∃ (m : RV32.Machine) (P G out xp yp retAddr : RV32.Word), RV32.K12Env m.mem P G out xp yp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.a2 = yp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x70 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC7070 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.wideMul12x2Address, witnessMemWideMul12x2⟩,
    BitVec.ofNat 32 Image.wideMul12x2Address, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  · code_in
  · code_in
  · code_in
  · code_in

def witnessMemWideMul8x2 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.wideMul8x2Address, Image.wideMul8x2Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `widening_mul_fixed::<8, 2>` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC7060` meets `wideMul8x2_correct`'s hypotheses. -/
theorem exists_wideMul8x2_machine :
    ∃ (m : RV32.Machine) (P G out xp yp retAddr : RV32.Word), RV32.K8Env m.mem P G out xp yp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.a2 = yp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x60 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC7060 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.wideMul8x2Address, witnessMemWideMul8x2⟩,
    BitVec.ofNat 32 Image.wideMul8x2Address, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  · code_in
  · code_in
  · code_in
  · code_in

def witnessMemEdDouble : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.edDoubleAddress, Image.edDoubleCode),
    (Image.feSquareAddress, Image.feSquareCode),
    (Image.feSquareInnerAddress, Image.feSquareInnerCode),
    (Image.feReduceAddress, Image.feReduceCode),
    (Image.feAddAddress, Image.feAddCode),
    (Image.feSubAddress, Image.feSubCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `curve25519_dalek`'s `ProjectivePoint::double` with
the result at `0x3FCC5000`, the point at `0x3FCC6000`, and the stack at
`0x3FCC7210` meets `edDouble_correct`'s hypotheses. -/
theorem exists_edDouble_machine :
    ∃ (m : RV32.Machine) (P G out sf retAddr : RV32.Word), RV32.EdDblEnv m.mem P G out sf ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = sf ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x210 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.sp then 0x3FCC7210 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.edDoubleAddress, witnessMemEdDouble⟩,
    BitVec.ofNat 32 Image.edDoubleAddress, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

def witnessMemFePow2k : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.fePow2kAddress, Image.fePow2kCode),
    (Image.feSquareAddress, Image.feSquareCode),
    (Image.feSquareInnerAddress, Image.feSquareInnerCode),
    (Image.feReduceAddress, Image.feReduceCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `FieldElement2625::pow2k` with `k = 3`, the result at
`0x3FCC5000`, the operand at `0x3FCC6000`, and the stack at `0x3FCC7110`
meets `fePow2k_correct`'s hypotheses. -/
theorem exists_fePow2k_machine :
    ∃ (m : RV32.Machine) (P G out xp retAddr : RV32.Word), RV32.FpkEnv m.mem P G out xp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 3 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x110 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 3
    else if r = RV32.sp then 0x3FCC7110 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.fePow2kAddress, witnessMemFePow2k⟩,
    BitVec.ofNat 32 Image.fePow2kAddress, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals code_in

/-- Memory with the current image's `compress512`, `RangeFrom::index`,
`memcpy`, `memset`, and SHA-512's round constants where the image loads them,
and zeros elsewhere. -/
def witnessMemS5 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.sha512CompressAddress, Image.sha512CompressCode),
    (Image.rangeFromIndexAddress, Image.rangeFromIndexCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.sha512KAddress, Image.sha512KData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `compress512` on 2 blocks (`n = 2`) with the state at
`0x3FCC5800`, the blocks at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`s5Compress_correct`'s hypotheses. -/
theorem exists_s5Compress_machine :
    ∃ (m : RV32.Machine) (P sp0 stp bp retAddr : RV32.Word) (n : Nat),
      RV32.S5Env m.mem P sp0 stp bp n ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = stp ∧ RV32.reg m RV32.a1 = bp ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ 0 < n := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5800 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 2
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.sha512CompressAddress, witnessMemS5⟩,
    BitVec.ofNat 32 Image.sha512CompressAddress, 0x3FCC8000, 0x3FCC5800, 0x3FCC6000, 0, 2,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      (RV32.sep_of_le (by decide) (by decide)).symm⟩,
    rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide⟩
  all_goals code_in


/-- Memory with the current image's P-384 point doubling, the field
operations it calls, and the constants they load where the image loads them,
and zeros elsewhere. -/
def witnessMemP384Pt : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p384PtDoubleAddress, Image.p384PtDoubleCode),
    (Image.p384MulAddress, Image.p384MulCode),
    (Image.p384SqrAddress, Image.p384SqrCode),
    (Image.mulMont12Address, Image.mulMont12Code),
    (Image.sqMont12Address, Image.sqMont12Code),
    (Image.p384AddAddress, Image.p384AddCode),
    (Image.p384SubAddress, Image.p384SubCode),
    (Image.p384DoubleAddress, Image.p384DoubleCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384ModulusAddress, Image.p384ModulusData),
    (Image.p384BAddress, Image.p384BData)]

set_option exponentiation.threshold 600 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-384's `FieldElement::mul` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC8000` meets `p384Mul_correct`'s hypotheses. -/
theorem exists_p384Mul_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp yp retAddr : RV32.Word), RV32.P3MEnv m.mem P sp0 out xp yp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.a2 = yp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.limbVal (RV32.wordsAt m.mem yp 12) < RV32.p384 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384MulAddress, witnessMemP384Pt⟩, BitVec.ofNat 32 Image.p384MulAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0, ⟨?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, by decide, rfl, ?_⟩
  case refine_4 =>
    constructor <;> first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option exponentiation.threshold 600 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-384's `FieldElement::square` with the result at
`0x3FCC5000`, the operand at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `p384Sqr_correct`'s hypotheses. -/
theorem exists_p384Sqr_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word), RV32.P3QEnv m.mem P sp0 out xp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.limbVal (RV32.wordsAt m.mem xp 12) < RV32.p384 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384SqrAddress, witnessMemP384Pt⟩, BitVec.ofNat 32 Image.p384SqrAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ⟨?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, by decide, rfl, ?_⟩
  case refine_4 =>
    constructor <;> first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option exponentiation.threshold 600 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-384's point doubling with the result at
`0x3FCC5000`, the point at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`p384PtDouble_correct`'s hypotheses, the coordinates' bounds included. -/
theorem exists_p384PtDouble_machine :
    ∃ (m : RV32.Machine) (P sp0 out sf retAddr : RV32.Word), RV32.D3Env m.mem P sp0 out sf ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = sf ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.limbVal (RV32.wordsAt m.mem sf 12) < RV32.p384 ∧
      RV32.limbVal (RV32.wordsAt m.mem (sf + 0x30) 12) < RV32.p384 ∧
      RV32.limbVal (RV32.wordsAt m.mem (sf + 0x60) 12) < RV32.p384 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384PtDoubleAddress, witnessMemP384Pt⟩,
    BitVec.ofNat 32 Image.p384PtDoubleAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    by decide, rfl, ?_, ?_, ?_⟩
  case refine_1 =>
    constructor <;> first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel


/-- Memory with the current image's P-384 point addition, the field
operations it calls, and the constants they load where the image loads them,
and zeros elsewhere. -/
def witnessMemP384Add3 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p384PtAddAddress, Image.p384PtAddCode),
    (Image.p384MulAddress, Image.p384MulCode),
    (Image.mulMont12Address, Image.mulMont12Code),
    (Image.p384AddAddress, Image.p384AddCode),
    (Image.p384SubAddress, Image.p384SubCode),
    (Image.p384DoubleAddress, Image.p384DoubleCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384ModulusAddress, Image.p384ModulusData),
    (Image.p384BAddress, Image.p384BData)]

set_option exponentiation.threshold 600 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-384's point addition with `lhs` at `0x3FCC5000`,
`rhs` at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`p384PtAdd_correct`'s hypotheses, the coordinates' bounds included. -/
theorem exists_p384PtAdd_machine :
    ∃ (m : RV32.Machine) (P sp0 lhs rhs retAddr : RV32.Word), RV32.A3Env m.mem P sp0 lhs rhs ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = lhs ∧ RV32.reg m RV32.a1 = rhs ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.limbVal (RV32.wordsAt m.mem lhs 12) < RV32.p384 ∧
      RV32.limbVal (RV32.wordsAt m.mem (lhs + 0x30) 12) < RV32.p384 ∧
      RV32.limbVal (RV32.wordsAt m.mem (lhs + 0x60) 12) < RV32.p384 ∧
      RV32.limbVal (RV32.wordsAt m.mem rhs 12) < RV32.p384 ∧
      RV32.limbVal (RV32.wordsAt m.mem (rhs + 0x30) 12) < RV32.p384 ∧
      RV32.limbVal (RV32.wordsAt m.mem (rhs + 0x60) 12) < RV32.p384 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384PtAddAddress, witnessMemP384Add3⟩,
    BitVec.ofNat 32 Image.p384PtAddAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    constructor <;> first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `conditional_negate_in_place_wide::<12, 2>`,
the functions it calls, and `Uint<2>::ZERO` and `Uint<2>::ONE` where the
image loads them, and zeros elsewhere. -/
def witnessMemCN : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.condNeg12Address, Image.condNeg12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Uint<2>::select` with the result at `0x3FCC5000`,
the operands at `0x3FCC6000` and `0x3FCC6100`, the choice 1, and the stack
at `0x3FCC8000` meets `uintSelect2_correct`'s hypotheses. -/
theorem exists_uintSelect2_machine :
    ∃ (m : RV32.Machine) (P sp0 out ap bp c retAddr : RV32.Word),
      RV32.CodeIn m.mem P Image.uintSelect2Code ∧ m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = c ∧
      (c = 0 ∨ c = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      sp0.toNat % 4 = 0 ∧ 16 ≤ sp0.toNat ∧ ap.toNat % 4 = 0 ∧ bp.toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧
      RV32.Sep (sp0 + 0xFFFFFFF0) 16 P Image.uintSelect2Code.length ∧ RV32.Sep out 8 P Image.uintSelect2Code.length ∧
      RV32.Sep ap 8 (sp0 + 0xFFFFFFF0) 16 ∧ RV32.Sep bp 8 (sp0 + 0xFFFFFFF0) 16 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.a3 then 1 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.uintSelect2Address, witnessMemCN⟩, BitVec.ofNat 32 Image.uintSelect2Address,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 1, 0, ?_, rfl, rfl, rfl, rfl, rfl, rfl, .inr rfl, rfl, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option exponentiation.threshold 600 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `conditional_negate_in_place_wide::<12, 2>` with
`lo` at `0x3FCC5000`, `hi` at `0x3FCC6000`, the flag 1, and the stack at
`0x3FCC8000` meets `condNeg12_correct`'s hypotheses. -/
theorem exists_condNeg12_machine :
    ∃ (m : RV32.Machine) (P sp0 lo hi fl retAddr : RV32.Word), RV32.CNEnv m.mem P sp0 lo hi ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = lo ∧ RV32.reg m RV32.a1 = hi ∧ RV32.reg m RV32.a2 = fl ∧
      (fl = 0 ∨ fl = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 1
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.condNeg12Address, witnessMemCN⟩, BitVec.ofNat 32 Image.condNeg12Address,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 1, 0, ?_, rfl, rfl, rfl, rfl, rfl, .inr rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel


/-- Memory with the current image's `conditional_negate_in_place_wide::<8, 2>`,
the functions it calls, and `Uint<2>::ZERO` and `Uint<2>::ONE` where the
image loads them, and zeros elsewhere. -/
def witnessMemC8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.condNeg8Address, Image.condNeg8Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Uint<8>::select` with the result at `0x3FCC5000`,
the operands at `0x3FCC6000` and `0x3FCC6100`, the choice 1, and the stack
at `0x3FCC8000` meets `uintSelect8_correct`'s hypotheses. -/
theorem exists_uintSelect8_machine :
    ∃ (m : RV32.Machine) (S out ap bp c retAddr : RV32.Word),
      RV32.Sel8Env m.mem S (RV32.reg m RV32.sp) out ap bp ∧ m.pc = S ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = c ∧ (c = 0 ∨ c = 1) ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.a3 then 1 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.uintSelect8Address, witnessMemC8⟩, BitVec.ofNat 32 Image.uintSelect8Address,
    0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 1, 0, ?_, rfl, rfl, rfl, rfl, rfl, .inr rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option exponentiation.threshold 600 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `conditional_negate_in_place_wide::<8, 2>` with
`lo` at `0x3FCC5000`, `hi` at `0x3FCC6000`, the flag 1, and the stack at
`0x3FCC8000` meets `condNeg8_correct`'s hypotheses. -/
theorem exists_condNeg8_machine :
    ∃ (m : RV32.Machine) (P sp0 lo hi fl retAddr : RV32.Word), RV32.C8Env m.mem P sp0 lo hi ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = lo ∧ RV32.reg m RV32.a1 = hi ∧ RV32.reg m RV32.a2 = fl ∧
      (fl = 0 ∨ fl = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 1
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.condNeg8Address, witnessMemC8⟩, BitVec.ofNat 32 Image.condNeg8Address,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 1, 0, ?_, rfl, rfl, rfl, rfl, rfl, .inr rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel


/-- Memory with the current image's `Int<2>::abs_sign` and `Int<2>::from_i64`
where the image loads them, and zeros elsewhere. -/
def witnessMemInt2 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.absSign2Address, Image.absSign2Code),
    (Image.fromI64Address, Image.fromI64Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Int<2>::abs_sign` with the result at `0x3FCC5000`,
`x` at `0x3FCC6000`, and the stack at `0x3FCC8000` meets `absSign2_correct`'s
hypotheses. -/
theorem exists_absSign2_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word),
      RV32.CodeIn m.mem P Image.absSign2Code ∧ m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      sp0.toNat % 4 = 0 ∧ 0x20 ≤ sp0.toNat ∧ xp.toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧
      RV32.Sep (sp0 + 0xFFFFFFE0) 0x20 P Image.absSign2Code.length ∧ RV32.Sep out 9 P Image.absSign2Code.length ∧
      RV32.Sep xp 8 (sp0 + 0xFFFFFFE0) 0x20 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.absSign2Address, witnessMemInt2⟩, BitVec.ofNat 32 Image.absSign2Address,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Int<2>::from_i64` with the result at `0x3FCC5000`,
`-2` in `a1` and `a2`, and the stack at `0x3FCC8000` meets
`fromI64_correct`'s hypotheses. -/
theorem exists_fromI64_machine :
    ∃ (m : RV32.Machine) (P sp0 out lo hi retAddr : RV32.Word),
      RV32.CodeIn m.mem P Image.fromI64Code ∧ m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = lo ∧ RV32.reg m RV32.a2 = hi ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ sp0.toNat % 4 = 0 ∧ 16 ≤ sp0.toNat ∧ out.toNat % 4 = 0 ∧
      RV32.Sep (sp0 + 0xFFFFFFF0) 16 P Image.fromI64Code.length ∧ RV32.Sep out 8 P Image.fromI64Code.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0xFFFFFFFE else if r = RV32.a2 then 0xFFFFFFFF
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.fromI64Address, witnessMemInt2⟩, BitVec.ofNat 32 Image.fromI64Address,
    0x3FCC8000, 0x3FCC5000, 0xFFFFFFFE, 0xFFFFFFFF, 0, ?_, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide,
    by decide, by decide, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

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

/-- info: 'C3.RV32.memset_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.memset_correct

/-- info: 'C3.exists_memsetAny_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_memsetAny_machine

/-- info: 'C3.RV32.memcpy_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.memcpy_correct

/-- info: 'C3.exists_memcpyAny_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_memcpyAny_machine

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

/-- info: 'C3.RV32.fm_red' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fm_red

/-- info: 'C3.RV32.fieldMul_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fieldMul_correct

/-- info: 'C3.exists_fieldMul_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fieldMul_machine

/-- info: 'C3.RV32.fieldSub_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fieldSub_correct

/-- info: 'C3.RV32.fieldAdd_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fieldAdd_correct

/-- info: 'C3.RV32.fieldDouble_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fieldDouble_correct

/-- info: 'C3.exists_fieldSub_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fieldSub_machine

/-- info: 'C3.exists_fieldAdd_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fieldAdd_machine

/-- info: 'C3.exists_fieldDouble_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fieldDouble_machine

/-- info: 'C3.RV32.pointAdd_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pointAdd_correct

/-- info: 'C3.exists_pointAdd_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_pointAdd_machine

/-- info: 'C3.RV32.sha_rounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sha_rounds

/-- info: 'C3.RV32.sha256Compress_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sha256Compress_correct

/-- info: 'C3.exists_sha256Compress_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sha256Compress_machine

/-- info: 'C3.RV32.shaBlocks_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.shaBlocks_correct

/-- info: 'C3.RV32.shaUpdate_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.shaUpdate_correct

/-- info: 'C3.exists_shaUpdate_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_shaUpdate_machine

/-- info: 'C3.fullBlocks_fill' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.fullBlocks_fill

/-- info: 'C3.RV32.shaZero32_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.shaZero32_correct

/-- info: 'C3.RV32.shaFinBlock_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.shaFinBlock_correct

/-- info: 'C3.RV32.len_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.len_bytes

/-- info: 'C3.RV32.shaFinalize_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.shaFinalize_correct

/-- info: 'C3.exists_shaFinalize_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_shaFinalize_machine

/-- info: 'C3.RV32.sha256Fn_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sha256Fn_correct

/-- info: 'C3.exists_sha256Fn_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sha256Fn_machine

/-- info: 'C3.RV32.mulMont12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.mulMont12_correct

/-- info: 'C3.RV32.uintSelect12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uintSelect12_correct

/-- info: 'C3.exists_mulMont12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_mulMont12_machine

/-- info: 'C3.RV32.sqrMont12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sqrMont12_correct

/-- info: 'C3.exists_sqrMont12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sqrMont12_machine

/-- info: 'C3.RV32.kcCompress_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.kcCompress_correct

/-- info: 'C3.exists_kcCompress_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_kcCompress_machine

/-- info: 'C3.RV32.p384Add_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384Add_correct

/-- info: 'C3.RV32.p3AddRes_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p3AddRes_mod

/-- info: 'C3.exists_p384Add_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384Add_machine

/-- info: 'C3.RV32.p384Double_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384Double_correct

/-- info: 'C3.exists_p384Double_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384Double_machine

/-- info: 'C3.RV32.p384Sub_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384Sub_correct

/-- info: 'C3.exists_p384Sub_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384Sub_machine

/-- info: 'C3.RV32.feReduce_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feReduce_correct

/-- info: 'C3.exists_feReduce_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feReduce_machine

/-- info: 'C3.RV32.feMul_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feMul_correct

/-- info: 'C3.exists_feMul_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feMul_machine

/-- info: 'C3.RV32.feSqInner_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feSqInner_correct

/-- info: 'C3.exists_feSqInner_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feSqInner_machine

/-- info: 'C3.RV32.feSquare_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feSquare_correct

/-- info: 'C3.exists_feSquare_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feSquare_machine

/-- info: 'C3.RV32.romFlashReadWords_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.romFlashReadWords_correct

/-- info: 'C3.RV32.flashRead_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.flashRead_correct

/-- info: 'C3.RV32.romStub_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.romStub_read

/-- info: 'C3.exists_flashRead_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_flashRead_machine

/-- info: 'C3.RV32.selectI64_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.selectI64_correct

/-- info: 'C3.exists_selectI64_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_selectI64_machine

/-- info: 'C3.RV32.feAdd_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feAdd_correct

/-- info: 'C3.exists_feAdd_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feAdd_machine

/-- info: 'C3.RV32.feSub_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feSub_correct

/-- info: 'C3.exists_feSub_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feSub_machine

/-- info: 'C3.RV32.wideMul12x2_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.wideMul12x2_correct

/-- info: 'C3.exists_wideMul12x2_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_wideMul12x2_machine

/-- info: 'C3.RV32.wideMul8x2_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.wideMul8x2_correct

/-- info: 'C3.exists_wideMul8x2_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_wideMul8x2_machine

/-- info: 'C3.RV32.edDouble_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.edDouble_correct

/-- info: 'C3.exists_edDouble_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_edDouble_machine

/-- info: 'C3.RV32.fePow2k_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fePow2k_correct

/-- info: 'C3.exists_fePow2k_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fePow2k_machine

/-- info: 'C3.RV32.s5Compress_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.s5Compress_correct

/-- info: 'C3.exists_s5Compress_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_s5Compress_machine

/-- info: 'C3.RV32.p384Mul_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384Mul_correct

/-- info: 'C3.exists_p384Mul_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384Mul_machine

/-- info: 'C3.RV32.p384Sqr_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384Sqr_correct

/-- info: 'C3.exists_p384Sqr_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384Sqr_machine

/-- info: 'C3.RV32.p384PtDouble_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384PtDouble_correct

/-- info: 'C3.exists_p384PtDouble_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384PtDouble_machine

/-- info: 'C3.RV32.p384PtAdd_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384PtAdd_correct

/-- info: 'C3.exists_p384PtAdd_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384PtAdd_machine

/-- info: 'C3.RV32.uintSelect2_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uintSelect2_correct

/-- info: 'C3.exists_uintSelect2_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uintSelect2_machine

/-- info: 'C3.RV32.condNeg12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.condNeg12_correct

/-- info: 'C3.exists_condNeg12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_condNeg12_machine

/-- info: 'C3.RV32.uintSelect8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uintSelect8_correct

/-- info: 'C3.exists_uintSelect8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uintSelect8_machine

/-- info: 'C3.RV32.condNeg8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.condNeg8_correct

/-- info: 'C3.exists_condNeg8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_condNeg8_machine

/-- info: 'C3.RV32.absSign2_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.absSign2_correct

/-- info: 'C3.exists_absSign2_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_absSign2_machine

/-- info: 'C3.RV32.fromI64_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fromI64_correct

/-- info: 'C3.exists_fromI64_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fromI64_machine
