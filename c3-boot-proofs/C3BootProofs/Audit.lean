import C3BootProofs.Theorems.TrustRoot
import C3BootProofs.Theorems.Formats
import C3BootProofs.Proofs.Crc32
import C3BootProofs.Proofs.Reader

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
