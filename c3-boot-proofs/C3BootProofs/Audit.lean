import C3BootProofs.Theorems.Trace
import C3BootProofs.Theorems.Formats
import C3BootProofs.Theorems.ImageTake
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
import C3BootProofs.Proofs.P256PtDouble
import C3BootProofs.Proofs.CondNeg12
import C3BootProofs.Proofs.CondNeg8
import C3BootProofs.Proofs.ShrWide12Main
import C3BootProofs.Proofs.LincombInt12
import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.AsProjective
import C3BootProofs.Proofs.AsExtended
import C3BootProofs.Proofs.P384Neg
import C3BootProofs.Proofs.DerOid
import C3BootProofs.Proofs.DerNested
import C3BootProofs.Proofs.SliceEq
import C3BootProofs.Proofs.ShrWide8Main
import C3BootProofs.Proofs.FeToBytes
import C3BootProofs.Proofs.Scalar29Sub
import C3BootProofs.Proofs.LincombInt8
import C3BootProofs.Proofs.MontMul8
import C3BootProofs.Proofs.ScalarMont
import C3BootProofs.Proofs.P256Scalar
import C3BootProofs.Proofs.LincombShift8
import C3BootProofs.Proofs.LincombShiftMod12
import C3BootProofs.Proofs.UpdateDe12
import C3BootProofs.Proofs.UpdateDe8
import C3BootProofs.Proofs.DerReaders
import C3BootProofs.Proofs.DerOptional
import C3BootProofs.Proofs.UintEq
import C3BootProofs.Proofs.ByteCompare
import C3BootProofs.Proofs.P384Scalar
import C3BootProofs.Proofs.Prim
import C3BootProofs.Proofs.CtEq
import C3BootProofs.Proofs.MontRetrieve12
import C3BootProofs.Proofs.P384Retrieve
import C3BootProofs.Proofs.CtAssign
import C3BootProofs.Proofs.ZipNext
import C3BootProofs.Proofs.DerPositive
import C3BootProofs.Proofs.DerScalar32
import C3BootProofs.Proofs.EcdsaSig
import C3BootProofs.Proofs.IntegerIs
import C3BootProofs.Proofs.CheckpointLine
import C3BootProofs.Proofs.Sec1Tag
import C3BootProofs.Proofs.TimeDigits
import C3BootProofs.Proofs.P256Neg
import C3BootProofs.Proofs.ScalarIsZero256
import C3BootProofs.Proofs.Arr32Eq
import C3BootProofs.Proofs.CtWrap
import C3BootProofs.Proofs.TagAndThen
import C3BootProofs.Proofs.CondSelect
import C3BootProofs.Proofs.NonZero384
import C3BootProofs.Proofs.FeIsNeg
import C3BootProofs.Proofs.Ashldi3
import C3BootProofs.Proofs.DerAlgorithm
import C3BootProofs.Proofs.ListsOid
import C3BootProofs.Proofs.LeadingZeros
import C3BootProofs.Proofs.FeLoad
import C3BootProofs.Proofs.FeCtEq
import C3BootProofs.Proofs.AsProjNiels
import C3BootProofs.Proofs.IsSha256
import C3BootProofs.Proofs.FeCall
import C3BootProofs.Proofs.EdNiels
import C3BootProofs.Proofs.Pow22501
import C3BootProofs.Proofs.FeCondAssign
import C3BootProofs.Proofs.FeNeg
import C3BootProofs.Proofs.FeCondNeg
import C3BootProofs.Proofs.Select
import C3BootProofs.Proofs.Scalar29Pack
import C3BootProofs.Proofs.IncrementLimb
import C3BootProofs.Proofs.NonAdjacentForm
import C3BootProofs.Proofs.LincombShiftMod8
import C3BootProofs.Proofs.Lowest
import C3BootProofs.Proofs.Norm12
import C3BootProofs.Proofs.Norm8
import C3BootProofs.Proofs.ToUintResize
import C3BootProofs.Proofs.UpdateFg8
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
import C3BootProofs.Proofs.MemsetAny
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.Sha2OneShot
import C3BootProofs.Proofs.Sha2Finish
import C3BootProofs.Proofs.Sha2Parts
import C3BootProofs.Proofs.MerkleNode
import C3BootProofs.Proofs.RootFromInclusion
import C3BootProofs.Proofs.EncodedPoint
import C3BootProofs.Proofs.Sha512Blocks
import C3BootProofs.Proofs.CtInto
import C3BootProofs.Proofs.ZeroArray
import C3BootProofs.Proofs.ToBeBytes
import C3BootProofs.Proofs.P256Retrieve
import C3BootProofs.Proofs.P384FromRepr
import C3BootProofs.Proofs.P256FromRepr
import C3BootProofs.Proofs.FromBeSliceTrunc
import C3BootProofs.Proofs.Bytes2Scalar256
import C3BootProofs.Proofs.ScalarFromSlice256
import C3BootProofs.Proofs.IsSmallOrder
import C3BootProofs.Proofs.DateTime
import C3BootProofs.Proofs.X509ReadTime
import C3BootProofs.Proofs.TimeRfc3339
import C3BootProofs.Proofs.ParseSpecCur
import C3BootProofs.Proofs.Base64Decode
import C3BootProofs.Proofs.Base64Encode
import C3BootProofs.Proofs.Sha512UpdateArr32
import C3BootProofs.Proofs.EdDecompress
import C3BootProofs.Proofs.EdVerifyingKey
import C3BootProofs.Proofs.Ed25519PkOk
import C3BootProofs.Proofs.EdNafTable
import C3BootProofs.Proofs.Wnaf
import C3BootProofs.Spec.Ecdsa
import C3BootProofs.Proofs.MontMul12Main
import C3BootProofs.Proofs.SqrMont12Main
import C3BootProofs.Image.BootloaderV0
import C3BootProofs.Proofs.Ed25519VerifyWitness
import C3BootProofs.Proofs.MagicCur
import C3BootProofs.Proofs.PartCur
import C3BootProofs.Proofs.SmallFns
import C3BootProofs.Proofs.Bundle
import C3BootProofs.Proofs.BsDecode
import C3BootProofs.Proofs.ImageTopCur
import C3BootProofs.Proofs.BootWrite
import C3BootProofs.Proofs.Boot
import C3BootProofs.Proofs.BootLevel
import C3BootProofs.Proofs.Dec384End
import C3BootProofs.Proofs.Fs384Main
import C3BootProofs.Proofs.Fs256Main
import C3BootProofs.Proofs.Dec256End
import C3BootProofs.Proofs.Pv384Main
import C3BootProofs.Proofs.Pv384Np
import C3BootProofs.Image.BootloaderData5
import C3BootProofs.Image.BootloaderData7
import C3BootProofs.Proofs.P2vP256
import C3BootProofs.Proofs.SvLib
import C3BootProofs.Proofs.SvVerifyAt
import C3BootProofs.Proofs.SvSpec
import C3BootProofs.Models.EcdsaClosed
import C3BootProofs.Models.Ed25519Closed
import C3BootProofs.Proofs.TufIndex
import C3BootProofs.Proofs.TufHex
import C3BootProofs.Proofs.AsciiDigits
import C3BootProofs.Proofs.FlashPart
import C3BootProofs.Proofs.StripPrefix
import C3BootProofs.Proofs.EfuseRun
import C3BootProofs.Proofs.TufHexDecode
import C3BootProofs.Proofs.TufReadDoc
import C3BootProofs.Proofs.EcdsaSig32
import C3BootProofs.Proofs.Sha384Fn
import C3BootProofs.Proofs.JsonSkipWs
import C3BootProofs.Proofs.JsonStringEnd
import C3BootProofs.Proofs.JsonNumberEnd
import C3BootProofs.Proofs.JsonKeyEnd
import C3BootProofs.Proofs.JsonStr
import C3BootProofs.Proofs.JsonMembers
import C3BootProofs.Proofs.JsonLiteralEnd
import C3BootProofs.Proofs.JsonU64
import C3BootProofs.Proofs.JsonReadItem
import C3BootProofs.Proofs.JsonNextElement
import C3BootProofs.Proofs.JsonNextMember
import C3BootProofs.Proofs.JsonGet
import C3BootProofs.Proofs.JsonField
import C3BootProofs.Proofs.JsonParseModel
import C3BootProofs.Proofs.JsonParseFrame
import C3BootProofs.Proofs.JsonParseKeys
import C3BootProofs.Proofs.JsonParseStrict
import C3BootProofs.Proofs.JsonParseClose
import C3BootProofs.Proofs.JsonParseLoop
import C3BootProofs.Proofs.JsonParseItem
import C3BootProofs.Proofs.JsonParseOuter
import C3BootProofs.Proofs.JsonParseEnd
import C3BootProofs.Proofs.JsonParse
import C3BootProofs.Proofs.TufExpires
import C3BootProofs.Proofs.TufPemSpki
import C3BootProofs.Proofs.TufParseMetadataHead
import C3BootProofs.Proofs.TufParseRoot
import C3BootProofs.Proofs.TufRoleKeysRead
import C3BootProofs.Proofs.TufRoleKeysMetSpec
import C3BootProofs.Proofs.TufRoleKeysMetResult
import C3BootProofs.Proofs.TrustedRootDecode
import C3BootProofs.Proofs.TrustedRootValidFor
import C3BootProofs.Proofs.TrustedRootReadChainAt
import C3BootProofs.Proofs.TrustedRootReadChainCalls
import C3BootProofs.Proofs.TrustedRootReadChainCtx
import C3BootProofs.Proofs.TrustedRootReadChainDer
import C3BootProofs.Proofs.TrustedRootReadChainFrame
import C3BootProofs.Proofs.TrustedRootReadChainKey
import C3BootProofs.Proofs.TrustedRootReadChainKeySeg
import C3BootProofs.Proofs.TrustedRootReadChainModel
import C3BootProofs.Proofs.TrustedRootReadChainParse
import C3BootProofs.Proofs.TrustedRootReadChainParseTop
import C3BootProofs.Proofs.TrustedRootReadChainRec
import C3BootProofs.Proofs.TrustedRootReadChainLoop
import C3BootProofs.Proofs.TrustedRootReadChainFin
import C3BootProofs.Proofs.TrustedRootReadChainHead
import C3BootProofs.Proofs.TrustedRootReadChainErr
import C3BootProofs.Proofs.TrustedRootReadChain
import C3BootProofs.Proofs.TrustedRootLift
import C3BootProofs.Proofs.TrustedRootLiftDer
import C3BootProofs.Proofs.TrustedRootLiftKey
import C3BootProofs.Proofs.TrustedRootLiftCert
import C3BootProofs.Proofs.TrustedRootLiftChain
import C3BootProofs.Models.JsonLinkWalk
import C3BootProofs.Models.JsonLinkValue
import C3BootProofs.Models.JsonLinkParse
import C3BootProofs.Models.JsonLinkUnique
import C3BootProofs.Models.JsonLinkCanon
import C3BootProofs.Models.TufLink
import C3BootProofs.Models.TufLinkMeta
import C3BootProofs.Models.TufLinkKeys
import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.AcceptImageSpec
import C3BootProofs.Proofs.AcceptImage
import C3BootProofs.Proofs.AcceptFinish
import C3BootProofs.Proofs.SvErrBound
import C3BootProofs.Proofs.BootMainRecord
import C3BootProofs.Proofs.BootMainContract
import C3BootProofs.Proofs.BootMainSpec
import C3BootProofs.Proofs.BootMainTail
import C3BootProofs.Proofs.BootMainPick
import C3BootProofs.Proofs.BootMainWrite
import C3BootProofs.Proofs.BootMainDecide
import C3BootProofs.Proofs.BootMainPlan
import C3BootProofs.Proofs.BootMainEntry
import C3BootProofs.Proofs.BootMainStart
import C3BootProofs.Proofs.AcceptPinned
import C3BootProofs.Proofs.AcceptIndex
import C3BootProofs.Proofs.AcceptRead
import C3BootProofs.Proofs.AcceptTargetsTop
import C3BootProofs.Proofs.AcceptRoots
import C3BootProofs.Proofs.AcceptExtractTail
import C3BootProofs.Proofs.AcceptExtractErr
import C3BootProofs.Proofs.AcceptExtractHeadLib
import C3BootProofs.Proofs.AcceptExtractHead
import C3BootProofs.Proofs.AcceptBundle
import C3BootProofs.Proofs.ResetPath
import C3BootProofs.Proofs.Reset
import C3BootProofs.Proofs.AcceptSpec
import C3BootProofs.Proofs.AcceptExtractDup
import C3BootProofs.Proofs.AcceptExtractTsa
import C3BootProofs.Proofs.AcceptExtractCa
import C3BootProofs.Proofs.ResetLoaded
import C3BootProofs.Proofs.PanicFree
import C3BootProofs.Proofs.PanicFreeTargets
import C3BootProofs.Proofs.SramAlias
import C3BootProofs.Proofs.AcceptExtractTlogStage

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
    (Image.p256PtDoubleAddress, Image.p256PtDoubleCode),
    (Image.fieldSquareAddress, Image.fieldSquareCode),
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

/-- The hasher of the empty message: an empty buffer, the initial hash value
as the image stores it, and a block count of zero. -/
def emptyHasherBytes : List Nat := List.replicate 64 0 ++ Image.shaIVData ++ List.replicate 8 0

/-- Memory with the empty hasher at `0x3FCC5100`, and the current image's
`update`, `finalize`, `sha256`, their helpers, the zeroing `from_fn`s, both `to_be_byte_array`s, `node_hash`,
`root_from_inclusion`, `compress256` with its
helpers, `memset`, `memcpy`, the initial hash value, and the round constants
where the image loads them, and zeros elsewhere. -/
def witnessMemSha2 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(0x3FCC5100, emptyHasherBytes),
    (Image.shaUpdateAddress, Image.shaUpdateCode),
    (Image.shaUpdateBlocksAddress, Image.shaUpdateBlocksCode),
    (Image.shaFinalizeAddress, Image.shaFinalizeCode),
    (Image.shaZero32Address, Image.shaZero32Code),
    (Image.zeroArray48Address, Image.zeroArray48Code),
    (Image.zeroArray64Address, Image.zeroArray64Code),
    (Image.toBeBytes12Address, Image.toBeBytes12Code),
    (Image.toBeBytes8Address, Image.toBeBytes8Code),
    (Image.shaFinBlockAddress, Image.shaFinBlockCode),
    (Image.sha256FnAddress, Image.sha256FnCode),
    (Image.shaFinishAddress, Image.shaFinishCode),
    (Image.sha256PartsAddress, Image.sha256PartsCode),
    (Image.merkleNodeHashAddress, Image.merkleNodeHashCode),
    (Image.rootFromInclusionAddress, Image.rootFromInclusionCode),
    (Image.merklePrefixAddress, Image.merklePrefixData),
    (0x3FCC6200, [0x00, 0x61, 0xCC, 0x3F, 3, 0, 0, 0, 0x10, 0x61, 0xCC, 0x3F, 5, 0, 0, 0]),
    (Image.sha256CompressAddress, Image.sha256CompressCode),
    (Image.rangeFromIndexAddress, Image.rangeFromIndexCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.shaIVAddress, Image.shaIVData),
    (Image.shaKAddress, Image.shaKData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `update` with 100 bytes at `0x3FCC6000`, the empty
hasher at `0x3FCC5100`, and the stack at `0x3FCC8000` meets
`shaUpdate_correct`'s hypotheses. -/
theorem exists_shaUpdate_machine :
    ∃ (m : RV32.Machine) (S D sp0 retAddr : RV32.Word) (n : Nat) (msg : List Nat),
      RV32.UpdEnv m.mem S D sp0 n ∧ m.pc = BitVec.ofNat 32 Image.shaUpdateAddress ∧
      RV32.reg m RV32.a0 = S ∧ RV32.reg m RV32.a1 = D ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.HasherAt m.mem S msg ∧ n < 2 ^ 31 ∧ msg.length + n < 2 ^ 32 := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC5100 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 100
      else if r = RV32.sp then 0x3FCC8000 else 0), BitVec.ofNat 32 Image.shaUpdateAddress,
      witnessMemSha2⟩,
    0x3FCC5100, 0x3FCC6000, 0x3FCC8000, 0, 100, [], ?_, rfl, rfl, rfl, rfl, rfl, by decide, rfl,
    ⟨by decide, ?_, rfl, ?_, ?_, ?_⟩, by decide, by decide⟩
  case refine_1 =>
    constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `finalize` with the empty hasher at `0x3FCC5100`,
the output at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`shaFinalize_correct`'s hypotheses. -/
theorem exists_shaFinalize_machine :
    ∃ (m : RV32.Machine) (S out sp0 retAddr : RV32.Word) (msg : List Nat),
      RV32.FinEnv m.mem S out sp0 ∧ m.pc = BitVec.ofNat 32 Image.shaFinalizeAddress ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = S ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.HasherAt m.mem S msg := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0
      else if r = RV32.sp then 0x3FCC8000 else 0), BitVec.ofNat 32 Image.shaFinalizeAddress,
      witnessMemSha2⟩,
    0x3FCC5100, 0x3FCC6000, 0x3FCC8000, 0, [], ?_, rfl, rfl, rfl, rfl, by decide, rfl,
    ⟨by decide, ?_, rfl, ?_, ?_, ?_⟩⟩
  case refine_1 =>
    constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `sha256` on 3 bytes at `0x3FCC6100`, with the
output at `0x3FCC6000` and the stack at `0x3FCC8000`, meets
`sha256Fn_correct`'s hypotheses. -/
theorem exists_sha256Fn_machine :
    ∃ (m : RV32.Machine) (out D sp0 retAddr : RV32.Word) (n : Nat),
      RV32.Sha256Env m.mem out D sp0 n ∧ m.pc = BitVec.ofNat 32 Image.sha256FnAddress ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = D ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ n < 2 ^ 31 := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC6100 else if r = RV32.a2 then 3
      else if r = RV32.sp then 0x3FCC8000 else 0), BitVec.ofNat 32 Image.sha256FnAddress,
      witnessMemSha2⟩,
    0x3FCC6000, 0x3FCC6100, 0x3FCC8000, 0, 3, ?_, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Sha256::finish` with the empty hasher at
`0x3FCC5100`, the output at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `shaFinish_correct`'s hypotheses. -/
theorem exists_shaFinish_machine :
    ∃ (m : RV32.Machine) (S out sp0 retAddr : RV32.Word) (msg : List Nat),
      RV32.FinishEnv m.mem S out sp0 ∧ m.pc = BitVec.ofNat 32 Image.shaFinishAddress ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = S ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.HasherAt m.mem S msg := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC5100
      else if r = RV32.sp then 0x3FCC8000 else 0), BitVec.ofNat 32 Image.shaFinishAddress, witnessMemSha2⟩,
    0x3FCC5100, 0x3FCC6000, 0x3FCC8000, 0, [], ?_, rfl, rfl, rfl, rfl, by decide, rfl,
    ⟨by decide, ?_, rfl, ?_, ?_, ?_⟩⟩
  case refine_1 =>
    constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `sha256_parts` on two slices, 3 bytes at
`0x3FCC6100` and 5 bytes at `0x3FCC6110`, whose descriptors are at
`0x3FCC6200`, with the output at `0x3FCC6000` and the stack at
`0x3FCC8000`, meets `sha256Parts_correct`'s hypotheses. -/
theorem exists_sha256Parts_machine :
    ∃ (m : RV32.Machine) (out P sp0 retAddr : RV32.Word) (k : Nat),
      RV32.PartsEnv m.mem out P sp0 k ∧ m.pc = BitVec.ofNat 32 Image.sha256PartsAddress ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = P ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 k ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC6200
      else if r = RV32.a2 then 2 else if r = RV32.sp then 0x3FCC8000 else 0),
      BitVec.ofNat 32 Image.sha256PartsAddress, witnessMemSha2⟩,
    0x3FCC6000, 0x3FCC6200, 0x3FCC8000, 0, 2, ?_, rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  constructor
  case parts =>
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      exact ⟨by decide +kernel, by decide +kernel, RV32.sep_of_le (by decide +kernel) (by decide +kernel)⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `node_hash` with the hashes at `0x3FCC5200` and
`0x3FCC5300`, the output at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `merkleNodeHash_correct`'s hypotheses. -/
theorem exists_merkleNodeHash_machine :
    ∃ (m : RV32.Machine) (out L Rt sp0 retAddr : RV32.Word),
      RV32.NodeEnv m.mem out L Rt sp0 ∧ m.pc = BitVec.ofNat 32 Image.merkleNodeHashAddress ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = L ∧ RV32.reg m RV32.a2 = Rt ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC5200
      else if r = RV32.a2 then 0x3FCC5300 else if r = RV32.sp then 0x3FCC8000 else 0),
      BitVec.ofNat 32 Image.merkleNodeHashAddress, witnessMemSha2⟩,
    0x3FCC6000, 0x3FCC5200, 0x3FCC5300, 0x3FCC8000, 0, ?_, rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `root_from_inclusion` for index 0 of a 2-leaf tree,
with the leaf hash at `0x3FCC5200`, one 32-byte proof hash at `0x3FCC5300`,
the result at `0x3FCC6000`, and the stack at `0x3FCC8000`, meets
`rootFromInclusion_correct`'s hypotheses. -/
theorem exists_rootFromInclusion_machine :
    ∃ (m : RV32.Machine) (out L Pp sp0 retAddr : RV32.Word) (n : Nat),
      RV32.RootEnv m.mem out L Pp sp0 n ∧ m.pc = BitVec.ofNat 32 Image.rootFromInclusionAddress ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a5 = L ∧ RV32.reg m RV32.a6 = Pp ∧
      RV32.reg m RV32.a7 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a3 then 2
      else if r = RV32.a5 then 0x3FCC5200 else if r = RV32.a6 then 0x3FCC5300 else if r = RV32.a7 then 32
      else if r = RV32.sp then 0x3FCC8000 else 0),
      BitVec.ofNat 32 Image.rootFromInclusionAddress, witnessMemSha2⟩,
    0x3FCC6000, 0x3FCC5200, 0x3FCC5300, 0x3FCC8000, 0, 32, ?_, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that zeroes 48 bytes at `0x3FCC6000` with the stack at
`0x3FCC8000` meets `zeroArray48_correct`'s hypotheses. -/
theorem exists_zeroArray48_machine :
    ∃ (m : RV32.Machine) (d T retAddr : RV32.Word),
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.zeroArray48Address) Image.zeroArray48Code ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.memcpyStubAddress) Image.memcpyStubCode ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.memcpyStubAddress + 8) Image.memcpyBodyCode ∧
      m.pc = BitVec.ofNat 32 Image.zeroArray48Address ∧ RV32.reg m RV32.a0 = d ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = T ∧ T.toNat % 16 = 0 ∧ 0x50 ≤ T.toNat ∧
      T.toNat ≤ 0x40000000 ∧ d.toNat + 48 ≤ 0x40000000 ∧ RV32.Sep d 48 (T + 0xFFFFFFB0) 0x50 := by
  refine ⟨⟨fun r => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.sp then 0x3FCC8000 else 0,
      BitVec.ofNat 32 Image.zeroArray48Address, witnessMemSha2⟩, 0x3FCC6000, 0x3FCC8000, 0,
    by code_in, by code_in, by code_in, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide)⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that zeroes 64 bytes at `0x3FCC6000` with the stack at
`0x3FCC8000` meets `zeroArray64_correct`'s hypotheses. -/
theorem exists_zeroArray64_machine :
    ∃ (m : RV32.Machine) (d T retAddr : RV32.Word),
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.zeroArray64Address) Image.zeroArray64Code ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.memcpyStubAddress) Image.memcpyStubCode ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.memcpyStubAddress + 8) Image.memcpyBodyCode ∧
      m.pc = BitVec.ofNat 32 Image.zeroArray64Address ∧ RV32.reg m RV32.a0 = d ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = T ∧ T.toNat % 16 = 0 ∧ 0x60 ≤ T.toNat ∧
      T.toNat ≤ 0x40000000 ∧ d.toNat + 64 ≤ 0x40000000 ∧ RV32.Sep d 64 (T + 0xFFFFFFA0) 0x60 := by
  refine ⟨⟨fun r => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.sp then 0x3FCC8000 else 0,
      BitVec.ofNat 32 Image.zeroArray64Address, witnessMemSha2⟩, 0x3FCC6000, 0x3FCC8000, 0,
    by code_in, by code_in, by code_in, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide)⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that encodes the 12 limbs at `0x3FCC5100` big-endian to
`0x3FCC6000` with the stack at `0x3FCC8000` meets `toBeBytes12_correct`'s
hypotheses. -/
theorem exists_toBeBytes12_machine :
    ∃ (m : RV32.Machine) (out s sp0 retAddr : RV32.Word),
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.toBeBytes12Address) Image.toBeBytes12Code ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.zeroArray48Address) Image.zeroArray48Code ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.memcpyStubAddress) Image.memcpyStubCode ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.memcpyStubAddress + 8) Image.memcpyBodyCode ∧
      m.pc = BitVec.ofNat 32 Image.toBeBytes12Address ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = s ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      sp0.toNat % 16 = 0 ∧ 0x90 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧ s.toNat % 4 = 0 ∧
      s.toNat + 48 ≤ 0x40000000 ∧ out.toNat + 48 ≤ 0x40000000 ∧ RV32.Sep s 48 (sp0 + 0xFFFFFF70) 0x90 ∧
      RV32.Sep out 48 (sp0 + 0xFFFFFF70) 0x90 :=
  ⟨⟨fun r => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.sp then 0x3FCC8000
      else 0, BitVec.ofNat 32 Image.toBeBytes12Address, witnessMemSha2⟩, 0x3FCC6000, 0x3FCC5100, 0x3FCC8000, 0,
    by code_in, by code_in, by code_in, by code_in, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide,
    by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that encodes the 8 limbs at `0x3FCC5100` big-endian to
`0x3FCC6000` with the stack at `0x3FCC8000` meets `toBeBytes8_correct`'s
hypotheses. -/
theorem exists_toBeBytes8_machine :
    ∃ (m : RV32.Machine) (out s sp0 retAddr : RV32.Word),
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.toBeBytes8Address) Image.toBeBytes8Code ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.shaZero32Address) Image.shaZero32Code ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.memcpyStubAddress) Image.memcpyStubCode ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.memcpyStubAddress + 8) Image.memcpyBodyCode ∧
      m.pc = BitVec.ofNat 32 Image.toBeBytes8Address ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = s ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      sp0.toNat % 16 = 0 ∧ 0x70 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧ s.toNat % 4 = 0 ∧
      s.toNat + 32 ≤ 0x40000000 ∧ out.toNat + 32 ≤ 0x40000000 ∧ RV32.Sep s 32 (sp0 + 0xFFFFFF90) 0x70 ∧
      RV32.Sep out 32 (sp0 + 0xFFFFFF90) 0x70 :=
  ⟨⟨fun r => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.sp then 0x3FCC8000
      else 0, BitVec.ofNat 32 Image.toBeBytes8Address, witnessMemSha2⟩, 0x3FCC6000, 0x3FCC5100, 0x3FCC8000, 0,
    by code_in, by code_in, by code_in, by code_in, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide,
    by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `FieldElement::square` with the result at
`0x3FCC5000`, the operand at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `fieldSquare_correct`'s hypotheses. -/
theorem exists_fieldSquare_machine :
    ∃ (m : RV32.Machine) (P sp0 res ap retAddr : RV32.Word), RV32.FQEnv m.mem P sp0 res ap ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.fieldSquareAddress, witnessMemP256⟩, BitVec.ofNat 32 Image.fieldSquareAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ⟨by decide, ?_, ?_⟩, rfl, rfl, rfl, rfl, by decide, rfl⟩
  all_goals first
    | code_in
    | (constructor <;> first
        | code_in
        | decide
        | exact RV32.sep_of_le (by decide) (by decide)
        | exact (RV32.sep_of_le (by decide) (by decide)).symm
        | decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-256's point doubling with the result at
`0x3FCC5000`, the point at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`p256PtDouble_correct`'s hypotheses, the coordinates' bounds included. -/
theorem exists_p256PtDouble_machine :
    ∃ (m : RV32.Machine) (P sp0 out sf retAddr : RV32.Word), RV32.D2Env m.mem P sp0 out sf ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = sf ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.limbVal (RV32.wordsAt m.mem sf 8) < RV32.p256 ∧
      RV32.limbVal (RV32.wordsAt m.mem (sf + 0x20) 8) < RV32.p256 ∧
      RV32.limbVal (RV32.wordsAt m.mem (sf + 0x40) 8) < RV32.p256 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p256PtDoubleAddress, witnessMemP256⟩,
    BitVec.ofNat 32 Image.p256PtDoubleAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    by decide, rfl, ?_, ?_, ?_⟩
  case refine_1 =>
    constructor <;> first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals first
    | decide
    | decide +kernel

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
the state at `0x3FCC5100`, the blocks at `0x3FCC6000`, and the stack at
`0x3FCC8000` meets `kcCompress_correct`'s hypotheses. -/
theorem exists_kcCompress_machine :
    ∃ (m : RV32.Machine) (P sp0 stp bp retAddr : RV32.Word) (n : Nat),
      RV32.KCEnv m.mem P sp0 stp bp n ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = stp ∧ RV32.reg m RV32.a1 = bp ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ 0 < n := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5100 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 2
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.sha256CompressAddress, witnessMemKC⟩,
    BitVec.ofNat 32 Image.sha256CompressAddress, 0x3FCC8000, 0x3FCC5100, 0x3FCC6000, 0, 2,
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
`memcpy`, `memset`, SHA-512's round constants, and the two block closures
where the image loads them, and zeros elsewhere. -/
def witnessMemS5 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.sha512CompressAddress, Image.sha512CompressCode),
    (Image.rangeFromIndexAddress, Image.rangeFromIndexCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.sha512KAddress, Image.sha512KData),
    (Image.sha512FinBlockAddress, Image.sha512FinBlockCode),
    (Image.sha384UpdateBlocksAddress, Image.sha384UpdateBlocksCode)]

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


set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls the single-block finalize closure with the state at
`0x3FCC5800`, the block at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`sha512FinBlock_correct`'s hypotheses. -/
theorem exists_sha512FinBlock_machine :
    ∃ (m : RV32.Machine) (st blk sp0 retAddr : RV32.Word),
      RV32.FB5Env m.mem st blk sp0 ∧ m.pc = BitVec.ofNat 32 Image.sha512FinBlockAddress ∧
      RV32.reg m RV32.a0 = st ∧ RV32.reg m RV32.a1 = blk ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5800 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.sha512FinBlockAddress, witnessMemS5⟩,
    0x3FCC5800, 0x3FCC6000, 0x3FCC8000, 0, ?_, rfl, rfl, rfl, rfl, by decide, rfl⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- A machine that calls `update`'s block closure on 2 blocks at `0x3FCC6000`
with the state at `0x3FCC5800`, a zero count, and the stack at `0x3FCC8000`
meets `sha384UpdateBlocks_correct`'s hypotheses. -/
theorem exists_sha384UpdateBlocks_machine :
    ∃ (m : RV32.Machine) (st bp sp0 retAddr : RV32.Word) (n : Nat),
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.sha384UpdateBlocksAddress) Image.sha384UpdateBlocksCode ∧
      m.pc = BitVec.ofNat 32 Image.sha384UpdateBlocksAddress ∧
      RV32.S5Env m.mem (BitVec.ofNat 32 Image.sha512CompressAddress) sp0 st bp n ∧
      RV32.reg m RV32.a0 = st ∧ RV32.reg m RV32.a1 = bp ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      (RV32.memLoad32 m.mem (st + 0x40)).toNat + n < 2 ^ 32 ∧
      RV32.Sep (st + 0x40) 16 (BitVec.ofNat 32 Image.sha512CompressAddress) Image.sha512CompressCode.length ∧
      RV32.Sep (st + 0x40) 16 (BitVec.ofNat 32 Image.sha512CompressAddress + 0xFFFFFFEA)
        Image.rangeFromIndexCode.length ∧
      RV32.Sep (st + 0x40) 16 (BitVec.ofNat 32 Image.sha512CompressAddress + 0x5AC) Image.memcpyStubCode.length ∧
      RV32.Sep (st + 0x40) 16 (BitVec.ofNat 32 Image.sha512CompressAddress + 0x5B4) Image.memcpyBodyCode.length ∧
      RV32.Sep (st + 0x40) 16 (BitVec.ofNat 32 Image.sha512CompressAddress + 0x544) Image.memsetCode.length ∧
      RV32.Sep (st + 0x40) 16 (BitVec.ofNat 32 Image.sha512KAddress) 640 ∧
      RV32.Sep (st + 0x40) 16 (sp0 + 0xFFFFFC70) 0x390 ∧ RV32.Sep bp (128 * n) (st + 0x40) 16 ∧
      RV32.Sep (st + 0x40) 16 (BitVec.ofNat 32 Image.sha384UpdateBlocksAddress)
        Image.sha384UpdateBlocksCode.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5800 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 2
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.sha384UpdateBlocksAddress, witnessMemS5⟩,
    0x3FCC5800, 0x3FCC6000, 0x3FCC8000, 0, 2, by code_in, rfl,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
      RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
      (RV32.sep_of_le (by decide) (by decide)).symm⟩,
    rfl, rfl, rfl, rfl, by decide, rfl, by decide +kernel,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
    RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm,
    RV32.sep_of_le (by decide) (by decide)⟩
  all_goals code_in

/-- SHA-512's initial hash value as the hasher stores it: eight 64-bit words,
each little-endian. -/
def sha512H0Bytes : List Nat :=
  (Sha512.h0.map fun w => (List.range 8).map fun j => w.toNat / 256 ^ j % 256).flatten

/-- `witnessMemS5` with SHA-512's `update` and its 32-byte caller and, at `0x3FCC5800`, the hasher of
the empty message: an empty buffer, the initial hash value, and a zero block
count. -/
def witnessMemS5U : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(0x3FCC5800, List.replicate 128 0 ++ sha512H0Bytes ++ List.replicate 16 0),
    (Image.sha512UpdateAddress, Image.sha512UpdateCode),
    (Image.sha512UpdateArr32Address, Image.sha512UpdateArr32Code),
    (Image.sha512CompressAddress, Image.sha512CompressCode),
    (Image.rangeFromIndexAddress, Image.rangeFromIndexCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.sha512KAddress, Image.sha512KData),
    (Image.sha384UpdateBlocksAddress, Image.sha384UpdateBlocksCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls SHA-512's `update` with 200 bytes at `0x3FCC6000`,
the empty hasher at `0x3FCC5800`, and the stack at `0x3FCC8000` meets
`sha512Update_correct`'s hypotheses. -/
theorem exists_sha512Update_machine :
    ∃ (m : RV32.Machine) (S D sp0 retAddr : RV32.Word) (n : Nat) (msg : List Nat),
      RV32.S5U.UpdEnv m.mem S D sp0 n ∧ m.pc = BitVec.ofNat 32 Image.sha512UpdateAddress ∧
      RV32.reg m RV32.a0 = S ∧ RV32.reg m RV32.a1 = D ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.S5U.Hasher5At m.mem S msg ∧ n < 2 ^ 31 ∧ msg.length + n < 2 ^ 32 := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC5800 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 200
      else if r = RV32.sp then 0x3FCC8000 else 0), BitVec.ofNat 32 Image.sha512UpdateAddress,
      witnessMemS5U⟩,
    0x3FCC5800, 0x3FCC6000, 0x3FCC8000, 0, 200, [], ?_, rfl, rfl, rfl, rfl, rfl, by decide, rfl,
    ⟨by decide, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩, by decide, by decide⟩
  case refine_1 =>
    constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls SHA-512's `Digest::update` on a 32-byte array at
`0x3FCC6000` with the empty hasher at `0x3FCC5800` and the stack at
`0x3FCC8000` meets `sha512UpdateArr32_correct`'s hypotheses. -/
theorem exists_sha512UpdateArr32_machine :
    ∃ (m : RV32.Machine) (S D sp0 retAddr : RV32.Word) (msg : List Nat),
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.sha512UpdateArr32Address) Image.sha512UpdateArr32Code ∧
      RV32.S5U.UpdEnv m.mem S D sp0 32 ∧ m.pc = BitVec.ofNat 32 Image.sha512UpdateArr32Address ∧
      RV32.reg m RV32.a0 = S ∧ RV32.reg m RV32.a1 = D ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.S5U.Hasher5At m.mem S msg ∧ msg.length + 32 < 2 ^ 32 := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC5800 else if r = RV32.a1 then 0x3FCC6000
      else if r = RV32.sp then 0x3FCC8000 else 0), BitVec.ofNat 32 Image.sha512UpdateArr32Address,
      witnessMemS5U⟩,
    0x3FCC5800, 0x3FCC6000, 0x3FCC8000, 0, [], by code_in, ?_, rfl, rfl, rfl, rfl, by decide, rfl,
    ⟨by decide, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩, by decide⟩
  case refine_1 =>
    constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals decide +kernel

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


/-- Memory with the current image's `shr_in_place_wide::<12, 2>` and the
functions it calls where the image loads them, and zeros elsewhere. -/
def witnessMemShr12 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.shr12Address, Image.shr12Code),
    (Image.leadMut12Address, Image.leadMut12Code),
    (Image.trailing12Address, Image.trailing12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `shr_in_place_wide::<12, 2>` with `lo` at
`0x3FCC5000`, `hi` at `0x3FCC6000`, the shift 5, and the stack at
`0x3FCC8000` meets `shr12_correct`'s hypotheses. -/
theorem exists_shr12_machine :
    ∃ (m : RV32.Machine) (P sp0 lo hi retAddr : RV32.Word) (s : Nat), RV32.SHEnv m.mem P sp0 lo hi ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = lo ∧ RV32.reg m RV32.a1 = hi ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 s ∧ 1 ≤ s ∧ s ≤ 63 ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 5
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.shr12Address, witnessMemShr12⟩, BitVec.ofNat 32 Image.shr12Address,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, 5, ?_, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<12>::lincomb_int::<2>` and the
functions and constants it reaches where the image loads them, and zeros
elsewhere. -/
def witnessMemLc12 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.lincomb12Address, Image.lincomb12Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul12x2Address, Image.wideMul12x2Code),
    (Image.condNeg12Address, Image.condNeg12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- A machine that calls `SignedInt<12>::lincomb_int::<2>` with `out` at
`0x3FCC5000`, `a`, `b`, `c`, and `d` at `0x3FCC5100` through `0x3FCC5400`,
and the stack at `0x3FCC8000` meets `lincomb12_correct`'s hypotheses. -/
theorem exists_lincomb12_machine :
    ∃ (m : RV32.Machine) (P sp0 out ap bp cp dp retAddr : RV32.Word), RV32.LCEnv m.mem P sp0 out ap bp cp dp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = cp ∧ RV32.reg m RV32.a4 = dp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (m.mem (ap + 0x30)).toNat ≤ 1 ∧ (m.mem (bp + 0x30)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a4 then 0x3FCC5400
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.lincomb12Address, witnessMemLc12⟩, BitVec.ofNat 32 Image.lincomb12Address,
    0x3FCC8000, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300, 0x3FCC5400, 0, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, by decide, by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's small leaf functions where the image
loads them, and zeros elsewhere. -/
def witnessMemLeaves : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.ctEqU8Address, Image.ctEqU8Code),
    (Image.ctEqSliceAddress, Image.ctEqSliceCode),
    (Image.memcmpAddress, Image.memcmpCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.lshrdi3Address, Image.lshrdi3Code)]

/-- The registers of the leaf witnesses: `a0` through `a2` and the stack. -/
def leafRegs (x y z : RV32.Word) : Fin 32 → RV32.Word := fun r =>
  if r = RV32.a0 then x else if r = RV32.a1 then y else if r = RV32.a2 then z
  else if r = RV32.sp then 0x3FCC8000 else 0

/-- Memory with P-256's field `retrieve`, `memset`, `memcpy`, and the field
modulus where the image loads them, and zeros elsewhere. -/
def witnessMemP256Retrieve : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p256FieldRetrieveAddress, Image.p256FieldRetrieveCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p256ModulusAddress, Image.p256ModulusData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that retrieves the 8 limbs at `0x3FCC5000` from Montgomery
form to `0x3FCC6000`, with the stack at `0x3FCC8000`, meets
`p256FieldRetrieve_correct`'s hypotheses, and the modulus it reads is
P-256's field prime. -/
theorem exists_p256FieldRetrieve_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word), RV32.PREnv m.mem P sp0 out xp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.accV m.mem RV32.p256Np 8 = p256.p := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 0, BitVec.ofNat 32 Image.p256FieldRetrieveAddress, witnessMemP256Retrieve⟩,
    BitVec.ofNat 32 Image.p256FieldRetrieveAddress, 0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0, ?_, rfl, rfl, rfl, rfl,
    by decide, rfl, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with P-384's field `from_repr`, its callees, P-384's modulus, and
`R² mod p` where the image loads them, and zeros elsewhere. -/
def witnessMemP384FromRepr : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p384FromReprAddress, Image.p384FromReprCode),
    (Image.zeroArray48Address, Image.zeroArray48Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.mulMont12Address, Image.mulMont12Code),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.condSelect384Address, Image.condSelect384Code),
    (Image.uint12CtAssignAddress, Image.uint12CtAssignCode),
    (Image.sliceCtAssignAddress, Image.sliceCtAssignCode),
    (Image.p384ModulusAddress, Image.p384ModulusData),
    (Image.p384R2Address, Image.p384R2Data)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that reads the 48 bytes at `0x3FCC5000` into a field element at
`0x3FCC6000`, with the stack at `0x3FCC8000`, meets `p384FromRepr_correct`'s
hypotheses; the modulus it reads is P-384's field prime and the constant
0x60 bytes past it is `2^768 mod p`, so the result is `x · 2^384 mod p`. -/
theorem exists_p384FromRepr_machine :
    ∃ (m : RV32.Machine) (sp0 out inp retAddr : RV32.Word), RV32.FRPEnv m.mem ∧ m.pc = RV32.FRP ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = inp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 16 = 0 ∧ 0x1A0 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat + 49 ≤ 0x40000000 ∧ RV32.Sep out 49 (sp0 + 0xFFFFFE60) 0x1A0 ∧
      RV32.Sep inp 48 (sp0 + 0xFFFFFE60) 0x1A0 ∧ RV32.Sep (sp0 + 0xFFFFFE60) 0x1A0 RV32.p384Np 0x90 ∧
      RV32.accV m.mem RV32.p384Np 12 = p384.p ∧ RV32.accV m.mem (RV32.p384Np + 0x60) 12 = 2 ^ 768 % p384.p := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 0, BitVec.ofNat 32 Image.p384FromReprAddress, witnessMemP384FromRepr⟩,
    0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0, ?_, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide,
    by decide, RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm, by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide +kernel

/-- Memory with P-256's field `from_repr`, its callees, P-256's modulus, and
`R² mod p` where the image loads them, and zeros elsewhere. -/
def witnessMemP256FromRepr : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p256FromReprAddress, Image.p256FromReprCode),
    (Image.shaZero32Address, Image.shaZero32Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.mulMont8Address, Image.mulMont8Code),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.condSelect256Address, Image.condSelect256Code),
    (Image.sliceCtAssignAddress, Image.sliceCtAssignCode),
    (Image.p256ModulusAddress, Image.p256ModulusData),
    (Image.p256R2Address, Image.p256R2Data)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that reads the 32 bytes at `0x3FCC5000` into a field element at
`0x3FCC6000`, with the stack at `0x3FCC8000`, meets `p256FromRepr_correct`'s
hypotheses; the modulus it reads is P-256's field prime and the constant
0x40 bytes past it is `2^512 mod p`, so the result is `x · 2^256 mod p`. -/
theorem exists_p256FromRepr_machine :
    ∃ (m : RV32.Machine) (sp0 out inp retAddr : RV32.Word), RV32.FRQEnv m.mem ∧ m.pc = RV32.FRQ ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = inp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 16 = 0 ∧ 0x140 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat + 33 ≤ 0x40000000 ∧ RV32.Sep out 33 (sp0 + 0xFFFFFEC0) 0x140 ∧
      RV32.Sep inp 32 (sp0 + 0xFFFFFEC0) 0x140 ∧ RV32.Sep (sp0 + 0xFFFFFEC0) 0x140 RV32.p256Np 0x60 ∧
      RV32.accV m.mem RV32.p256Np 8 = p256.p ∧ RV32.accV m.mem (RV32.p256Np + 0x40) 8 = 2 ^ 512 % p256.p := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 0, BitVec.ofNat 32 Image.p256FromReprAddress, witnessMemP256FromRepr⟩,
    0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0, ?_, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide,
    by decide, RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm, by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide +kernel

/-- Memory with `fill_limbs_from_be_slice_truncated` where the image loads
it, and zeros elsewhere. -/
def witnessMemFillLimbs : RV32.Word → BitVec 8 :=
  RV32.regionMem [(Image.fillLimbsBeTruncAddress, Image.fillLimbsBeTruncCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that fills 12 limbs at `0x3FCC6000` from the 48 bytes at
`0x3FCC5000` at a 384-bit precision, with the stack at `0x3FCC8000`, meets
`fillLimbs_correct`'s hypotheses. -/
theorem exists_fillLimbs_machine :
    ∃ (m : RV32.Machine) (sp0 b Lp retAddr : RV32.Word) (n L bits mm : Nat),
      RV32.CodeIn m.mem RV32.FL Image.fillLimbsBeTruncCode ∧ m.pc = RV32.FL ∧ RV32.reg m RV32.a0 = b ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.a2 = Lp ∧ RV32.reg m RV32.a3 = BitVec.ofNat 32 L ∧
      RV32.reg m RV32.a4 = BitVec.ofNat 32 bits ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 ∧ bits % 32 = 0 ∧ bits ≤ 32 * L ∧ L < 2 ^ 25 ∧ mm = min n (bits / 8) ∧
      b.toNat + n < 2 ^ 32 ∧ sp0.toNat % 4 = 0 ∧ 0x20 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧
      Lp.toNat + 4 * L ≤ 0x40000000 ∧ Lp.toNat % 4 = 0 ∧ RV32.Sep b n (sp0 + 0xFFFFFFE0) 0x20 ∧
      RV32.Sep b n Lp (4 * L) ∧ RV32.Sep (sp0 + 0xFFFFFFE0) 0x20 Lp (4 * L) := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 48 else if r = RV32.a2 then 0x3FCC6000
    else if r = RV32.a3 then 12 else if r = RV32.a4 then 384 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, RV32.FL, witnessMemFillLimbs⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, 48, 12, 384, 48, ?_, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm⟩
  code_in

/-- Memory with both `from_be_slice_truncated` instances and their callees
where the image loads them, and zeros elsewhere. -/
def witnessMemFromBeSlice : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.fromBeSliceTrunc12Address, Image.fromBeSliceTrunc12Code),
    (Image.fromBeSliceTrunc8Address, Image.fromBeSliceTrunc8Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.fillLimbsBeTruncAddress, Image.fillLimbsBeTruncCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that reads a `Uint<12>` at `0x3FCC6000` from the 48 bytes at
`0x3FCC5000` at a 384-bit precision, with the stack at `0x3FCC8000`, meets
`fromBeSliceTrunc12_correct`'s hypotheses. -/
theorem exists_fromBeSliceTrunc12_machine :
    ∃ (m : RV32.Machine) (sp0 out b retAddr : RV32.Word) (n bits : Nat), RV32.FBEnv m.mem ∧ m.pc = RV32.FB ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.a3 = BitVec.ofNat 32 bits ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 ∧ bits % 32 = 0 ∧ bits ≤ 384 ∧ b.toNat + n < 2 ^ 32 ∧ sp0.toNat % 4 = 0 ∧
      0x70 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧ out.toNat + 48 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧
      RV32.Sep b n (sp0 + 0xFFFFFF90) 0x70 ∧ RV32.Sep out 48 (sp0 + 0xFFFFFF90) 0x70 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 48 |> fun f r => if r = RV32.a3 then 384 else f r, RV32.FB,
    witnessMemFromBeSlice⟩, 0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0, 48, 384, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩
  constructor
  all_goals code_in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that reads a `Uint<8>` at `0x3FCC6000` from the 32 bytes at
`0x3FCC5000` at a 256-bit precision, with the stack at `0x3FCC8000`, meets
`fromBeSliceTrunc8_correct`'s hypotheses. -/
theorem exists_fromBeSliceTrunc8_machine :
    ∃ (m : RV32.Machine) (sp0 out b retAddr : RV32.Word) (n bits : Nat), RV32.FCEnv m.mem ∧ m.pc = RV32.FC ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.a3 = BitVec.ofNat 32 bits ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 ∧ bits % 32 = 0 ∧ bits ≤ 256 ∧ b.toNat + n < 2 ^ 32 ∧ sp0.toNat % 4 = 0 ∧
      0x60 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧ out.toNat + 32 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧
      RV32.Sep b n (sp0 + 0xFFFFFFA0) 0x60 ∧ RV32.Sep out 32 (sp0 + 0xFFFFFFA0) 0x60 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 32 |> fun f r => if r = RV32.a3 then 256 else f r, RV32.FC,
    witnessMemFromBeSlice⟩, 0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0, 32, 256, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩
  constructor
  all_goals code_in

/-- Both `bytes2scalar` instances, their callees, the panic code, and the
constants they read, where the image loads them. -/
def witnessRegionsB2S : List (Nat × List Nat) :=
  RV32.panicFns ++ [(Image.bytes2scalar384Address, Image.bytes2scalar384Code),
    (Image.bytes2scalar256Address, Image.bytes2scalar256Code),
    (Image.leadingZerosAddress, Image.leadingZerosCode), (Image.expectUsizeAddress, Image.expectUsizeCode),
    (Image.fromBeSliceTrunc12Address, Image.fromBeSliceTrunc12Code),
    (Image.fromBeSliceTrunc8Address, Image.fromBeSliceTrunc8Code), (Image.memsetAddress, Image.memsetCode),
    (Image.fillLimbsBeTruncAddress, Image.fillLimbsBeTruncCode), (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode), (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.blackBoxU8Address, Image.blackBoxU8Code), (Image.choiceNotAddress, Image.choiceNotCode),
    (Image.sliceCtAssignAddress, Image.sliceCtAssignCode), (Image.p384ScalarNewAddress, Image.p384ScalarNewCode),
    (Image.mulMont12Address, Image.mulMont12Code), (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.p384OrderAddress, Image.p384OrderData), (Image.p384ScalarR2Address, Image.p384ScalarR2Data),
    (Image.b2sOrder384Address, Image.b2sOrder384Data), (Image.b2sOrder256Address, Image.b2sOrder256Data),
    (Image.scalarFromSlice384Address, Image.scalarFromSlice384Code),
    (Image.scalarFromSlice256Address, Image.scalarFromSlice256Code),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode)]

def witnessMemB2S : RV32.Word → BitVec 8 := RV32.regionMem witnessRegionsB2S

set_option maxRecDepth 200000 in
theorem witnessRegionsB2S_apart : RV32.regionsApart witnessRegionsB2S = true := by decide +kernel

theorem witnessMemB2S_panic : RV32.PanicCode witnessMemB2S :=
  fun _ hp => RV32.regionMem_codeIn witnessRegionsB2S_apart (List.mem_append_left _ hp)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that turns the 48 bytes at `0x3FCC5000` into a P-384 scalar at
`0x3FCC6000`, with the stack at `0x3FCC8000`, meets
`bytes2scalar384_correct`'s hypotheses; the order it compares against is
P-384's. -/
theorem exists_bytes2scalar384_machine :
    ∃ (m : RV32.Machine) (sp0 out b retAddr : RV32.Word) (n : Nat), RV32.BZEnv m.mem ∧ m.pc = RV32.BS ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      sp0.toNat % 16 = 0 ∧ 0x3FC80000 + 0x200 ≤ sp0.toNat ∧ sp0.toNat ≤ RV32.dramEnd ∧
      out.toNat + 48 ≤ RV32.dramEnd ∧ out.toNat % 4 = 0 ∧ b.toNat + n < 2 ^ 32 ∧
      RV32.Sep b n (sp0 + 0xFFFFFE50) 0x1B0 ∧ RV32.Sep out 48 (sp0 + 0xFFFFFE50) 0x1B0 ∧
      RV32.Sep (sp0 + 0xFFFFFE50) 0x1B0 RV32.BZO 48 ∧ RV32.Sep (sp0 + 0xFFFFFE50) 0x1B0 RV32.n3M 48 ∧
      RV32.Sep (sp0 + 0xFFFFFE50) 0x1B0 RV32.n3R2A 48 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 48, RV32.BS, witnessMemB2S⟩, 0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0, 48,
    ?_, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm, (RV32.sep_of_le (by decide) (by decide)).symm,
    (RV32.sep_of_le (by decide) (by decide)).symm⟩
  refine ⟨by code_in, by code_in, witnessMemB2S_panic, by code_in, ⟨by code_in, by code_in, by code_in, by code_in,
    by code_in⟩, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    by code_in, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that turns the 32 bytes at `0x3FCC5000` into a P-256 scalar at
`0x3FCC6000`, with the stack at `0x3FCC8000`, meets
`bytes2scalar256_correct`'s hypotheses; the order it compares against is
P-256's. -/
theorem exists_bytes2scalar256_machine :
    ∃ (m : RV32.Machine) (sp0 out b retAddr : RV32.Word), RV32.BYEnv m.mem ∧ m.pc = RV32.BY ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = b ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      sp0.toNat % 16 = 0 ∧ 0x3FC80000 + 0x200 ≤ sp0.toNat ∧ sp0.toNat ≤ RV32.dramEnd ∧
      out.toNat + 32 ≤ RV32.dramEnd ∧ out.toNat % 4 = 0 ∧ b.toNat + 32 < 2 ^ 32 ∧
      RV32.Sep b 32 (sp0 + 0xFFFFFF20) 0xE0 ∧ RV32.Sep out 32 (sp0 + 0xFFFFFF20) 0xE0 ∧
      RV32.Sep (sp0 + 0xFFFFFF20) 0xE0 RV32.BYO 32 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 0, RV32.BY, witnessMemB2S⟩, 0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0,
    ?_, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm⟩
  refine ⟨by code_in, by code_in, witnessMemB2S_panic, by code_in, ⟨by code_in, by code_in, by code_in, by code_in,
    by code_in⟩, by code_in, by code_in, by code_in, by code_in, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that reads a P-384 scalar at `0x3FCC6000` from the 48 bytes at
`0x3FCC5000`, with the stack at `0x3FCC8000`, meets
`scalarFromSlice384_correct`'s hypotheses. -/
theorem exists_scalarFromSlice384_machine :
    ∃ (m : RV32.Machine) (sp0 out b retAddr : RV32.Word), RV32.BFEnv m.mem ∧ m.pc = RV32.BF ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0xF0 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat + 52 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧
      RV32.Sep b 48 (sp0 + 0xFFFFFF10) 0xF0 ∧ RV32.Sep out 52 (sp0 + 0xFFFFFF10) 0xF0 ∧
      RV32.Sep (sp0 + 0xFFFFFF10) 0xF0 RV32.BZO 48 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 0, RV32.BF, witnessMemB2S⟩, 0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0,
    ?_, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm⟩
  exact ⟨by code_in, ⟨by code_in, by code_in, by code_in, by code_in, by code_in⟩, by code_in, by code_in, by code_in,
    by decide +kernel⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that reads a P-256 scalar at `0x3FCC6000` from the 32 bytes at
`0x3FCC5000`, with the stack at `0x3FCC8000`, meets
`scalarFromSlice256_correct`'s hypotheses. -/
theorem exists_scalarFromSlice256_machine :
    ∃ (m : RV32.Machine) (sp0 out b retAddr : RV32.Word), RV32.BGEnv m.mem ∧ m.pc = RV32.BV ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0xC0 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat + 36 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧
      RV32.Sep b 32 (sp0 + 0xFFFFFF40) 0xC0 ∧ RV32.Sep out 36 (sp0 + 0xFFFFFF40) 0xC0 ∧
      RV32.Sep (sp0 + 0xFFFFFF40) 0xC0 RV32.BYO 32 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 0, RV32.BV, witnessMemB2S⟩, 0x3FCC8000, 0x3FCC6000, 0x3FCC5000, 0,
    ?_, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm⟩
  exact ⟨by code_in, ⟨by code_in, by code_in, by code_in, by code_in, by code_in⟩, by code_in, by code_in, by code_in,
    by decide +kernel⟩

/-- `is_small_order`, its callees, and the field element `ONE`, where the
image loads them. -/
def witnessRegionsISO : List (Nat × List Nat) :=
  [(Image.isSmallOrderAddress, Image.isSmallOrderCode), (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode), (Image.memsetAddress, Image.memsetCode),
    (Image.edDoubleAddress, Image.edDoubleCode), (Image.feSquareAddress, Image.feSquareCode),
    (Image.feSquareInnerAddress, Image.feSquareInnerCode), (Image.feReduceAddress, Image.feReduceCode),
    (Image.feAddAddress, Image.feAddCode), (Image.feSubAddress, Image.feSubCode),
    (Image.asProjectiveAddress, Image.asProjectiveCode), (Image.asExtendedAddress, Image.asExtendedCode),
    (Image.feMulAddress, Image.feMulCode), (Image.feCtEqAddress, Image.feCtEqCode),
    (Image.feToBytesAddress, Image.feToBytesCode), (Image.ctEqSliceAddress, Image.ctEqSliceCode),
    (Image.ctEqU8Address, Image.ctEqU8Code), (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.edOneAddress, Image.edOneData)]

def witnessMemISO : RV32.Word → BitVec 8 := RV32.regionMem witnessRegionsISO

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that asks whether the point at `0x3FCC5000` has small order,
with the stack at `0x3FCC8000`, meets `isSmallOrder_correct`'s hypotheses. -/
theorem exists_isSmallOrder_machine :
    ∃ (m : RV32.Machine) (sp0 p retAddr : RV32.Word), RV32.ISOEnv m.mem ∧ m.pc = RV32.ISO ∧
      RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x4D0 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧
      p.toNat % 4 = 0 ∧ RV32.Sep p 120 (sp0 + 0xFFFFFB30) 0x4D0 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edOneAddress) 40 (sp0 + 0xFFFFFB30) 0x4D0 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0 0, RV32.ISO, witnessMemISO⟩, 0x3FCC8000, 0x3FCC5000, 0,
    ?_, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩
  exact ⟨by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    by decide +kernel⟩

/-- `decompress`, its callees, and the field elements `ONE`, `EDWARDS_D`,
and `SQRT_M1`, where the image loads them. -/
def witnessRegionsDec : List (Nat × List Nat) :=
  [(Image.edDecompressAddress, Image.edDecompressCode), (Image.feLoad3Address, Image.feLoad3Code),
    (Image.feLoad4Address, Image.feLoad4Code), (Image.feReduceAddress, Image.feReduceCode),
    (Image.feSquareAddress, Image.feSquareCode), (Image.feSquareInnerAddress, Image.feSquareInnerCode),
    (Image.feSubAddress, Image.feSubCode), (Image.feAddAddress, Image.feAddCode),
    (Image.feMulAddress, Image.feMulCode), (Image.pow22501Address, Image.pow22501Code),
    (Image.fePow2kAddress, Image.fePow2kCode), (Image.feCtEqAddress, Image.feCtEqCode),
    (Image.feToBytesAddress, Image.feToBytesCode), (Image.ctEqSliceAddress, Image.ctEqSliceCode),
    (Image.ctEqU8Address, Image.ctEqU8Code), (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.feNegAddress, Image.feNegCode), (Image.feCondAssignAddress, Image.feCondAssignCode),
    (Image.feIsNegativeAddress, Image.feIsNegativeCode), (Image.feCondNegAddress, Image.feCondNegCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode), (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.edOneAddress, Image.edOneData), (Image.edDAddress, Image.edDData),
    (Image.edSqrtM1Address, Image.edSqrtM1Data)]

def witnessMemDec : RV32.Word → BitVec 8 := RV32.regionMem witnessRegionsDec

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that decompresses the 32 bytes at `0x3FCC6100` into the slot
at `0x3FCC6000`, with the stack at `0x3FCC8000`, meets
`edDecompress_correct`'s hypotheses. -/
theorem exists_edDecompress_machine :
    ∃ (m : RV32.Machine) (sp0 out bp retAddr : RV32.Word), RV32.DecEnv m.mem ∧ m.pc = RV32.DEC ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = bp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x6F0 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧ out.toNat + 0xA4 ≤ 0x40000000 ∧
      RV32.Sep out 0xA4 (sp0 + 0xFFFFF910) 0x6F0 ∧ RV32.Sep bp 32 (sp0 + 0xFFFFF910) 0x6F0 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edOneAddress) 40 (sp0 + 0xFFFFF910) 0x6F0 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edDAddress) 40 (sp0 + 0xFFFFF910) 0x6F0 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edSqrtM1Address) 40 (sp0 + 0xFFFFF910) 0x6F0 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC6100 0, RV32.DEC, witnessMemDec⟩, 0x3FCC8000, 0x3FCC6000, 0x3FCC6100, 0,
    ?_, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩
  exact ⟨by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    by code_in, by code_in, by code_in, by code_in⟩

def witnessMemVkb : RV32.Word → BitVec 8 :=
  RV32.regionMem ((Image.edVerifyingKeyFromBytesAddress, Image.edVerifyingKeyFromBytesCode) :: witnessRegionsDec)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `VerifyingKey::from_bytes` on the 32 bytes at
`0x3FCC6100` with the result at `0x3FCC6000` and the stack at `0x3FCC8000`
meets `edVkFromBytes_correct`'s hypotheses. -/
theorem exists_edVkFromBytes_machine :
    ∃ (m : RV32.Machine) (sp0 out bp retAddr : RV32.Word), RV32.DecEnv m.mem ∧
      RV32.CodeIn m.mem RV32.VKB Image.edVerifyingKeyFromBytesCode ∧ m.pc = RV32.VKB ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = bp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x7B0 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧ out.toNat + 0xC4 ≤ 0x40000000 ∧ bp.toNat + 32 < 2 ^ 32 ∧
      RV32.Sep out 0xC4 (sp0 + 0xFFFFF850) 0x7B0 ∧ RV32.Sep bp 32 (sp0 + 0xFFFFF850) 0x7B0 ∧ RV32.Sep bp 32 out 0xC4 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edOneAddress) 40 (sp0 + 0xFFFFF850) 0x7B0 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edDAddress) 40 (sp0 + 0xFFFFF850) 0x7B0 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edSqrtM1Address) 40 (sp0 + 0xFFFFF850) 0x7B0 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC6100 0, RV32.VKB, witnessMemVkb⟩, 0x3FCC8000, 0x3FCC6000, 0x3FCC6100, 0,
    ?_, by code_in, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide,
    by decide, RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩
  exact ⟨by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    by code_in, by code_in, by code_in, by code_in⟩

def witnessMemPkOk : RV32.Word → BitVec 8 :=
  RV32.regionMem ((Image.ed25519PublicKeyOkAddress, Image.ed25519PublicKeyOkCode) ::
    (Image.edVerifyingKeyFromBytesAddress, Image.edVerifyingKeyFromBytesCode) ::
    (Image.lessThanLeAddress, Image.lessThanLeCode) :: (Image.arr32EqCryptoAddress, Image.arr32EqCryptoCode) ::
    (Image.memcmpAddress, Image.memcmpCode) :: (Image.memsetAddress, Image.memsetCode) ::
    (Image.edDoubleAddress, Image.edDoubleCode) :: (Image.asProjectiveAddress, Image.asProjectiveCode) ::
    (Image.asExtendedAddress, Image.asExtendedCode) :: (Image.isSmallOrderAddress, Image.isSmallOrderCode) ::
    witnessRegionsDec)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that asks whether the 32 key bytes at `0x3FCC6100` are an
acceptable Ed25519 public key, with the stack at `0x3FCC8000`, meets
`pkOk_correct`'s hypotheses. -/
theorem exists_pkOk_machine :
    ∃ (m : RV32.Machine) (sp0 pk retAddr : RV32.Word), RV32.PkEnv m.mem ∧ m.pc = RV32.PKO ∧
      RV32.reg m RV32.a0 = pk ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x940 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧
      pk.toNat + 32 < 2 ^ 32 ∧ RV32.Sep pk 32 (sp0 + 0xFFFFF6C0) 0x940 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edOneAddress) 40 (sp0 + 0xFFFFF6C0) 0x940 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edDAddress) 40 (sp0 + 0xFFFFF6C0) 0x940 ∧
      RV32.Sep (BitVec.ofNat 32 Image.edSqrtM1Address) 40 (sp0 + 0xFFFFF6C0) 0x940 ∧
      RV32.Sep (BitVec.ofNat 32 (img% edPrimeAddress)) 32 (sp0 + 0xFFFFF6C0) 0x940 ∧
      RV32.Sep (BitVec.ofNat 32 (img% p256OneAddress)) 32 (sp0 + 0xFFFFF6C0) 0x940 ∧
      RV32.Sep (BitVec.ofNat 32 (img% edPm1Address)) 32 (sp0 + 0xFFFFF6C0) 0x940 := by
  refine ⟨⟨leafRegs 0x3FCC6100 0 0, RV32.PKO, witnessMemPkOk⟩, 0x3FCC8000, 0x3FCC6100, 0,
    ?_, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩
  exact ⟨⟨by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
      by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
      by code_in, by code_in, by code_in, by code_in⟩,
    ⟨by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
      by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
      by decide +kernel⟩,
    by code_in, by code_in, by code_in, by code_in, by code_in⟩

def witnessMemNt : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.nafTableFromAddress, Image.nafTableFromCode), (Image.asProjNielsAddress, Image.asProjNielsCode),
    (Image.edAddNielsAddress, Image.edAddNielsCode), (Image.asExtendedAddress, Image.asExtendedCode),
    (Image.edDoubleAddress, Image.edDoubleCode), (Image.feAddAddress, Image.feAddCode),
    (Image.feSubAddress, Image.feSubCode), (Image.feMulAddress, Image.feMulCode),
    (Image.feReduceAddress, Image.feReduceCode), (Image.feSquareAddress, Image.feSquareCode),
    (Image.feSquareInnerAddress, Image.feSquareInnerCode), (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that builds the table for the point at `0x3FCC6000` into
`0x3FCC6100`, with the stack at `0x3FCC8000`, meets `nafTable_correct`'s
hypotheses. -/
theorem exists_nafTable_machine :
    ∃ (m : RV32.Machine) (sp0 out A retAddr : RV32.Word), RV32.NtEnv m.mem ∧ m.pc = RV32.NTF ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = A ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0xA10 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ A.toNat % 4 = 0 ∧ A.toNat + 0xA0 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧
      out.toNat + 0x500 ≤ 0x40000000 ∧ RV32.Sep A 0xA0 (sp0 + 0xFFFFF5F0) 0xA10 ∧
      RV32.Sep out 0x500 (sp0 + 0xFFFFF5F0) 0xA10 ∧ RV32.Sep RV32.apnD 40 (sp0 + 0xFFFFF5F0) 0xA10 := by
  refine ⟨⟨leafRegs 0x3FCC6100 0x3FCC6000 0, RV32.NTF, witnessMemNt⟩, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0,
    ?_, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩
  exact ⟨by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    by code_in, by code_in, by code_in, by code_in⟩

/-- `wnaf_form`, its callees, and the panic code where the image loads them,
the four scalar bytes `0x13 0 0 0` at `0x3FCC6000`, and zeros elsewhere. -/
def witnessRegionsWf : List (Nat × List Nat) :=
  RV32.panicFns ++ [(Image.wnafFormAddress, Image.wnafFormCode), (Image.memsetAddress, Image.memsetCode),
    (Image.incrementLimbAddress, Image.incrementLimbCode), (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode), (Image.lshrdi3Address, Image.lshrdi3Code),
    (Image.ashldi3Address, Image.ashldi3Code), (Image.expectUsizeAddress, Image.expectUsizeCode),
    (0x3FCC6000, [0x13, 0x00, 0x00, 0x00])]

def witnessMemWf : RV32.Word → BitVec 8 := RV32.regionMem witnessRegionsWf

set_option maxRecDepth 200000 in
theorem witnessRegionsWf_apart : RV32.regionsApart witnessRegionsWf = true := by decide +kernel

theorem witnessMemWf_panic : RV32.PanicCode witnessMemWf :=
  fun _ hp => RV32.regionMem_codeIn witnessRegionsWf_apart (List.mem_append_left _ hp)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `wnaf_form` on the 4 bytes at `0x3FCC6000` with
`L = 32`, a 40-byte digit buffer at `0x3FCC6100`, and the stack at
`0x3FCC8000` meets `wnafForm_correct`'s hypotheses. -/
theorem exists_wnafForm_machine :
    ∃ (m : RV32.Machine) (sp0 wp cp retAddr : RV32.Word) (wl cn L : Nat),
      RV32.WfCtx m.mem (sp0 + 0xFFFFFF90) wp cp wl cn L ∧ m.pc = RV32.WF ∧ RV32.reg m RV32.a0 = wp ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 wl ∧ RV32.reg m RV32.a2 = cp ∧ RV32.reg m RV32.a3 = BitVec.ofNat 32 cn ∧
      RV32.reg m RV32.a4 = BitVec.ofNat 32 L ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 := by
  refine ⟨⟨leafRegs 0x3FCC6100 40 0x3FCC6000 |> fun f r => if r = RV32.a3 then 4 else if r = RV32.a4 then 32 else f r,
    RV32.WF, witnessMemWf⟩, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0, 40, 4, 32, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, rfl⟩
  refine ⟨by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in,
    witnessMemWf_panic, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    RV32.sep_of_le (by decide) (by decide), by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), by decide +kernel⟩

/-- Memory with `time::date_time` and `time::digits::<2>` where the image
loads them, a slice reader at `0x3FCC6000` over 10 bytes at `0x3FCC7000`,
and zeros elsewhere. -/
def witnessMemDT : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.dateTimeAddress, Image.dateTimeCode), (Image.timeDigits2Address, Image.timeDigits2Code),
    (0x3FCC6000, [0x00, 0x70, 0xCC, 0x3F, 0x0A, 0x00, 0x00, 0x00])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `time::date_time` for the year 2000 on a reader
at `0x3FCC6000` over 10 bytes, with the result at `0x3FCC5000` and the stack
at `0x3FCC8000`, meets `dateTime_correct`'s hypotheses. -/
theorem exists_dateTime_machine :
    ∃ (m : RV32.Machine) (sp0 out d p Y retAddr : RV32.Word) (n : Nat),
      RV32.CodeIn m.mem RV32.DT Image.dateTimeCode ∧ RV32.CodeIn m.mem RV32.TD Image.timeDigits2Code ∧
      m.pc = RV32.DT ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = Y ∧ RV32.reg m RV32.a2 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      sp0.toNat % 4 = 0 ∧ 0x30 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧ out.toNat + 16 ≤ 0x40000000 ∧
      out.toNat % 4 = 0 ∧ d.toNat + 8 ≤ 0x40000000 ∧ d.toNat % 4 = 0 ∧ n < 2 ^ 32 ∧
      RV32.memLoad32 m.mem d = p ∧ RV32.memLoad32 m.mem (d + 4) = BitVec.ofNat 32 n ∧
      RV32.Sep out 16 (sp0 + 0xFFFFFFD0) 0x30 ∧ RV32.Sep d 8 (sp0 + 0xFFFFFFD0) 0x30 ∧ RV32.Sep out 16 d 8 ∧
      RV32.Sep p n (sp0 + 0xFFFFFFD0) 0x30 ∧ RV32.Sep p n d 8 ∧ RV32.Sep d 8 p 10 := by
  refine ⟨⟨leafRegs 0x3FCC5000 2000 0x3FCC6000, RV32.DT, witnessMemDT⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000,
    0x3FCC7000, 2000, 0, 10, by code_in, by code_in, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm, RV32.sep_of_le (by decide) (by decide)⟩

/-- Memory with `time::generalized_time` and its callees where the image
loads them, and zeros elsewhere. -/
def witnessMemGT : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.generalizedTimeAddress, Image.generalizedTimeCode), (Image.dateTimeAddress, Image.dateTimeCode),
    (Image.timeDigits2Address, Image.timeDigits2Code), (Image.timeDigits4Address, Image.timeDigits4Code),
    (Image.allAsciiDigitAddress, Image.allAsciiDigitCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Memory with `x509::read_time` and its callees where the image loads
them, a DER reader at `0x3FCC6000` over 17 bytes at `0x3FCC7000`, and zeros
elsewhere. -/
def witnessMemXRT : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.x509ReadTimeAddress, Image.x509ReadTimeCode), (Image.derTlvAddress, Image.derTlvCode),
    (Image.generalizedTimeAddress, Image.generalizedTimeCode), (Image.dateTimeAddress, Image.dateTimeCode),
    (Image.timeDigits2Address, Image.timeDigits2Code), (Image.timeDigits4Address, Image.timeDigits4Code),
    (Image.allAsciiDigitAddress, Image.allAsciiDigitCode),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F, 0x11, 0x00, 0x00, 0x00])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `time::generalized_time` on 15 bytes at
`0x3FCC7000`, with the result at `0x3FCC5000` and the stack at `0x3FCC8000`,
meets `generalizedTime_correct`'s hypotheses. -/
theorem exists_generalizedTime_machine :
    ∃ (m : RV32.Machine) (sp0 out p retAddr : RV32.Word) (n : Nat),
      RV32.CodeIn m.mem RV32.GNT Image.generalizedTimeCode ∧ RV32.CodeIn m.mem RV32.DT Image.dateTimeCode ∧
      RV32.CodeIn m.mem RV32.TD Image.timeDigits2Code ∧ RV32.CodeIn m.mem RV32.TD4 Image.timeDigits4Code ∧
      RV32.CodeIn m.mem RV32.AAD Image.allAsciiDigitCode ∧ m.pc = RV32.GNT ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = p ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x60 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat + 16 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧ n < 2 ^ 32 ∧
      p.toNat + n + 14 ≤ 0x40000000 ∧ 0 < p.toNat ∧ RV32.Sep out 16 (sp0 + 0xFFFFFFA0) 0x60 ∧
      RV32.Sep p (n + 14) (sp0 + 0xFFFFFFA0) 0x60 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC7000 15, RV32.GNT, witnessMemGT⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC7000, 0, 15,
    by code_in, by code_in, by code_in, by code_in, by code_in, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `x509::read_time` on a DER reader at `0x3FCC6000`
over 17 bytes, with the result at `0x3FCC5000` and the stack at
`0x3FCC8000`, meets `x509ReadTime_correct`'s hypotheses. -/
theorem exists_x509ReadTime_machine :
    ∃ (m : RV32.Machine) (sp0 out d rp retAddr : RV32.Word) (rl : Nat),
      RV32.CodeIn m.mem RV32.XRT Image.x509ReadTimeCode ∧ RV32.CodeIn m.mem RV32.TLV Image.derTlvCode ∧
      RV32.CodeIn m.mem RV32.GNT Image.generalizedTimeCode ∧ RV32.CodeIn m.mem RV32.DT Image.dateTimeCode ∧
      RV32.CodeIn m.mem RV32.TD Image.timeDigits2Code ∧ RV32.CodeIn m.mem RV32.TD4 Image.timeDigits4Code ∧
      RV32.CodeIn m.mem RV32.AAD Image.allAsciiDigitCode ∧ m.pc = RV32.XRT ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = d ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x60 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧
      out.toNat + 16 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧ d.toNat + 16 ≤ 0x40000000 ∧ d.toNat % 4 = 0 ∧
      RV32.memLoad32 m.mem (d + 8) = rp ∧ RV32.memLoad32 m.mem (d + 0xC) = BitVec.ofNat 32 rl ∧
      rp.toNat + rl + 14 ≤ 0x40000000 ∧ 0 < rp.toNat ∧ RV32.Sep out 16 (sp0 + 0xFFFFFFA0) 0x60 ∧
      RV32.Sep (d + 8) 8 (sp0 + 0xFFFFFFA0) 0x60 ∧ RV32.Sep out 16 (d + 8) 8 ∧
      RV32.Sep rp (rl + 14) (sp0 + 0xFFFFFFA0) 0x60 ∧ RV32.Sep rp rl (d + 8) 8 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, RV32.XRT, witnessMemXRT⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000,
    0x3FCC7000, 0, 17, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, by code_in, rfl, rfl,
    rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide +kernel, by decide +kernel, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), (RV32.sep_of_le (by decide) (by decide)).symm⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Memory with `time::rfc3339` and its callees where the image loads them,
and zeros elsewhere. -/
def witnessMemRFC : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.timeRfc3339Address, Image.timeRfc3339Code), (Image.dateTimeAddress, Image.dateTimeCode),
    (Image.timeDigits2Address, Image.timeDigits2Code), (Image.timeDigits4Address, Image.timeDigits4Code),
    (Image.allAsciiDigitAddress, Image.allAsciiDigitCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `time::rfc3339` on 20 bytes at `0x3FCC7000`, with
the result at `0x3FCC5000` and the stack at `0x3FCC8000`, meets
`timeRfc3339_correct`'s hypotheses. -/
theorem exists_timeRfc3339_machine :
    ∃ (m : RV32.Machine) (sp0 out p retAddr : RV32.Word) (n : Nat),
      RV32.CodeIn m.mem RV32.RFC Image.timeRfc3339Code ∧ RV32.CodeIn m.mem RV32.DT Image.dateTimeCode ∧
      RV32.CodeIn m.mem RV32.TD Image.timeDigits2Code ∧ RV32.CodeIn m.mem RV32.TD4 Image.timeDigits4Code ∧
      RV32.CodeIn m.mem RV32.AAD Image.allAsciiDigitCode ∧ m.pc = RV32.RFC ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = p ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x90 ≤ sp0.toNat ∧
      sp0.toNat ≤ 0x40000000 ∧ out.toNat + 16 ≤ 0x40000000 ∧ out.toNat % 4 = 0 ∧
      p.toNat + n + 4 ≤ 0x40000000 ∧ RV32.Sep out 16 (sp0 + 0xFFFFFF70) 0x90 ∧
      RV32.Sep p (n + 4) (sp0 + 0xFFFFFF70) 0x90 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC7000 20, RV32.RFC, witnessMemRFC⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC7000, 0, 20,
    by code_in, by code_in, by code_in, by code_in, by code_in, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide,
    by decide, by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩

/-- Memory with `manifest::parse` and its callees where the image loads them,
and zeros elsewhere. -/
def witnessMemParseCur : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.manifestParseAddress, Image.manifestParseCode), (Image.readerMagicAddress, Image.readerMagicCode),
    (Image.readerArray4Address, Image.readerArray4Code), (Image.readerBytesAddress, Image.readerBytesCode),
    (Image.readerU16Address, Image.readerU16Code), (Image.readerReservedAddress, Image.readerReservedCode),
    (Image.manifestPartAddress, Image.manifestPartCode), (Image.readerU32Address, Image.readerU32Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `manifest::parse` on 32 bytes at `0x3FCC6000`, with
the result at `0x3FCC5000` and the stack at `0x3FCC8000`, meets
`Cur.manifestParse_correct`'s hypotheses. -/
theorem exists_manifestParseCur_machine :
    ∃ (m : RV32.Machine) (sp0 out bp retAddr : RV32.Word),
      RV32.Cur.MPCode m.mem ∧ m.pc = RV32.Cur.MP ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = bp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      sp0.toNat % 4 = 0 ∧ 0x80 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧ bp ≠ 0 ∧ bp.toNat + 32 ≤ 2 ^ 32 ∧
      out.toNat % 4 = 0 ∧ out.toNat + 28 ≤ 0x40000000 ∧ RV32.Sep bp 32 (sp0 + 0xFFFFFF80) 0x80 ∧
      RV32.Sep out 28 (sp0 + 0xFFFFFF80) 0x80 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, RV32.Cur.MP, witnessMemParseCur⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000,
    0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide)⟩
  all_goals code_in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Memory with `base64::decode_into`, `copy_from_slice`, and `memcpy` where
the image loads them, the text `QUJDREVG` at `0x3FCC7000`, and zeros
elsewhere. -/
def witnessMemBDI : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.base64DecodeIntoAddress, Image.base64DecodeIntoCode),
    (Image.copyFromSliceU8Address, Image.copyFromSliceU8Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode), (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (0x3FCC7000, [0x51, 0x55, 0x4A, 0x44, 0x52, 0x45, 0x56, 0x47])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `base64::decode_into` on 8 characters at
`0x3FCC7000` into 6 bytes at `0x3FCC6000`, with the result at `0x3FCC5000`
and the stack at `0x3FCC8000`, meets `base64DecodeInto_correct`'s
hypotheses. -/
theorem exists_base64DecodeInto_machine :
    ∃ (m : RV32.Machine) (sp0 res t out retAddr : RV32.Word) (n L : Nat),
      RV32.CodeIn m.mem RV32.BDI Image.base64DecodeIntoCode ∧ RV32.CodeIn m.mem RV32.BCW Image.copyFromSliceU8Code ∧
      RV32.CodeIn m.mem RV32.BMS Image.memcpyStubCode ∧ RV32.CodeIn m.mem RV32.BMB Image.memcpyBodyCode ∧
      m.pc = RV32.BDI ∧ RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = t ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.a3 = out ∧ RV32.reg m RV32.a4 = BitVec.ofNat 32 L ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧
      0x50 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧ res.toNat + 8 ≤ 0x40000000 ∧ res.toNat % 4 = 0 ∧
      out.toNat + L ≤ 0x40000000 ∧ t.toNat + n ≤ 0x40000000 ∧ RV32.Sep out L (sp0 + 0xFFFFFFB0) 0x50 ∧
      RV32.Sep t n (sp0 + 0xFFFFFFB0) 0x50 ∧ RV32.Sep res 8 (sp0 + 0xFFFFFFB0) 0x50 ∧ RV32.Sep t n out L ∧
      RV32.Sep res 8 out L := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC7000 else if r = RV32.a2 then 8
    else if r = RV32.a3 then 0x3FCC6000 else if r = RV32.a4 then 6 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, RV32.BDI, witnessMemBDI⟩, 0x3FCC8000, 0x3FCC5000, 0x3FCC7000, 0x3FCC6000, 0, 8, 6,
    by code_in, by code_in, by code_in, by code_in, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide),
    (RV32.sep_of_le (by decide) (by decide)).symm, RV32.sep_of_le (by decide) (by decide)⟩

/-- Memory with `base64::encode_to::<Sha256>`, the alphabet, `update` and the
code it runs, and the round constants where the image loads them, the empty
hasher at `0x3FCC5100`, the bytes `hello` at `0x3FCC6000`, and zeros
elsewhere. -/
def witnessMemBEE : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(0x3FCC5100, emptyHasherBytes),
    (Image.base64EncodeToAddress, Image.base64EncodeToCode),
    (Image.b64AlphabetAddress, Image.b64AlphabetData),
    (Image.shaUpdateAddress, Image.shaUpdateCode),
    (Image.shaUpdateBlocksAddress, Image.shaUpdateBlocksCode),
    (Image.sha256CompressAddress, Image.sha256CompressCode),
    (Image.rangeFromIndexAddress, Image.rangeFromIndexCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.shaKAddress, Image.shaKData),
    (0x3FCC6000, [0x68, 0x65, 0x6C, 0x6C, 0x6F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `base64::encode_to::<Sha256>` with the 5 bytes at
`0x3FCC6000`, the empty hasher at `0x3FCC5100`, and the stack at
`0x3FCC8000` meets `base64EncodeTo_correct`'s hypotheses. -/
theorem exists_base64EncodeTo_machine :
    ∃ (m : RV32.Machine) (sp0 S D retAddr : RV32.Word) (n : Nat) (msg : List Nat),
      RV32.BeeEnv m.mem S D sp0 n ∧ m.pc = RV32.BEE ∧ RV32.reg m RV32.a0 = D ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.a2 = S ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.HasherAt m.mem S msg ∧
      msg.length + 4 * (n / 3) + 4 < 2 ^ 32 := by
  refine ⟨⟨(fun r : Fin 32 => if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 5 else if r = RV32.a2 then 0x3FCC5100
      else if r = RV32.sp then 0x3FCC8000 else 0), RV32.BEE, witnessMemBEE⟩,
    0x3FCC8000, 0x3FCC5100, 0x3FCC6000, 0, 5, [], ?_, rfl, rfl, rfl, rfl, rfl, by decide, rfl,
    ⟨by decide, ?_, rfl, ?_, ?_, ?_⟩, by decide⟩
  case refine_1 =>
    constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  all_goals decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `black_box::<u8>` with the stack at `0x3FCC8000`
meets `blackBoxU8_correct`'s hypotheses. -/
theorem exists_blackBoxU8_machine :
    ∃ (m : RV32.Machine) (base retAddr : RV32.Word), RV32.CodeIn m.mem base Image.blackBoxU8Code ∧ m.pc = base ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFF) 1 base Image.blackBoxU8Code.length := by
  refine ⟨⟨leafRegs 7 0 0, BitVec.ofNat 32 Image.blackBoxU8Address, witnessMemLeaves⟩,
    BitVec.ofNat 32 Image.blackBoxU8Address, 0, ?_, rfl, rfl, by decide, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `__lshrdi3` to shift `0x12345678_9ABCDEF0` right 5
bits meets `lshrdi3_correct`'s hypotheses. -/
theorem exists_lshrdi3_machine :
    ∃ (m : RV32.Machine) (base retAddr lo hi : RV32.Word) (s : Nat), RV32.CodeIn m.mem base Image.lshrdi3Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = lo ∧ RV32.reg m RV32.a1 = hi ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 s ∧
      s < 64 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x9ABCDEF0 0x12345678 5, BitVec.ofNat 32 Image.lshrdi3Address, witnessMemLeaves⟩,
    BitVec.ofNat 32 Image.lshrdi3Address, 0, 0x9ABCDEF0, 0x12345678, 5, ?_, rfl, rfl, rfl, rfl, by decide, rfl,
    by decide⟩
  code_in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `memcmp` on 32 bytes at `0x3FCC5000` and
`0x3FCC5100` meets `memcmp_correct`'s hypotheses. -/
theorem exists_memcmp_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word) (n : Nat), RV32.CodeIn m.mem base Image.memcmpCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      n < 2 ^ 32 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC5100 32, BitVec.ofNat 32 Image.memcmpAddress, witnessMemLeaves⟩,
    BitVec.ofNat 32 Image.memcmpAddress, 0, 0x3FCC5000, 0x3FCC5100, 32, ?_, rfl, rfl, rfl, rfl, by decide, rfl,
    by decide⟩
  code_in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `UintRef::is_nonzero` on 12 words at `0x3FCC5000`
with the stack at `0x3FCC8000` meets `uintRefIsNonzero_correct`'s
hypotheses. -/
theorem exists_uintRefIsNonzero_machine :
    ∃ (m : RV32.Machine) (base retAddr ptr : RV32.Word) (len : Nat),
      RV32.CodeIn m.mem base Image.uintRefIsNonzeroCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = ptr ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 len ∧ len < 2 ^ 32 ∧ ptr.toNat % 4 = 0 ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base Image.uintRefIsNonzeroCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 12 0, BitVec.ofNat 32 Image.uintRefIsNonzeroAddress, witnessMemLeaves⟩,
    BitVec.ofNat 32 Image.uintRefIsNonzeroAddress, 0, 0x3FCC5000, 12, ?_, rfl, rfl, rfl, by decide, by decide,
    by decide, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `ct_eq` for bytes on 0x41 and 0x41 with the stack at
`0x3FCC8000` meets `ctEqU8_correct`'s hypotheses. -/
theorem exists_ctEqU8_machine :
    ∃ (m : RV32.Machine) (base retAddr x y : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.ctEqU8Code ∧ RV32.CodeIn m.mem (base + 0xFFFFE84E) Image.blackBoxU8Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = x ∧ RV32.reg m RV32.a1 = y ∧ x.toNat < 256 ∧ y.toNat < 256 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFF) 1 (base + 0xFFFFE84E) Image.blackBoxU8Code.length := by
  refine ⟨⟨leafRegs 0x41 0x41 0, BitVec.ofNat 32 Image.ctEqU8Address, witnessMemLeaves⟩,
    BitVec.ofNat 32 Image.ctEqU8Address, 0, 0x41, 0x41, by decide, ?_, ?_, rfl, rfl, rfl, by decide, by decide,
    rfl, by decide, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls the 32-byte `ct_eq` on `0x3FCC5000` and
`0x3FCC5100` with the stack at `0x3FCC8000` meets `ctEqSlice_correct`'s
hypotheses. -/
theorem exists_ctEqSlice_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.ctEqSliceCode ∧ RV32.CodeIn m.mem (base + 0xFFFFFFE8) Image.ctEqU8Code ∧
      RV32.CodeIn m.mem (base + 0xFFFFE836) Image.blackBoxU8Code ∧ m.pc = base ∧ RV32.reg m RV32.a0 = p ∧
      RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧ 0x21 ≤ (RV32.reg m RV32.sp).toNat ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFDF) 0x21 base Image.ctEqSliceCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFDF) 0x21 (base + 0xFFFFFFE8) Image.ctEqU8Code.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFDF) 0x21 (base + 0xFFFFE836) Image.blackBoxU8Code.length ∧
      RV32.Sep p 32 (RV32.reg m RV32.sp + 0xFFFFFFDF) 0x21 ∧ RV32.Sep q 32 (RV32.reg m RV32.sp + 0xFFFFFFDF) 0x21 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC5100 0, BitVec.ofNat 32 Image.ctEqSliceAddress, witnessMemLeaves⟩,
    BitVec.ofNat 32 Image.ctEqSliceAddress, 0, 0x3FCC5000, 0x3FCC5100, by decide, ?_, ?_, ?_, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
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

/-- Memory with the current image's `CompletedPoint::as_projective`,
`<&FieldElement2625 as Mul>::mul`, and `reduce` where the image loads them,
and zeros elsewhere. -/
def witnessMemAsProjective : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.asProjectiveAddress, Image.asProjectiveCode),
    (Image.feMulAddress, Image.feMulCode),
    (Image.feReduceAddress, Image.feReduceCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `CompletedPoint::as_projective` with the result at
`0x3FCC5000`, the completed point at `0x3FCC6000`, and the stack at
`0x3FCC8000` meets `asProjective_correct`'s hypotheses. -/
theorem exists_asProjective_machine :
    ∃ (m : RV32.Machine) (P sp0 out cp retAddr : RV32.Word), RV32.ApEnv m.mem P sp0 out cp ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = cp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.asProjectiveAddress, witnessMemAsProjective⟩,
    BitVec.ofNat 32 Image.asProjectiveAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `CompletedPoint::as_extended`,
`<&FieldElement2625 as Mul>::mul`, and `reduce` where the image loads them,
and zeros elsewhere. -/
def witnessMemAsExtended : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.asExtendedAddress, Image.asExtendedCode),
    (Image.feMulAddress, Image.feMulCode),
    (Image.feReduceAddress, Image.feReduceCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `CompletedPoint::as_extended` with the result at
`0x3FCC5000`, the completed point at `0x3FCC6000`, and the stack at
`0x3FCC8000` meets `asExtended_correct`'s hypotheses. -/
theorem exists_asExtended_machine :
    ∃ (m : RV32.Machine) (P sp0 out cp retAddr : RV32.Word), RV32.AxEnv m.mem P sp0 out cp ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = cp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.asExtendedAddress, witnessMemAsExtended⟩,
    BitVec.ofNat 32 Image.asExtendedAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `ConstMontyForm<p384>::neg`, its callees,
and the modulus where the image loads them, and zeros elsewhere. -/
def witnessMemP384Neg : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p384NegAddress, Image.p384NegCode),
    (Image.uint12IsNonzeroAddress, Image.uint12IsNonzeroCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384ModulusAddress, Image.p384ModulusData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Uint<12>::is_nonzero` on 12 words at `0x3FCC5000`
with the stack at `0x3FCC8000` meets `uint12IsNonzero_correct`'s
hypotheses. -/
theorem exists_uint12IsNonzero_machine :
    ∃ (m : RV32.Machine) (base retAddr ptr : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.uint12IsNonzeroCode ∧
      RV32.CodeIn m.mem (base + 0xFFFED346) Image.uintRefIsNonzeroCode ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = ptr ∧ ptr.toNat % 4 = 0 ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 (base + 0xFFFED346) Image.uintRefIsNonzeroCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0 0, BitVec.ofNat 32 Image.uint12IsNonzeroAddress, witnessMemP384Neg⟩,
    BitVec.ofNat 32 Image.uint12IsNonzeroAddress, 0, 0x3FCC5000, by decide, ?_, ?_, rfl, rfl, by decide,
    by decide, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `ConstMontyForm<p384::FieldParams, 12>::neg` with the
result at `0x3FCC5000`, `x` at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `p384Neg_correct`'s hypotheses. -/
theorem exists_p384Neg_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word), RV32.NgEnv m.mem P sp0 out xp ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.p384NegAddress, witnessMemP384Neg⟩,
    BitVec.ofNat 32 Image.p384NegAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's DER reader functions where the image
loads them, a reader at `0x3FCC6000` whose unread bytes start at
`0x3FCC7000` and number zero, and zeros elsewhere. -/
def witnessMemDer : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.derTlvAddress, Image.derTlvCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derOidAddress, Image.derOidCode),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::tlv` with the result at `0x3FCC5000` and the
reader at `0x3FCC6000` meets `derTlv_correct`'s hypotheses. -/
theorem exists_derTlv_machine :
    ∃ (m : RV32.Machine) (base out d retAddr : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.derTlvCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = d ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ out.toNat % 4 = 0 ∧
      d.toNat % 4 = 0 ∧ RV32.Sep out 17 base Image.derTlvCode.length ∧
      RV32.Sep (d + 8) 8 base Image.derTlvCode.length := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derTlvAddress, witnessMemDer⟩,
    BitVec.ofNat 32 Image.derTlvAddress, 0x3FCC5000, 0x3FCC6000, 0, by decide, ?_, rfl, rfl, rfl, rfl, by decide,
    by decide, by decide, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::element` for tag 6 with the result at
`0x3FCC5000` and the reader at `0x3FCC6000` meets `derElement_correct`'s
hypotheses. -/
theorem exists_derElement_machine :
    ∃ (m : RV32.Machine) (base out d retAddr : RV32.Word) (tag : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.derElementCode ∧ RV32.CodeIn m.mem (base + 0x26) Image.derTlvCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 tag ∧ tag < 256 ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ out.toNat % 4 = 0 ∧ d.toNat % 4 = 0 ∧
      RV32.Sep out 17 base Image.derElementCode.length ∧ RV32.Sep out 17 (base + 0x26) Image.derTlvCode.length ∧
      RV32.Sep (d + 8) 8 (base + 0x26) Image.derTlvCode.length := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 6, BitVec.ofNat 32 Image.derElementAddress, witnessMemDer⟩,
    BitVec.ofNat 32 Image.derElementAddress, 0x3FCC5000, 0x3FCC6000, 0, 6, by decide, ?_, ?_, rfl, rfl, rfl, rfl,
    by decide, rfl, by decide, by decide, by decide, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::oid` with the result at `0x3FCC5000`, the
reader at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`derOid_correct`'s hypotheses. -/
theorem exists_derOid_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word), RV32.OidEnv m.mem P sp0 out d ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derOidAddress, witnessMemDer⟩,
    BitVec.ofNat 32 Image.derOidAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `Der::nested`, `Der::sequence`, slice
comparison, and DER reader functions where the image loads them, a reader at
`0x3FCC6000` whose unread bytes start at `0x3FCC7000` and number zero, and
zeros elsewhere. -/
def witnessMemDer2 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.derTlvAddress, Image.derTlvCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derNestedAddress, Image.derNestedCode),
    (Image.derSequenceAddress, Image.derSequenceCode),
    (Image.equalSameLengthAddress, Image.equalSameLengthCode),
    (Image.sliceEqAddress, Image.sliceEqCode),
    (Image.memcmpAddress, Image.memcmpCode),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::nested` for tag 0x30 with the result at
`0x3FCC5000`, the reader at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `derNested_correct`'s hypotheses. -/
theorem exists_derNested_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word) (tag : Nat), RV32.NestEnv m.mem P sp0 out d ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 tag ∧ tag < 256 ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0x30, BitVec.ofNat 32 Image.derNestedAddress, witnessMemDer2⟩,
    BitVec.ofNat 32 Image.derNestedAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, 0x30,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::sequence` with the result at `0x3FCC5000`,
the reader at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`derSequence_correct`'s hypotheses. -/
theorem exists_derSequence_machine :
    ∃ (m : RV32.Machine) (Q sp0 out d retAddr : RV32.Word), Q.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem Q Image.derSequenceCode ∧ RV32.NestEnv m.mem (Q + 0x278) sp0 out d ∧ m.pc = Q ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derSequenceAddress, witnessMemDer2⟩,
    BitVec.ofNat 32 Image.derSequenceAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, by decide, ?_,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩, rfl, rfl, rfl, rfl, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `Der::set`, `Der::octet_string`,
`Der::bit_string`, `Der::integer`, `Der::boolean_true`, and `Der::optional`,
and the functions they call, where the image loads them, a reader at `0x3FCC6000` whose unread bytes start at `0x3FCC7000` and
number zero, and zeros elsewhere. -/
def witnessMemDer3 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.derTlvAddress, Image.derTlvCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derNestedAddress, Image.derNestedCode),
    (Image.derSetAddress, Image.derSetCode),
    (Image.derOctetStringAddress, Image.derOctetStringCode),
    (Image.derBitStringAddress, Image.derBitStringCode),
    (Image.derIntegerAddress, Image.derIntegerCode),
    (Image.derBooleanTrueAddress, Image.derBooleanTrueCode),
    (Image.derOptionalAddress, Image.derOptionalCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::set` with the result at `0x3FCC5000`, the
reader at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`derSet_correct`'s hypotheses. -/
theorem exists_derSet_machine :
    ∃ (m : RV32.Machine) (Q sp0 out d retAddr : RV32.Word), Q.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem Q Image.derSetCode ∧ RV32.NestEnv m.mem (Q + 0xFFFFD0B0) sp0 out d ∧ m.pc = Q ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derSetAddress, witnessMemDer3⟩,
    BitVec.ofNat 32 Image.derSetAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, by decide, ?_,
    ⟨by decide, ?_, ?_, ?_, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩, rfl, rfl, rfl, rfl, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::octet_string` with the result at
`0x3FCC5000`, the reader at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `derOctetString_correct`'s hypotheses. -/
theorem exists_derOctetString_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word),
      RV32.DerCallEnv m.mem Image.derOctetStringCode P 0xFFFFCF5A sp0 out d 8 ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derOctetStringAddress, witnessMemDer3⟩,
    BitVec.ofNat 32 Image.derOctetStringAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::bit_string` with the result at `0x3FCC5000`,
the reader at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`derBitString_correct`'s hypotheses. -/
theorem exists_derBitString_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word),
      RV32.DerCallEnv m.mem Image.derBitStringCode P 0xFFFFD3A0 sp0 out d 8 ∧
      RV32.Sep (d + 8) 8 (RV32.memLoad32 m.mem (d + 8)) (RV32.memLoad32 m.mem (d + 0xC)).toNat ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derBitStringAddress, witnessMemDer3⟩,
    BitVec.ofNat 32 Image.derBitStringAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide⟩
  · constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  · first
      | decide +kernel
      | exact RV32.sep_of_le (by decide) (by decide)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::integer` with the result at `0x3FCC5000`, the
reader at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`derInteger_correct`'s hypotheses. -/
theorem exists_derInteger_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word),
      RV32.DerCallEnv m.mem Image.derIntegerCode P 0x5E sp0 out d 8 ∧
      RV32.Sep (d + 8) 8 (RV32.memLoad32 m.mem (d + 8)) (RV32.memLoad32 m.mem (d + 0xC)).toNat ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derIntegerAddress, witnessMemDer3⟩,
    BitVec.ofNat 32 Image.derIntegerAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide⟩
  · constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  · first
      | decide +kernel
      | exact RV32.sep_of_le (by decide) (by decide)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::boolean_true` with the reader at
`0x3FCC6000` and the stack at `0x3FCC8000` meets `derBooleanTrue_correct`'s
hypotheses. -/
theorem exists_derBooleanTrue_machine :
    ∃ (m : RV32.Machine) (P sp0 d retAddr : RV32.Word),
      RV32.DerCallEnv m.mem Image.derBooleanTrueCode P 0xFFFFCE92 sp0 d d 0 ∧
      RV32.Sep (d + 8) 8 (RV32.memLoad32 m.mem (d + 8)) (RV32.memLoad32 m.mem (d + 0xC)).toNat ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.derBooleanTrueAddress, witnessMemDer3⟩,
    BitVec.ofNat 32 Image.derBooleanTrueAddress, 0x3FCC8000, 0x3FCC6000, 0, ?_, ?_, rfl, rfl, rfl,
    rfl, by decide⟩
  · constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  · first
      | decide +kernel
      | exact RV32.sep_of_le (by decide) (by decide)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::optional` for tag 0x30 with the result at
`0x3FCC5000`, the reader at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `derOptional_correct`'s hypotheses. -/
theorem exists_derOptional_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word) (tag : Nat), RV32.OptEnv m.mem P sp0 out d ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 tag ∧ tag < 256 ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0x30, BitVec.ofNat 32 Image.derOptionalAddress, witnessMemDer3⟩,
    BitVec.ofNat 32 Image.derOptionalAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, 0x30, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `Uint<12>::eq`, `Uint<8>::eq`,
`less_than_le`, and `in_scalar_range` where the image loads them, and zeros
elsewhere. -/
def witnessMemCmp : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.uint12EqAddress, Image.uint12EqCode),
    (Image.uint8EqAddress, Image.uint8EqCode),
    (Image.lessThanLeAddress, Image.lessThanLeCode),
    (Image.inScalarRangeAddress, Image.inScalarRangeCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Uint<12>::eq` on `0x3FCC5000` and `0x3FCC5100`
with the stack at `0x3FCC8000` meets `uint12Eq_correct`'s hypotheses. -/
theorem exists_uint12Eq_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word), RV32.CodeIn m.mem base Image.uint12EqCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ p.toNat % 4 = 0 ∧ q.toNat % 4 = 0 ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base Image.uint12EqCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC5100 0, BitVec.ofNat 32 Image.uint12EqAddress, witnessMemCmp⟩,
    BitVec.ofNat 32 Image.uint12EqAddress, 0, 0x3FCC5000, 0x3FCC5100, ?_, rfl, rfl, rfl, by decide, by decide,
    by decide, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Uint<8>::eq` on `0x3FCC5000` and `0x3FCC5100`
with the stack at `0x3FCC8000` meets `uint8Eq_correct`'s hypotheses. -/
theorem exists_uint8Eq_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word), RV32.CodeIn m.mem base Image.uint8EqCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ p.toNat % 4 = 0 ∧ q.toNat % 4 = 0 ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base Image.uint8EqCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC5100 0, BitVec.ofNat 32 Image.uint8EqAddress, witnessMemCmp⟩,
    BitVec.ofNat 32 Image.uint8EqAddress, 0, 0x3FCC5000, 0x3FCC5100, ?_, rfl, rfl, rfl, by decide, by decide,
    by decide, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `less_than_le` on `0x3FCC5000` and `0x3FCC5100`
meets `lessThanLe_correct`'s hypotheses. -/
theorem exists_lessThanLe_machine :
    ∃ (m : RV32.Machine) (base retAddr a b : RV32.Word), RV32.CodeIn m.mem base Image.lessThanLeCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = a ∧ RV32.reg m RV32.a1 = b ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC5100 0, BitVec.ofNat 32 Image.lessThanLeAddress, witnessMemCmp⟩,
    BitVec.ofNat 32 Image.lessThanLeAddress, 0, 0x3FCC5000, 0x3FCC5100, ?_, rfl, rfl, rfl, rfl, by decide⟩
  code_in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `in_scalar_range` on 48 bytes at `0x3FCC5000` and
an order of 48 bytes at `0x3FCC5100` meets `inScalarRange_correct`'s
hypotheses. -/
theorem exists_inScalarRange_machine :
    ∃ (m : RV32.Machine) (base retAddr x o : RV32.Word) (n n' : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.inScalarRangeCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = x ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.a2 = o ∧ RV32.reg m RV32.a3 = BitVec.ofNat 32 n' ∧
      n < 2 ^ 32 ∧ n' < 2 ^ 32 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 48 else if r = RV32.a2 then 0x3FCC5100
    else if r = RV32.a3 then 48 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.inScalarRangeAddress, witnessMemCmp⟩,
    BitVec.ofNat 32 Image.inScalarRangeAddress, 0, 0x3FCC5000, 0x3FCC5100, 48, 48, by decide, ?_, rfl, rfl, rfl,
    rfl, rfl, by decide, by decide, rfl, by decide⟩
  code_in

/-- Memory with the current image's P-384 scalar `mul` and `new`,
`mul_montgomery_form::<12>` and its callees, the group order, and `R² mod n`
where the image loads them, and zeros elsewhere. -/
def witnessMemN384 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p384ScalarMulAddress, Image.p384ScalarMulCode),
    (Image.p384ScalarNewAddress, Image.p384ScalarNewCode),
    (Image.mulMont12Address, Image.mulMont12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384OrderAddress, Image.p384OrderData),
    (Image.p384ScalarR2Address, Image.p384ScalarR2Data)]

set_option exponentiation.threshold 600 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-384's scalar `mul` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC8000` meets `p384ScalarMul_correct`'s hypotheses. -/
theorem exists_p384ScalarMul_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp yp retAddr : RV32.Word), RV32.N3MEnv m.mem P sp0 out xp yp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧ RV32.reg m RV32.a2 = yp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.accV m.mem yp 12 < RV32.n384 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384ScalarMulAddress, witnessMemN384⟩,
    BitVec.ofNat 32 Image.p384ScalarMulAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0,
    ⟨?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, by decide, rfl, ?_⟩
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
/-- A machine that calls P-384's scalar `new` with the result at
`0x3FCC5000`, the operand at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `p384ScalarNew_correct`'s hypotheses. -/
theorem exists_p384ScalarNew_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word), RV32.N3NEnv m.mem P sp0 out xp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384ScalarNewAddress, witnessMemN384⟩,
    BitVec.ofNat 32 Image.p384ScalarNewAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0,
    ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, by decide, rfl⟩
  case refine_5 =>
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

/-- Memory with the current image's `u32_min`, `<[u8]>::reverse`, and the
constant-time equality functions and their callees where the image loads
them, and zeros elsewhere. -/
def witnessMemCt : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.u32MinAddress, Image.u32MinCode),
    (Image.sliceReverseAddress, Image.sliceReverseCode),
    (Image.splitAt12Address, Image.splitAt12Code),
    (Image.choiceNotAddress, Image.choiceNotCode),
    (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.uintRefIsZeroAddress, Image.uintRefIsZeroCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.limbCtEqAddress, Image.limbCtEqCode),
    (Image.uint12CtEqAddress, Image.uint12CtEqCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `u32_min` on 5 with the stack at `0x3FCC8000` meets
`u32Min_correct`'s hypotheses. -/
theorem exists_u32Min_machine :
    ∃ (m : RV32.Machine) (base retAddr a : RV32.Word), RV32.CodeIn m.mem base Image.u32MinCode ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = a ∧ RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFF) 1 base Image.u32MinCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 5 0 0, BitVec.ofNat 32 Image.u32MinAddress, witnessMemCt⟩, BitVec.ofNat 32 Image.u32MinAddress,
    0, 5, ?_, rfl, rfl, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<[u8]>::reverse` on 7 bytes at `0x3FCC5000` meets
`sliceReverse_correct`'s hypotheses. -/
theorem exists_sliceReverse_machine :
    ∃ (m : RV32.Machine) (base retAddr p : RV32.Word) (n : Nat), RV32.CodeIn m.mem base Image.sliceReverseCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧ n < 2 ^ 32 ∧
      p.toNat + n ≤ 2 ^ 32 ∧ RV32.Sep p n base Image.sliceReverseCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 7 0, BitVec.ofNat 32 Image.sliceReverseAddress, witnessMemCt⟩,
    BitVec.ofNat 32 Image.sliceReverseAddress, 0, 0x3FCC5000, 7, ?_, rfl, rfl, rfl, by decide, by decide, ?_, rfl,
    by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `UintRef::split_at (.238)` with the result at
`0x3FCC5000` meets `splitAt12_correct`'s hypotheses. -/
theorem exists_splitAt12_machine :
    ∃ (m : RV32.Machine) (base retAddr out p : RV32.Word), RV32.CodeIn m.mem base Image.splitAt12Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = p ∧ out.toNat % 4 = 0 ∧
      RV32.Sep out 16 base Image.splitAt12Code.length ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.splitAt12Address, witnessMemCt⟩,
    BitVec.ofNat 32 Image.splitAt12Address, 0, 0x3FCC5000, 0x3FCC6000, ?_, rfl, rfl, rfl, by decide, ?_, rfl,
    by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Choice::not (.164)` on 1 with the stack at
`0x3FCC8000` meets `choiceNot_correct`'s hypotheses. -/
theorem exists_choiceNot_machine :
    ∃ (m : RV32.Machine) (P retAddr c : RV32.Word), P.toNat % 2 = 0 ∧ RV32.CodeIn m.mem P Image.choiceNotCode ∧
      RV32.CodeIn m.mem (P + 0xFFFFBDEE) Image.blackBoxU8Code ∧ m.pc = P ∧ RV32.reg m RV32.a0 = c ∧ c.toNat ≤ 1 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFF) 1 (P + 0xFFFFBDEE) Image.blackBoxU8Code.length := by
  refine ⟨⟨leafRegs 1 0 0, BitVec.ofNat 32 Image.choiceNotAddress, witnessMemCt⟩, BitVec.ofNat 32 Image.choiceNotAddress,
    0, 1, by decide, ?_, ?_, rfl, rfl, by decide, rfl, by decide, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `UintRef::is_zero` on 12 words at `0x3FCC5000`
with the stack at `0x3FCC8000` meets `uintRefIsZero_correct`'s hypotheses. -/
theorem exists_uintRefIsZero_machine :
    ∃ (m : RV32.Machine) (P retAddr ptr sp0 : RV32.Word) (len : Nat), P.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem P Image.uintRefIsZeroCode ∧ RV32.CodeIn m.mem (P + 0x1A) Image.uintRefIsNonzeroCode ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ RV32.reg m RV32.a0 = ptr ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 len ∧ len < 2 ^ 32 ∧ ptr.toNat % 4 = 0 ∧
      RV32.Sep (sp0 + 0xFFFFFFEC) 0x14 P Image.uintRefIsZeroCode.length ∧
      RV32.Sep (sp0 + 0xFFFFFFEC) 0x14 (P + 0x1A) Image.uintRefIsNonzeroCode.length ∧
      RV32.Sep ptr (4 * len) (sp0 + 0xFFFFFFEC) 0x14 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 12 0, BitVec.ofNat 32 Image.uintRefIsZeroAddress, witnessMemCt⟩,
    BitVec.ofNat 32 Image.uintRefIsZeroAddress, 0, 0x3FCC5000, 0x3FCC8000, 12, by decide, ?_, ?_, rfl, rfl, by decide,
    rfl, rfl, by decide, by decide, ?_, ?_, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<[Limb] as CtEq>::ct_eq` on 12 limbs at
`0x3FCC5000` and `0x3FCC5100` meets `limbCtEq_correct`'s hypotheses. -/
theorem exists_limbCtEq_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word) (n n' : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.limbCtEqCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = p ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.a2 = q ∧ RV32.reg m RV32.a3 = BitVec.ofNat 32 n' ∧
      n < 2 ^ 32 ∧ n' < 2 ^ 32 ∧ p.toNat % 4 = 0 ∧ q.toNat % 4 = 0 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 12 else if r = RV32.a2 then 0x3FCC5100
    else if r = RV32.a3 then 12 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.limbCtEqAddress, witnessMemCt⟩, BitVec.ofNat 32 Image.limbCtEqAddress, 0,
    0x3FCC5000, 0x3FCC5100, 12, 12, by decide, ?_, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide,
    rfl, by decide⟩
  code_in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Uint<12>::ct_eq` on `0x3FCC5000` and `0x3FCC5100`
with the stack at `0x3FCC8000` meets `uint12CtEq_correct`'s hypotheses. -/
theorem exists_uint12CtEq_machine :
    ∃ (m : RV32.Machine) (P sp0 pa pb retAddr : RV32.Word), RV32.UCEEnv m.mem P sp0 pa pb ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = pa ∧ RV32.reg m RV32.a1 = pb ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC5100 0, BitVec.ofNat 32 Image.uint12CtEqAddress, witnessMemCt⟩,
    BitVec.ofNat 32 Image.uint12CtEqAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC5100, 0, ?_, rfl, rfl, rfl, rfl, rfl,
    by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `montgomery_retrieve::<12>`, P-384's
field `retrieve`, `memset`, `memcpy`, and P-384's modulus where the image
loads them, and zeros elsewhere. -/
def witnessMemRetrieve : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.montRetrieve12Address, Image.montRetrieve12Code),
    (Image.p384FieldRetrieveAddress, Image.p384FieldRetrieveCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384ModulusAddress, Image.p384ModulusData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `montgomery_retrieve::<12>` with the result at
`0x3FCC5000`, the input at `0x3FCC6000`, P-384's modulus where the image
keeps it, `k = 1`, and the stack at `0x3FCC8000` meets
`montRetrieve12_correct`'s hypotheses. -/
theorem exists_montRetrieve12_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp np K retAddr : RV32.Word),
      RV32.MREnv m.mem P sp0 out xp np ∧ m.pc = P ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.a2 = np ∧ RV32.reg m RV32.a3 = K ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      (K.toNat * (RV32.memLoad32 m.mem np).toNat + 1) % 2 ^ 32 = 0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.a2 then BitVec.ofNat 32 Image.p384ModulusAddress else if r = RV32.a3 then 1
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.montRetrieve12Address, witnessMemRetrieve⟩,
    BitVec.ofNat 32 Image.montRetrieve12Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000,
    BitVec.ofNat 32 Image.p384ModulusAddress, 1, 0, ?_, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, ?_⟩
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

set_option exponentiation.threshold 600 in
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-384's field `retrieve` with the result at
`0x3FCC5000`, the input 0 at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `p384FieldRetrieve_correct`'s hypotheses. -/
theorem exists_p384FieldRetrieve_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word), RV32.P3REnv m.mem P sp0 out xp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      RV32.accV m.mem xp 12 < RV32.p384 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p384FieldRetrieveAddress, witnessMemRetrieve⟩,
    BitVec.ofNat 32 Image.p384FieldRetrieveAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ⟨?_, ?_, ?_, ?_⟩, rfl,
    rfl, rfl, rfl, by decide, rfl, ?_⟩
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

/-- Memory with the current image's `ct_assign` functions,
`copy_from_slice_impl::<u8>`, and `memcpy` where the image loads them, and
zeros elsewhere. -/
def witnessMemCtA : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.sliceCtAssignAddress, Image.sliceCtAssignCode),
    (Image.uint12CtAssignAddress, Image.uint12CtAssignCode),
    (Image.copyFromSliceU8Address, Image.copyFromSliceU8Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<[u32] as CtAssign>::ct_assign` on 3 words at
`0x3FCC5000` and `0x3FCC5100` with the choice 1 and the stack at
`0x3FCC8000` meets `sliceCtAssign_correct`'s hypotheses. -/
theorem exists_sliceCtAssign_machine :
    ∃ (m : RV32.Machine) (B sp0 dst src c retAddr : RV32.Word) (n : Nat),
      RV32.CodeIn m.mem B Image.sliceCtAssignCode ∧ m.pc = B ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧
      0x20 ≤ sp0.toNat ∧ RV32.reg m RV32.a0 = dst ∧ RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.a2 = src ∧ RV32.reg m RV32.a3 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.a4 = c ∧
      (c = 0 ∨ c = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ dst.toNat % 4 = 0 ∧
      src.toNat % 4 = 0 ∧ dst.toNat + 4 * n ≤ 2 ^ 32 ∧
      RV32.Sep (sp0 + 0xFFFFFFE0) 0x20 B Image.sliceCtAssignCode.length ∧
      RV32.Sep dst (4 * n) B Image.sliceCtAssignCode.length ∧ RV32.Sep dst (4 * n) (sp0 + 0xFFFFFFE0) 0x20 ∧
      RV32.Sep src (4 * n) (sp0 + 0xFFFFFFE0) 0x20 ∧ RV32.Sep dst (4 * n) src (4 * n) := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 3 else if r = RV32.a2 then 0x3FCC5100
    else if r = RV32.a3 then 3 else if r = RV32.a4 then 1 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.sliceCtAssignAddress, witnessMemCtA⟩, BitVec.ofNat 32 Image.sliceCtAssignAddress,
    0x3FCC8000, 0x3FCC5000, 0x3FCC5100, 1, 0, 3, ?_, rfl, rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl,
    .inr rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<Uint<12> as CtAssign>::ct_assign` on
`0x3FCC5000` and `0x3FCC5100` with the choice 1 and the stack at
`0x3FCC8000` meets `uint12CtAssign_correct`'s hypotheses. -/
theorem exists_uint12CtAssign_machine :
    ∃ (m : RV32.Machine) (W sp0 dst src c retAddr : RV32.Word), W.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem W Image.uint12CtAssignCode ∧ RV32.CodeIn m.mem (W + 0xFFFF9B66) Image.sliceCtAssignCode ∧
      m.pc = W ∧ RV32.reg m RV32.sp = sp0 ∧ sp0.toNat % 4 = 0 ∧ 0x20 ≤ sp0.toNat ∧ RV32.reg m RV32.a0 = dst ∧
      RV32.reg m RV32.a1 = src ∧ RV32.reg m RV32.a2 = c ∧ (c = 0 ∨ c = 1) ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ dst.toNat % 4 = 0 ∧ src.toNat % 4 = 0 ∧ dst.toNat + 48 ≤ 2 ^ 32 ∧
      RV32.Sep (sp0 + 0xFFFFFFE0) 0x20 (W + 0xFFFF9B66) Image.sliceCtAssignCode.length ∧
      RV32.Sep dst 48 (W + 0xFFFF9B66) Image.sliceCtAssignCode.length ∧ RV32.Sep dst 48 (sp0 + 0xFFFFFFE0) 0x20 ∧
      RV32.Sep src 48 (sp0 + 0xFFFFFFE0) 0x20 ∧ RV32.Sep dst 48 src 48 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 1
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.uint12CtAssignAddress, witnessMemCtA⟩,
    BitVec.ofNat 32 Image.uint12CtAssignAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC5100, 1, 0, by decide, ?_, ?_, rfl,
    rfl, by decide, by decide, rfl, rfl, rfl, .inr rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_,
    ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `copy_from_slice_impl::<u8>` on 5 bytes from
`0x3FCC5100` to `0x3FCC5001` with the stack at `0x3FCC8000` meets
`copyFromSliceU8_correct`'s hypotheses. -/
theorem exists_copyFromSliceU8_machine :
    ∃ (m : RV32.Machine) (W retAddr dst src : RV32.Word) (n : Nat), W.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem W Image.copyFromSliceU8Code ∧ RV32.CodeIn m.mem (W + 0x761E) Image.memcpyStubCode ∧
      m.pc = W ∧ RV32.reg m RV32.a0 = dst ∧ RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.a2 = src ∧
      RV32.reg m RV32.a3 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      RV32.McEnv m.mem (W + 0x761E + 8) dst src (RV32.reg m RV32.sp + 0xFFFFFFF0) n := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5001 else if r = RV32.a1 then 5 else if r = RV32.a2 then 0x3FCC5100
    else if r = RV32.a3 then 5 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.copyFromSliceU8Address, witnessMemCtA⟩,
    BitVec.ofNat 32 Image.copyFromSliceU8Address, 0, 0x3FCC5001, 0x3FCC5100, 5, by decide, ?_, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, by decide, ?_⟩
  case refine_3 =>
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

/-- Memory with the current image's `Der::positive_integer`, its callees,
and the zip's `next` where the image loads them, a reader at `0x3FCC6000`
whose unread bytes start at `0x3FCC7000` and number 0, and zeros
elsewhere. -/
def witnessMemDer4 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.derTlvAddress, Image.derTlvCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derIntegerAddress, Image.derIntegerCode),
    (Image.derPositiveIntegerAddress, Image.derPositiveIntegerCode),
    (Image.zipSkipNextAddress, Image.zipSkipNextCode),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::positive_integer` with the result at
`0x3FCC5000`, the reader at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `derPositiveInteger_correct`'s hypotheses. -/
theorem exists_derPositiveInteger_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word), RV32.PIEnv m.mem P sp0 out d ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derPositiveIntegerAddress, witnessMemDer4⟩,
    BitVec.ofNat 32 Image.derPositiveIntegerAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls the zip's `next` with the zip at `0x3FCC5000`
meets `zipSkipNext_correct`'s hypotheses. -/
theorem exists_zipSkipNext_machine :
    ∃ (m : RV32.Machine) (B zp retAddr : RV32.Word), RV32.CodeIn m.mem B Image.zipSkipNextCode ∧ m.pc = B ∧
      RV32.reg m RV32.a0 = zp ∧ zp.toNat % 4 = 0 ∧ RV32.Sep (zp + 0x14) 4 B Image.zipSkipNextCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0 0, BitVec.ofNat 32 Image.zipSkipNextAddress, witnessMemDer4⟩,
    BitVec.ofNat 32 Image.zipSkipNextAddress, 0x3FCC5000, 0, ?_, rfl, rfl, by decide, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | decide +kernel

/-- Memory with the current image's `der::scalar::<48>` and
`der::scalar::<32>`, their callees, `memset`, and `memcpy` where the image
loads them, a reader at `0x3FCC6000` whose unread bytes start at
`0x3FCC7000` and number 0, and zeros elsewhere. -/
def witnessMemDer5 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.derTlvAddress, Image.derTlvCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derIntegerAddress, Image.derIntegerCode),
    (Image.derPositiveIntegerAddress, Image.derPositiveIntegerCode),
    (Image.zipSkipNextAddress, Image.zipSkipNextCode),
    (Image.derScalar48Address, Image.derScalar48Code),
    (Image.derScalar32Address, Image.derScalar32Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `der::scalar::<48>` with the result at
`0x3FCC5000`, the reader at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `derScalar48_correct`'s hypotheses. -/
theorem exists_derScalar48_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word), RV32.DSEnv m.mem P sp0 out d ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derScalar48Address, witnessMemDer5⟩,
    BitVec.ofNat 32 Image.derScalar48Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `der::scalar::<32>` with the result at
`0x3FCC5000`, the reader at `0x3FCC6000`, and the stack at `0x3FCC8000`
meets `derScalar32_correct`'s hypotheses. -/
theorem exists_derScalar32_machine :
    ∃ (m : RV32.Machine) (P sp0 out d retAddr : RV32.Word), RV32.DTEnv m.mem P sp0 out d ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derScalar32Address, witnessMemDer5⟩,
    BitVec.ofNat 32 Image.derScalar32Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `der::ecdsa_signature::<48>`, its
callees, `memset`, and `memcpy` where the image loads them, and zeros
elsewhere. -/
def witnessMemDer6 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.derSequenceAddress, Image.derSequenceCode),
    (Image.derNestedAddress, Image.derNestedCode),
    (Image.derTlvAddress, Image.derTlvCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derIntegerAddress, Image.derIntegerCode),
    (Image.derPositiveIntegerAddress, Image.derPositiveIntegerCode),
    (Image.zipSkipNextAddress, Image.zipSkipNextCode),
    (Image.ecdsaSignature48Address, Image.ecdsaSignature48Code),
    (Image.derScalar48Address, Image.derScalar48Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `der::ecdsa_signature::<48>` with the result at
`0x3FCC5000`, an empty signature at `0x3FCC7000`, and the stack at
`0x3FCC8000` meets `ecdsaSignature48_correct`'s hypotheses. -/
theorem exists_ecdsaSignature48_machine :
    ∃ (m : RV32.Machine) (P sp0 out p retAddr : RV32.Word) (n : Nat), RV32.ESEnv m.mem P sp0 out p n ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = p ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC7000 0, BitVec.ofNat 32 Image.ecdsaSignature48Address, witnessMemDer6⟩,
    BitVec.ofNat 32 Image.ecdsaSignature48Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC7000, 0, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `Der::integer_is`, its callees, and the
byte-slice comparison where the image loads them, a reader at `0x3FCC6000`
whose unread bytes start at `0x3FCC7000` and number 0, and zeros
elsewhere. -/
def witnessMemDer7 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.derTlvAddress, Image.derTlvCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derIntegerAddress, Image.derIntegerCode),
    (Image.derIntegerIsAddress, Image.derIntegerIsCode),
    (Image.sliceEqAddress, Image.sliceEqCode),
    (Image.equalSameLengthAddress, Image.equalSameLengthCode),
    (Image.memcmpAddress, Image.memcmpCode),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::integer_is` with the reader at `0x3FCC6000`
and the stack at `0x3FCC8000` meets `derIntegerIs_correct`'s hypotheses. -/
theorem exists_derIntegerIs_machine :
    ∃ (m : RV32.Machine) (P sp0 d retAddr : RV32.Word), RV32.IIEnv m.mem P sp0 d ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = d ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.derIntegerIsAddress, witnessMemDer7⟩,
    BitVec.ofNat 32 Image.derIntegerIsAddress, 0x3FCC8000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `checkpoint::line`, the `sec1::Tag`
helpers, and `time::digits::<2>` where the image loads them, a slice reader
at `0x3FCC6000` over 2 bytes at `0x3FCC7000`, and zeros elsewhere. -/
def witnessMemLeaf2 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.checkpointLineAddress, Image.checkpointLineCode),
    (Image.tagMessageLenAddress, Image.tagMessageLenCode),
    (Image.tagFromU8Address, Image.tagFromU8Code),
    (Image.timeDigits2Address, Image.timeDigits2Code),
    (0x3FCC6000, [0x00, 0x70, 0xCC, 0x3F, 0x02, 0x00, 0x00, 0x00])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `checkpoint::line` on 3 bytes meets
`checkpointLine_correct`'s hypotheses. -/
theorem exists_checkpointLine_machine :
    ∃ (m : RV32.Machine) (base retAddr out p : RV32.Word) (n : Nat), RV32.CodeIn m.mem base Image.checkpointLineCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = p ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      n < 2 ^ 32 ∧ out.toNat % 4 = 0 ∧ RV32.Sep out 16 base Image.checkpointLineCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC7000 3, BitVec.ofNat 32 Image.checkpointLineAddress, witnessMemLeaf2⟩,
    BitVec.ofNat 32 Image.checkpointLineAddress, 0, 0x3FCC5000, 0x3FCC7000, 3, ?_, rfl, rfl, rfl, rfl, by decide,
    by decide, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Tag::message_len` meets `tagMessageLen_correct`'s
hypotheses. -/
theorem exists_tagMessageLen_machine :
    ∃ (m : RV32.Machine) (base retAddr t fe : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.tagMessageLenCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = t ∧
      RV32.reg m RV32.a1 = fe ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 4 0x30 0, BitVec.ofNat 32 Image.tagMessageLenAddress, witnessMemLeaf2⟩,
    BitVec.ofNat 32 Image.tagMessageLenAddress, 0, 4, 0x30, by decide, ?_, rfl, rfl, rfl, rfl, by decide⟩
  code_in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Tag::from_u8` meets `tagFromU8_correct`'s
hypotheses. -/
theorem exists_tagFromU8_machine :
    ∃ (m : RV32.Machine) (base retAddr out b : RV32.Word), RV32.CodeIn m.mem base Image.tagFromU8Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = b ∧ out.toNat % 4 = 0 ∧
      RV32.Sep out 8 base Image.tagFromU8Code.length ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 4 0, BitVec.ofNat 32 Image.tagFromU8Address, witnessMemLeaf2⟩,
    BitVec.ofNat 32 Image.tagFromU8Address, 0, 0x3FCC5000, 4, ?_, rfl, rfl, rfl, by decide, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `time::digits::<2>` on a 2-byte slice meets
`timeDigits2_correct`'s hypotheses. -/
theorem exists_timeDigits2_machine :
    ∃ (m : RV32.Machine) (base retAddr out d p : RV32.Word) (n : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.timeDigits2Code ∧ m.pc = base ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = d ∧ d.toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧ n < 2 ^ 32 ∧ RV32.memLoad32 m.mem d = p ∧
      RV32.memLoad32 m.mem (d + 4) = BitVec.ofNat 32 n ∧ RV32.Sep out 8 base Image.timeDigits2Code.length ∧
      RV32.Sep d 8 base Image.timeDigits2Code.length ∧ RV32.Sep d 8 p 2 ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.timeDigits2Address, witnessMemLeaf2⟩,
    BitVec.ofNat 32 Image.timeDigits2Address, 0, 0x3FCC5000, 0x3FCC6000, 0x3FCC7000, 2, by decide, ?_, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | decide +kernel

/-- Memory with `time::digits::<4>` and `Iter<u8>::all(u8::is_ascii_digit)`
where the image loads them, a slice reader at `0x3FCC6000` over 4 bytes at
`0x3FCC7000`, an iterator at `0x3FCC6010` over no bytes at `0x3FCC7000`, and
zeros elsewhere. -/
def witnessMemTime : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.timeDigits4Address, Image.timeDigits4Code), (Image.allAsciiDigitAddress, Image.allAsciiDigitCode),
    (0x3FCC6000, [0x00, 0x70, 0xCC, 0x3F, 0x04, 0x00, 0x00, 0x00]),
    (0x3FCC6010, [0x00, 0x70, 0xCC, 0x3F, 0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `time::digits::<4>` on a 4-byte slice meets
`timeDigits4_correct`'s hypotheses. -/
theorem exists_timeDigits4_machine :
    ∃ (m : RV32.Machine) (base retAddr out d p : RV32.Word) (n : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.timeDigits4Code ∧ m.pc = base ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = d ∧ d.toNat % 4 = 0 ∧ out.toNat % 4 = 0 ∧ n < 2 ^ 32 ∧ RV32.memLoad32 m.mem d = p ∧
      RV32.memLoad32 m.mem (d + 4) = BitVec.ofNat 32 n ∧ RV32.Sep out 8 base Image.timeDigits4Code.length ∧
      RV32.Sep d 8 base Image.timeDigits4Code.length ∧ RV32.Sep d 8 p 4 ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.timeDigits4Address, witnessMemTime⟩,
    BitVec.ofNat 32 Image.timeDigits4Address, 0, 0x3FCC5000, 0x3FCC6000, 0x3FCC7000, 4, by decide, ?_, rfl, rfl, rfl,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Iter<u8>::all(u8::is_ascii_digit)` on an empty
iterator meets `allAsciiDigit_correct`'s hypotheses. -/
theorem exists_allAsciiDigit_machine :
    ∃ (m : RV32.Machine) (base it p retAddr : RV32.Word) (L : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.allAsciiDigitCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = it ∧
      it.toNat % 4 = 0 ∧ RV32.memLoad32 m.mem it = p ∧ RV32.memLoad32 m.mem (it + 4) = p + BitVec.ofNat 32 L ∧
      L < 2 ^ 32 ∧ RV32.Sep it 4 base Image.allAsciiDigitCode.length ∧ RV32.Sep it 4 p L ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6010 0 0, BitVec.ofNat 32 Image.allAsciiDigitAddress, witnessMemTime⟩,
    BitVec.ofNat 32 Image.allAsciiDigitAddress, 0x3FCC6010, 0x3FCC7000, 0, 0, by decide, ?_, rfl, rfl, by decide, ?_,
    ?_, by decide, ?_, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `equal_same_length` on two empty slices, with the
stack at `0x3FCC8000`, meets `equalSameLength_correct`'s hypotheses. -/
theorem exists_equalSameLength_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word) (n : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.equalSameLengthCode ∧ RV32.CodeIn m.mem (base + 0xD3BE) Image.memcmpCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 n ∧
      n < 2 ^ 32 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base Image.equalSameLengthCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 (base + 0xD3BE) Image.memcmpCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 p n ∧ RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 q n := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.equalSameLengthAddress,
    witnessMemDer2⟩, BitVec.ofNat 32 Image.equalSameLengthAddress, 0, 0x3FCC5000, 0x3FCC6000, 0, by decide, ?_, ?_,
    rfl, rfl, rfl, rfl, by decide, rfl, by decide, by decide, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that compares two empty slices with `<[u8] as PartialEq>::eq`,
with the stack at `0x3FCC8000`, meets `sliceEq_correct`'s hypotheses. -/
theorem exists_sliceEq_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word) (pl ql : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.sliceEqCode ∧ RV32.CodeIn m.mem (base + 0xFFFFEBAA) Image.equalSameLengthCode ∧
      RV32.CodeIn m.mem (base + 0xBF68) Image.memcmpCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = p ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 pl ∧ RV32.reg m RV32.a2 = q ∧ RV32.reg m RV32.a3 = BitVec.ofNat 32 ql ∧
      pl < 2 ^ 32 ∧ ql < 2 ^ 32 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 (base + 0xFFFFEBAA) Image.equalSameLengthCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 (base + 0xBF68) Image.memcmpCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 p pl ∧ RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 q ql := by
  refine ⟨⟨leafRegs 0x3FCC5000 0 0x3FCC6000, BitVec.ofNat 32 Image.sliceEqAddress, witnessMemDer2⟩,
    BitVec.ofNat 32 Image.sliceEqAddress, 0, 0x3FCC5000, 0x3FCC6000, 0, 0, by decide, ?_, ?_, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide, by decide, rfl, by decide, by decide, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `shr_in_place_wide::<8, 2>` and the
functions it calls where the image loads them, and zeros elsewhere. -/
def witnessMemShr8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.shr8Address, Image.shr8Code),
    (Image.leadMut8Address, Image.leadMut8Code),
    (Image.trailing8Address, Image.trailing8Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `shr_in_place_wide::<8, 2>` with `lo` at
`0x3FCC5000`, `hi` at `0x3FCC6000`, the shift 5, and the stack at
`0x3FCC8000` meets `shr8_correct`'s hypotheses. -/
theorem exists_shr8_machine :
    ∃ (m : RV32.Machine) (P sp0 lo hi retAddr : RV32.Word) (s : Nat), RV32.SHEnv8 m.mem P sp0 lo hi ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = lo ∧ RV32.reg m RV32.a1 = hi ∧
      RV32.reg m RV32.a2 = BitVec.ofNat 32 s ∧ 1 ≤ s ∧ s ≤ 63 ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 5
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.shr8Address, witnessMemShr8⟩, BitVec.ofNat 32 Image.shr8Address,
    0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, 5, ?_, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `FieldElement2625::to_bytes` and
`reduce` where the image loads them, and zeros elsewhere. -/
def witnessMemFeToBytes : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.feToBytesAddress, Image.feToBytesCode),
    (Image.feReduceAddress, Image.feReduceCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `FieldElement2625::to_bytes` with the result at
`0x3FCC5000`, the limbs at `0x3FCC6000`, and the stack at `0x3FCC8000` meets
`feToBytes_correct`'s hypotheses. -/
theorem exists_feToBytes_machine :
    ∃ (m : RV32.Machine) (P sp0 out fp retAddr : RV32.Word), RV32.TBEnv m.mem P sp0 out fp ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = fp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.feToBytesAddress, witnessMemFeToBytes⟩,
    BitVec.ofNat 32 Image.feToBytesAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl,
    by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `Scalar29::sub`, its callees, and
`constants::L` where the image loads them, and zeros elsewhere. -/
def witnessMemScalar29Sub : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.scalar29SubAddress, Image.scalar29SubCode),
    (Image.scalar29IndexAddress, Image.scalar29IndexCode),
    (Image.scalar29IndexMutAddress, Image.scalar29IndexMutCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.scalarLAddress, Image.scalarLData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Scalar29::sub(a, &L)` with the result at
`0x3FCC5000`, `a` at `0x3FCC6000`, and the stack at `0x3FCC7060` meets
`scalar29Sub_correct`'s hypotheses. -/
theorem exists_scalar29Sub_machine :
    ∃ (m : RV32.Machine) (P G out ap retAddr : RV32.Word), RV32.SSEnv m.mem P G out ap ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x60 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.sp then 0x3FCC7060 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.scalar29SubAddress, witnessMemScalar29Sub⟩,
    BitVec.ofNat 32 Image.scalar29SubAddress, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    by decide, rfl⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel


/-- Memory with the current image's `Scalar29::montgomery_mul`, `Scalar29::sub`
and its callees, and `constants::L` where the image loads them, and zeros
elsewhere. -/
def witnessMemScalar29MontMul : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.scalar29MontMulAddress, Image.scalar29MontMulCode),
    (Image.scalar29SubAddress, Image.scalar29SubCode),
    (Image.scalar29IndexAddress, Image.scalar29IndexCode),
    (Image.scalar29IndexMutAddress, Image.scalar29IndexMutCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.scalarLAddress, Image.scalarLData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Scalar29::montgomery_mul` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC71F0` meets `scalar29MontMul_correct`'s hypotheses. -/
theorem exists_scalar29MontMul_machine :
    ∃ (m : RV32.Machine) (P G out ap bp retAddr : RV32.Word), RV32.SMEnv m.mem P G out ap bp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.a2 = bp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x1F0 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC71F0 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.scalar29MontMulAddress, witnessMemScalar29MontMul⟩,
    BitVec.ofNat 32 Image.scalar29MontMulAddress, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0, ?_, rfl, rfl,
    rfl, rfl, rfl, by decide, rfl⟩
  constructor
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide


/-- Memory with the current image's `SignedInt<8>::lincomb_int::<2>` and the
functions and constants it reaches where the image loads them, and zeros
elsewhere. -/
def witnessMemLc8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.lincomb8Address, Image.lincomb8Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul8x2Address, Image.wideMul8x2Code),
    (Image.condNeg8Address, Image.condNeg8Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- A machine that calls `SignedInt<8>::lincomb_int::<2>` with `out` at
`0x3FCC5000`, `a`, `b`, `c`, and `d` at `0x3FCC5100` through `0x3FCC5400`,
and the stack at `0x3FCC8000` meets `lincomb8_correct`'s hypotheses. -/
theorem exists_lincomb8_machine :
    ∃ (m : RV32.Machine) (P sp0 out ap bp cp dp retAddr : RV32.Word), RV32.LCEnv8 m.mem P sp0 out ap bp cp dp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = cp ∧ RV32.reg m RV32.a4 = dp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (m.mem (ap + 0x20)).toNat ≤ 1 ∧ (m.mem (bp + 0x20)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a4 then 0x3FCC5400
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.lincomb8Address, witnessMemLc8⟩, BitVec.ofNat 32 Image.lincomb8Address,
    0x3FCC8000, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300, 0x3FCC5400, 0, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, by decide, by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's P-256 `<Scalar as Mul>::mul`,
`widening_mul_fixed::<8, 8>` and its callees, and `borrowing_sub` where the
image puts them, and zeros elsewhere. -/
def witnessMemP256ScalarMul : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p256ScalarMulAddress, Image.p256ScalarMulCode),
    (Image.wideMulAddress, Image.wideMulCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-256's `<Scalar as Mul>::mul` with the result at
`0x3FCC5000`, the operands at `0x3FCC6000` and `0x3FCC6100`, and the stack at
`0x3FCC7100` meets `p256ScalarMul_correct`'s hypotheses. -/
theorem exists_p256ScalarMul_machine :
    ∃ (m : RV32.Machine) (P G out ap bp retAddr : RV32.Word), RV32.PSMEnv m.mem P G out ap bp ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧ RV32.reg m RV32.a2 = bp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = G + 0x100 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000 else if r = RV32.a2 then 0x3FCC6100
    else if r = RV32.sp then 0x3FCC7100 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.p256ScalarMulAddress, witnessMemP256ScalarMul⟩,
    BitVec.ofNat 32 Image.p256ScalarMulAddress, 0x3FCC7000, 0x3FCC5000, 0x3FCC6000, 0x3FCC6100, 0, ?_, rfl, rfl,
    rfl, rfl, rfl, by decide, rfl⟩
  constructor
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<12>::lincomb_int_reduce_shift::<2>`
and its callees where the image loads them, and zeros elsewhere. -/
def witnessMemLs12 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.lincombShift12Address, Image.lincombShift12Code),
    (Image.lincomb12Address, Image.lincomb12Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul12x2Address, Image.wideMul12x2Code),
    (Image.condNeg12Address, Image.condNeg12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData),
    (Image.shr12Address, Image.shr12Code),
    (Image.leadMut12Address, Image.leadMut12Code),
    (Image.trailing12Address, Image.trailing12Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- A machine that calls `SignedInt<12>::lincomb_int_reduce_shift::<2>` with the
result at `0x3FCC5000`, `a`, `b`, `c`, and `d` at `0x3FCC5100` through
`0x3FCC5400`, a shift of 62, and the stack at `0x3FCC8000` meets
`lincombShift12_correct`'s hypotheses. -/
theorem exists_lincombShift12_machine :
    ∃ (m : RV32.Machine) (P G res ap bp cp dp retAddr : RV32.Word) (s : Nat), RV32.LSEnv m.mem P G res ap bp cp dp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = G + 0x270 ∧ RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = cp ∧ RV32.reg m RV32.a4 = dp ∧
      RV32.reg m RV32.a5 = BitVec.ofNat 32 s ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      1 ≤ s ∧ s ≤ 63 ∧ (m.mem (ap + 0x30)).toNat ≤ 1 ∧ (m.mem (bp + 0x30)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a4 then 0x3FCC5400 else if r = RV32.a5 then 62
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.lincombShift12Address, witnessMemLs12⟩,
    BitVec.ofNat 32 Image.lincombShift12Address, 0x3FCC7D90, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300,
    0x3FCC5400, 0, 62, ?_, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<12>::lincomb_int_reduce_shift_mod::<2>`
and its callees where the image loads them, and zeros elsewhere. -/
def witnessMemLm12 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.lincombShiftMod12Address, Image.lincombShiftMod12Code),
    (Image.lincomb12Address, Image.lincomb12Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul12x2Address, Image.wideMul12x2Code),
    (Image.condNeg12Address, Image.condNeg12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData),
    (Image.shr12Address, Image.shr12Code),
    (Image.leadMut12Address, Image.leadMut12Code),
    (Image.trailing12Address, Image.trailing12Code),
    (Image.toUintResize2Address, Image.toUintResize2Code),
    (Image.u2MaxAddress, Image.u2MaxData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- A machine that calls `SignedInt<12>::lincomb_int_reduce_shift_mod::<2>` with
the result at `0x3FCC5000`, `a`, `b`, `c`, and `d` at `0x3FCC5100` through
`0x3FCC5400`, the modulus at `0x3FCC5500`, `mi` at `0x3FCC5600`, a shift of
62, and the stack at `0x3FCC8000` meets `lincombShiftMod12_correct`'s
hypotheses. -/
theorem exists_lincombShiftMod12_machine :
    ∃ (m : RV32.Machine) (P G res ap bp cp dp mp mip retAddr : RV32.Word) (s : Nat),
      RV32.LMEnv m.mem P G res ap bp cp dp mp mip ∧
      m.pc = P ∧ RV32.reg m RV32.sp = G + 0x330 ∧ RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = cp ∧ RV32.reg m RV32.a4 = dp ∧
      RV32.reg m RV32.a5 = BitVec.ofNat 32 s ∧ RV32.reg m RV32.a6 = mp ∧ RV32.reg m 17 = mip ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      1 ≤ s ∧ s ≤ 63 ∧ (m.mem (ap + 0x30)).toNat ≤ 1 ∧ (m.mem (bp + 0x30)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a4 then 0x3FCC5400 else if r = RV32.a5 then 62
    else if r = RV32.a6 then 0x3FCC5500 else if r = 17 then 0x3FCC5600
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.lincombShiftMod12Address, witnessMemLm12⟩,
    BitVec.ofNat 32 Image.lincombShiftMod12Address, 0x3FCC7CD0, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300,
    0x3FCC5400, 0x3FCC5500, 0x3FCC5600, 0, 62, ?_, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<8>::lincomb_int_reduce_shift_mod::<2>`
and its callees where the image loads them, and zeros elsewhere. -/
def witnessMemLm8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.lincombShiftMod8Address, Image.lincombShiftMod8Code),
    (Image.lincomb8Address, Image.lincomb8Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul8x2Address, Image.wideMul8x2Code),
    (Image.condNeg8Address, Image.condNeg8Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData),
    (Image.shr8Address, Image.shr8Code),
    (Image.leadMut8Address, Image.leadMut8Code),
    (Image.trailing8Address, Image.trailing8Code),
    (Image.toUintResize2Address, Image.toUintResize2Code),
    (Image.u2MaxAddress, Image.u2MaxData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- A machine that calls `SignedInt<8>::lincomb_int_reduce_shift_mod::<2>` with
the result at `0x3FCC5000`, `a`, `b`, `c`, and `d` at `0x3FCC5100` through
`0x3FCC5400`, the modulus at `0x3FCC5500`, `mi` at `0x3FCC5600`, a shift of
62, and the stack at `0x3FCC8000` meets `lincombShiftMod8_correct`'s
hypotheses. -/
theorem exists_lincombShiftMod8_machine :
    ∃ (m : RV32.Machine) (P G res ap bp cp dp mp mip retAddr : RV32.Word) (s : Nat),
      RV32.LMEnv8 m.mem P G res ap bp cp dp mp mip ∧
      m.pc = P ∧ RV32.reg m RV32.sp = G + 0x280 ∧ RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = cp ∧ RV32.reg m RV32.a4 = dp ∧
      RV32.reg m RV32.a5 = BitVec.ofNat 32 s ∧ RV32.reg m RV32.a6 = mp ∧ RV32.reg m 17 = mip ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      1 ≤ s ∧ s ≤ 63 ∧ (m.mem (ap + 0x20)).toNat ≤ 1 ∧ (m.mem (bp + 0x20)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a4 then 0x3FCC5400 else if r = RV32.a5 then 62
    else if r = RV32.a6 then 0x3FCC5500 else if r = 17 then 0x3FCC5600
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.lincombShiftMod8Address, witnessMemLm8⟩,
    BitVec.ofNat 32 Image.lincombShiftMod8Address, 0x3FCC7D80, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300,
    0x3FCC5400, 0x3FCC5500, 0x3FCC5600, 0, 62, ?_, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<8>::lincomb_int_reduce_shift::<2>`
and its callees where the image loads them, and zeros elsewhere. -/
def witnessMemLs8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.lincombShift8Address, Image.lincombShift8Code),
    (Image.lincomb8Address, Image.lincomb8Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul8x2Address, Image.wideMul8x2Code),
    (Image.condNeg8Address, Image.condNeg8Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData),
    (Image.shr8Address, Image.shr8Code),
    (Image.leadMut8Address, Image.leadMut8Code),
    (Image.trailing8Address, Image.trailing8Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
/-- A machine that calls `SignedInt<8>::lincomb_int_reduce_shift::<2>` with the
result at `0x3FCC5000`, `a`, `b`, `c`, and `d` at `0x3FCC5100` through
`0x3FCC5400`, a shift of 62, and the stack at `0x3FCC8000` meets
`lincombShift8_correct`'s hypotheses. -/
theorem exists_lincombShift8_machine :
    ∃ (m : RV32.Machine) (P G res ap bp cp dp retAddr : RV32.Word) (s : Nat), RV32.LSEnv8 m.mem P G res ap bp cp dp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = G + 0x1F0 ∧ RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = cp ∧ RV32.reg m RV32.a4 = dp ∧
      RV32.reg m RV32.a5 = BitVec.ofNat 32 s ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      1 ≤ s ∧ s ≤ 63 ∧ (m.mem (ap + 0x20)).toNat ≤ 1 ∧ (m.mem (bp + 0x20)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a4 then 0x3FCC5400 else if r = RV32.a5 then 62
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.lincombShift8Address, witnessMemLs8⟩,
    BitVec.ofNat 32 Image.lincombShift8Address, 0x3FCC7E10, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300,
    0x3FCC5400, 0, 62, ?_, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<12>::norm`, its callees, and
P-384's modulus where the image loads them, and zeros elsewhere. -/
def witnessMemNorm12 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.norm12Address, Image.norm12Code),
    (Image.uint12IsNonzeroAddress, Image.uint12IsNonzeroCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.p384ModulusAddress, Image.p384ModulusData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `SignedInt<12>::norm` with the result at
`0x3FCC5000`, a zero value at `0x3FCC6000`, `f`'s sign 0, P-384's modulus,
and the stack at `0x3FCC8000` meets `norm12_correct`'s hypotheses. -/
theorem exists_norm12_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp np retAddr : RV32.Word), RV32.NmEnv m.mem P sp0 out xp np ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      (RV32.reg m RV32.a2 = 0 ∨ RV32.reg m RV32.a2 = 1) ∧ RV32.reg m RV32.a3 = np ∧
      (m.mem (xp + 0x30)).toNat ≤ 1 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.a3 then BitVec.ofNat 32 Image.p384ModulusAddress
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.norm12Address, witnessMemNorm12⟩,
    BitVec.ofNat 32 Image.norm12Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000,
    BitVec.ofNat 32 Image.p384ModulusAddress, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, rfl, .inl rfl, rfl, by decide +kernel, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<8>::norm` and its callees
where the image loads them, and zeros elsewhere. -/
def witnessMemNorm8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.norm8Address, Image.norm8Code),
    (Image.uint8IsNonzeroAddress, Image.uint8IsNonzeroCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Uint<8>::is_nonzero` on 8 words at `0x3FCC5000`
with the stack at `0x3FCC8000` meets `uint8IsNonzero_correct`'s
hypotheses. -/
theorem exists_uint8IsNonzero_machine :
    ∃ (m : RV32.Machine) (base retAddr ptr : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.uint8IsNonzeroCode ∧
      RV32.CodeIn m.mem (base + 0xFFFEF3FE) Image.uintRefIsNonzeroCode ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = ptr ∧ ptr.toNat % 4 = 0 ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 (base + 0xFFFEF3FE) Image.uintRefIsNonzeroCode.length ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0 0, BitVec.ofNat 32 Image.uint8IsNonzeroAddress, witnessMemNorm8⟩,
    BitVec.ofNat 32 Image.uint8IsNonzeroAddress, 0, 0x3FCC5000, by decide, ?_, ?_, rfl, rfl, by decide,
    by decide, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `SignedInt<8>::norm` with the result at
`0x3FCC5000`, a zero value at `0x3FCC6000`, `f`'s sign 0, a zero modulus at
`0x3FCC7000`, and the stack at `0x3FCC8000` meets `norm8_correct`'s
hypotheses. -/
theorem exists_norm8_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp np retAddr : RV32.Word), RV32.Nm8Env m.mem P sp0 out xp np ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      (RV32.reg m RV32.a2 = 0 ∨ RV32.reg m RV32.a2 = 1) ∧ RV32.reg m RV32.a3 = np ∧
      (m.mem (xp + 0x20)).toNat ≤ 1 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC6000
    else if r = RV32.a3 then 0x3FCC7000
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.norm8Address, witnessMemNorm8⟩,
    BitVec.ofNat 32 Image.norm8Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC7000, 0,
    ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, rfl, rfl, .inl rfl, rfl, by decide +kernel, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `UintRef::to_uint_resize::<2>` where the
image loads it, and zeros elsewhere. -/
def witnessMemTur : RV32.Word → BitVec 8 :=
  RV32.regionMem [(Image.toUintResize2Address, Image.toUintResize2Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `UintRef::to_uint_resize::<2>` with the result at
`0x3FCC5000` and the source at `0x3FCC6000` meets `toUintResize2_correct`'s
hypotheses. -/
theorem exists_toUintResize2_machine :
    ∃ (m : RV32.Machine) (P out src retAddr : RV32.Word), RV32.CodeIn m.mem P Image.toUintResize2Code ∧
      m.pc = P ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = src ∧ out.toNat % 4 = 0 ∧ src.toNat % 4 = 0 ∧
      RV32.Sep out 8 src 8 ∧ RV32.Sep out 8 P Image.toUintResize2Code.length ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.toUintResize2Address, witnessMemTur⟩,
    BitVec.ofNat 32 Image.toUintResize2Address, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, by decide, by decide,
    ?_, ?_, rfl, by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<12>::lowest` and
`Choice::select_i64` where the image loads them, and zeros elsewhere. -/
def witnessMemLowest12 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.lowest12Address, Image.lowest12Code),
    (Image.selectI64Address, Image.selectI64Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `SignedInt<12>::lowest` on a `SignedInt` at
`0x3FCC5000` with the stack at `0x3FCC8000` meets `lowest12_correct`'s
hypotheses. -/
theorem exists_lowest12_machine :
    ∃ (m : RV32.Machine) (P p retAddr : RV32.Word), P.toNat % 2 = 0 ∧ RV32.CodeIn m.mem P Image.lowest12Code ∧
      RV32.CodeIn m.mem (P + 0xFFFFE0D8) Image.selectI64Code ∧ m.pc = P ∧ RV32.reg m RV32.a0 = p ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ p.toNat % 4 = 0 ∧
      (m.mem (p + 0x30)).toNat ≤ 1 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFF) 1 (P + 0xFFFFE0D8) Image.selectI64Code.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.lowest12Address, witnessMemLowest12⟩,
    BitVec.ofNat 32 Image.lowest12Address, 0x3FCC5000, 0, by decide, ?_, ?_, rfl, rfl, rfl, by decide, by decide,
    by decide +kernel, ?_⟩
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `SignedInt<8>::lowest` and
`Choice::select_i64` where the image loads them, and zeros elsewhere. -/
def witnessMemLowest8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.lowest8Address, Image.lowest8Code),
    (Image.selectI64Address, Image.selectI64Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `SignedInt<8>::lowest` on a `SignedInt` at
`0x3FCC5000` with the stack at `0x3FCC8000` meets `lowest8_correct`'s
hypotheses. -/
theorem exists_lowest8_machine :
    ∃ (m : RV32.Machine) (P p retAddr : RV32.Word), P.toNat % 2 = 0 ∧ RV32.CodeIn m.mem P Image.lowest8Code ∧
      RV32.CodeIn m.mem (P + 0x22) Image.selectI64Code ∧ m.pc = P ∧ RV32.reg m RV32.a0 = p ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ p.toNat % 4 = 0 ∧
      (m.mem (p + 0x20)).toNat ≤ 1 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFF) 1 (P + 0x22) Image.selectI64Code.length := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.lowest8Address, witnessMemLowest8⟩,
    BitVec.ofNat 32 Image.lowest8Address, 0x3FCC5000, 0, by decide, ?_, ?_, rfl, rfl, rfl, by decide, by decide,
    by decide +kernel, ?_⟩
  all_goals first
    | code_in
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `safegcd::update_fg::<12>`, `Int<2>::from_i64`,
and `lincomb_int_reduce_shift::<2>` and its callees where the image loads them,
and zeros elsewhere. -/
def witnessMemUf12 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.updateFg12Address, Image.updateFg12Code),
    (Image.fromI64Address, Image.fromI64Code),
    (Image.lincombShift12Address, Image.lincombShift12Code),
    (Image.lincomb12Address, Image.lincomb12Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul12x2Address, Image.wideMul12x2Code),
    (Image.condNeg12Address, Image.condNeg12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData),
    (Image.shr12Address, Image.shr12Code),
    (Image.leadMut12Address, Image.leadMut12Code),
    (Image.trailing12Address, Image.trailing12Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 32000000 in
/-- A machine that calls `safegcd::update_fg::<12>` with the results at
`0x3FCC5000`, `f` and `g` at `0x3FCC5100` and `0x3FCC5200`, the matrix at
`0x3FCC5300`, a shift of 62, and the stack at `0x3FCC8000` meets
`updateFg12_correct`'s hypotheses. -/
theorem exists_updateFg12_machine :
    ∃ (m : RV32.Machine) (P G out ap bp tp retAddr : RV32.Word) (s : Nat), RV32.UFEnv m.mem P G out ap bp tp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = G + 0x2B0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = tp ∧ RV32.reg m RV32.a4 = BitVec.ofNat 32 s ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ 1 ≤ s ∧ s ≤ 63 ∧
      (m.mem (ap + 0x30)).toNat ≤ 1 ∧ (m.mem (bp + 0x30)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a4 then 62
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.updateFg12Address, witnessMemUf12⟩,
    BitVec.ofNat 32 Image.updateFg12Address, 0x3FCC7D50, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300, 0, 62, ?_, rfl,
    by decide, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `safegcd::update_de::<12>`, `Int<2>::from_i64`,
and `lincomb_int_reduce_shift_mod::<2>` and its callees where the image loads
them, and zeros elsewhere. -/
def witnessMemUd12 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.updateDe12Address, Image.updateDe12Code),
    (Image.fromI64Address, Image.fromI64Code),
    (Image.lincombShiftMod12Address, Image.lincombShiftMod12Code),
    (Image.lincomb12Address, Image.lincomb12Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul12x2Address, Image.wideMul12x2Code),
    (Image.condNeg12Address, Image.condNeg12Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect12Address, Image.uintSelect12Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData),
    (Image.shr12Address, Image.shr12Code),
    (Image.leadMut12Address, Image.leadMut12Code),
    (Image.trailing12Address, Image.trailing12Code),
    (Image.toUintResize2Address, Image.toUintResize2Code),
    (Image.u2MaxAddress, Image.u2MaxData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 32000000 in
/-- A machine that calls `safegcd::update_de::<12>` with the results at
`0x3FCC5000`, `d` and `e` at `0x3FCC5100` and `0x3FCC5200`, the modulus at
`0x3FCC5300`, `mi = 0`, the matrix at `0x3FCC5400`, a shift of 62, and the
stack at `0x3FCC8000` meets `updateDe12_correct`'s hypotheses. -/
theorem exists_updateDe12_machine :
    ∃ (m : RV32.Machine) (P G out ap bp mp tp retAddr mlo mhi : RV32.Word) (s : Nat),
      RV32.UDEnv m.mem P G out ap bp mp tp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = G + 0x380 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = mp ∧ RV32.reg m RV32.a4 = mlo ∧ RV32.reg m RV32.a5 = mhi ∧
      RV32.reg m RV32.a6 = tp ∧ RV32.reg m 17 = BitVec.ofNat 32 s ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ 1 ≤ s ∧ s ≤ 63 ∧
      (m.mem (ap + 0x30)).toNat ≤ 1 ∧ (m.mem (bp + 0x30)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a6 then 0x3FCC5400 else if r = 17 then 62
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.updateDe12Address, witnessMemUd12⟩,
    BitVec.ofNat 32 Image.updateDe12Address, 0x3FCC7C80, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300, 0x3FCC5400,
    0, 0, 0, 62, ?_, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `safegcd::update_de::<8>`, `Int<2>::from_i64`,
and `SignedInt<8>::lincomb_int_reduce_shift_mod::<2>` and its callees where the
image loads them, and zeros elsewhere. -/
def witnessMemUd8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.updateDe8Address, Image.updateDe8Code),
    (Image.fromI64Address, Image.fromI64Code),
    (Image.lincombShiftMod8Address, Image.lincombShiftMod8Code),
    (Image.lincomb8Address, Image.lincomb8Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul8x2Address, Image.wideMul8x2Code),
    (Image.condNeg8Address, Image.condNeg8Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData),
    (Image.shr8Address, Image.shr8Code),
    (Image.leadMut8Address, Image.leadMut8Code),
    (Image.trailing8Address, Image.trailing8Code),
    (Image.toUintResize2Address, Image.toUintResize2Code),
    (Image.u2MaxAddress, Image.u2MaxData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 32000000 in
/-- A machine that calls `safegcd::update_de::<8>` with the results at
`0x3FCC5000`, `d` and `e` at `0x3FCC5100` and `0x3FCC5200`, the modulus at
`0x3FCC5300`, `mi = 0`, the matrix at `0x3FCC5400`, a shift of 62, and the
stack at `0x3FCC8000` meets `updateDe8_correct`'s hypotheses. -/
theorem exists_updateDe8_machine :
    ∃ (m : RV32.Machine) (P G out ap bp mp tp retAddr mlo mhi : RV32.Word) (s : Nat),
      RV32.UD8Env m.mem P G out ap bp mp tp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = G + 0x2D0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = mp ∧ RV32.reg m RV32.a4 = mlo ∧ RV32.reg m RV32.a5 = mhi ∧
      RV32.reg m RV32.a6 = tp ∧ RV32.reg m 17 = BitVec.ofNat 32 s ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ 1 ≤ s ∧ s ≤ 63 ∧
      (m.mem (ap + 0x20)).toNat ≤ 1 ∧ (m.mem (bp + 0x20)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a6 then 0x3FCC5400 else if r = 17 then 62
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.updateDe8Address, witnessMemUd8⟩,
    BitVec.ofNat 32 Image.updateDe8Address, 0x3FCC7D30, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300, 0x3FCC5400,
    0, 0, 0, 62, ?_, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
    by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `safegcd::update_fg::<8>`, `Int<2>::from_i64`,
and `lincomb_int_reduce_shift::<2>` and its callees where the image loads them,
and zeros elsewhere. -/
def witnessMemUf8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.updateFg8Address, Image.updateFg8Code),
    (Image.fromI64Address, Image.fromI64Code),
    (Image.lincombShift8Address, Image.lincombShift8Code),
    (Image.lincomb8Address, Image.lincomb8Code),
    (Image.absSign2Address, Image.absSign2Code),
    (Image.wideMul8x2Address, Image.wideMul8x2Code),
    (Image.condNeg8Address, Image.condNeg8Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.uintSelect2Address, Image.uintSelect2Code),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.u2ZeroAddress, Image.u2ZeroData),
    (Image.u2OneAddress, Image.u2OneData),
    (Image.shr8Address, Image.shr8Code),
    (Image.leadMut8Address, Image.leadMut8Code),
    (Image.trailing8Address, Image.trailing8Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 32000000 in
/-- A machine that calls `safegcd::update_fg::<8>` with the results at
`0x3FCC5000`, `f` and `g` at `0x3FCC5100` and `0x3FCC5200`, the matrix at
`0x3FCC5300`, a shift of 62, and the stack at `0x3FCC8000` meets
`updateFg8_correct`'s hypotheses. -/
theorem exists_updateFg8_machine :
    ∃ (m : RV32.Machine) (P G out ap bp tp retAddr : RV32.Word) (s : Nat), RV32.UFEnv8 m.mem P G out ap bp tp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = G + 0x230 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.a2 = bp ∧ RV32.reg m RV32.a3 = tp ∧ RV32.reg m RV32.a4 = BitVec.ofNat 32 s ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ 1 ≤ s ∧ s ≤ 63 ∧
      (m.mem (ap + 0x20)).toNat ≤ 1 ∧ (m.mem (bp + 0x20)).toNat ≤ 1 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 0x3FCC5100 else if r = RV32.a2 then 0x3FCC5200
    else if r = RV32.a3 then 0x3FCC5300 else if r = RV32.a4 then 62
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.updateFg8Address, witnessMemUf8⟩,
    BitVec.ofNat 32 Image.updateFg8Address, 0x3FCC7DD0, 0x3FCC5000, 0x3FCC5100, 0x3FCC5200, 0x3FCC5300, 0, 62, ?_, rfl,
    by decide, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide +kernel, by decide +kernel⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- An 8-limb modulus of 3, as bytes. -/
def montModBytes8 : List Nat := 3 :: List.replicate 31 0

/-- Memory with the current image's `mul_montgomery_form::<8>`,
`Uint<8>::select`, `borrowing_sub`, `memset`, and `memcpy` where the image
loads them, the modulus at `0x3FCC6600`, and zeros elsewhere. -/
def witnessMemMont8 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.mulMont8Address, Image.mulMont8Code),
    (Image.uintSelect8Address, Image.uintSelect8Code),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (0x3FCC6600, montModBytes8)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `mul_montgomery_form::<8>` with the result at
`0x3FCC6000`, the operands at `0x3FCC6400` and `0x3FCC6500`, the modulus 3
at `0x3FCC6600`, `k = 0x55555555`, and the stack at `0x3FCC8000` meets
`mulMont8_correct`'s hypotheses. -/
theorem exists_mulMont8_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp yp np K retAddr : RV32.Word),
      RV32.MMEnv8 m.mem P sp0 out xp yp np ∧ m.pc = P ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.a2 = yp ∧ RV32.reg m RV32.a3 = np ∧ RV32.reg m RV32.a4 = K ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 ∧
      (K.toNat * (RV32.memLoad32 m.mem np).toNat + 1) % 2 ^ 32 = 0 ∧
      RV32.accV m.mem yp 8 < RV32.accV m.mem np 8 := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC6000 else if r = RV32.a1 then 0x3FCC6400 else if r = RV32.a2 then 0x3FCC6500
    else if r = RV32.a3 then 0x3FCC6600 else if r = RV32.a4 then 0x55555555
    else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.mulMont8Address, witnessMemMont8⟩, BitVec.ofNat 32 Image.mulMont8Address,
    0x3FCC8000, 0x3FCC6000, 0x3FCC6400, 0x3FCC6500, 0x3FCC6600, 0x55555555, 0, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, by decide, rfl, ?_, ?_⟩
  · constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
  all_goals decide +kernel

/-- Memory with the current image's P-256 `FieldElement::neg`, the
`field_impl::sub` it tail-calls with its callees, and the zero constant
where the image loads them, and zeros elsewhere. -/
def witnessMemNeg : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.p256FieldNegAddress, Image.p256FieldNegCode),
    (Image.fieldSubAddress, Image.fieldSubCode),
    (Image.subInnerAddress, Image.subInnerCode),
    (Image.borrowingSubAddress, Image.borrowingSubCode),
    (Image.p256ZeroAddress, Image.p256ZeroData)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-256 `FieldElement::neg` with the result at
`0x3FCC5000`, the operand at `0x3FCC6100`, and the stack at `0x3FCC8000`
meets `p256FieldNeg_correct`'s hypotheses. -/
theorem exists_p256FieldNeg_machine :
    ∃ (m : RV32.Machine) (P sp0 res bp retAddr : RV32.Word), P.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem P Image.p256FieldNegCode ∧
      RV32.FSEnv m.mem (P + 0x12) sp0 res (BitVec.ofNat 32 Image.p256ZeroAddress) bp ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.p256ZeroAddress) Image.p256ZeroData ∧ m.pc = P ∧
      RV32.reg m RV32.a0 = res ∧ RV32.reg m RV32.a1 = bp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.reg m RV32.sp = sp0 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6100 0, BitVec.ofNat 32 Image.p256FieldNegAddress, witnessMemNeg⟩,
    BitVec.ofNat 32 Image.p256FieldNegAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6100, 0, by decide, ?_, ?_, ?_, rfl,
    rfl, rfl, rfl, by decide, rfl⟩
  · code_in
  · constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  · code_in

/-- Memory with the current image's two `ScalarValue::is_zero` instances and
their callees where the image loads them, and zeros elsewhere. -/
def witnessMemScalarZero : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.scalarIsZero384Address, Image.scalarIsZero384Code),
    (Image.scalarIsZero256Address, Image.scalarIsZero256Code),
    (Image.memsetAddress, Image.memsetCode),
    (Image.limbCtEqAddress, Image.limbCtEqCode),
    (Image.uintRefIsZeroAddress, Image.uintRefIsZeroCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.blackBoxU8Address, Image.blackBoxU8Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `ScalarValue<NistP384>::is_zero` on the scalar at
`0x3FCC6000` with the stack at `0x3FCC8000` meets `scalarIsZero384_correct`'s
hypotheses. -/
theorem exists_scalarIsZero384_machine :
    ∃ (m : RV32.Machine) (P sp0 x retAddr : RV32.Word), RV32.SZEnv m.mem P sp0 x ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = x ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.scalarIsZero384Address, witnessMemScalarZero⟩,
    BitVec.ofNat 32 Image.scalarIsZero384Address, 0x3FCC8000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `ScalarValue<NistP256>::is_zero` on the scalar at
`0x3FCC6000` with the stack at `0x3FCC8000` meets `scalarIsZero256_correct`'s
hypotheses. -/
theorem exists_scalarIsZero256_machine :
    ∃ (m : RV32.Machine) (P sp0 x retAddr : RV32.Word), RV32.SYEnv m.mem P sp0 x ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = x ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.scalarIsZero256Address, witnessMemScalarZero⟩,
    BitVec.ofNat 32 Image.scalarIsZero256Address, 0x3FCC8000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's byte comparisons, constant-time
wrappers, `split_at (.165)`, `Result::and_then(Tag::from_u8)`, and their
callees where the image loads them, and zeros elsewhere. -/
def witnessMemWrap : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.arr32EqAddress, Image.arr32EqCode),
    (Image.arr32NeAddress, Image.arr32NeCode),
    (Image.sliceNeAddress, Image.sliceNeCode),
    (Image.sliceEqAddress, Image.sliceEqCode),
    (Image.equalSameLengthAddress, Image.equalSameLengthCode),
    (Image.memcmpAddress, Image.memcmpCode),
    (Image.choiceCtEqAddress, Image.choiceCtEqCode),
    (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.montyScalarCtEq384Address, Image.montyScalarCtEq384Code),
    (Image.uint12CtEqAddress, Image.uint12CtEqCode),
    (Image.splitAt12Address, Image.splitAt12Code),
    (Image.limbCtEqAddress, Image.limbCtEqCode),
    (Image.uintRefIsZeroAddress, Image.uintRefIsZeroCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.splitAt8Address, Image.splitAt8Code),
    (Image.tagAndThenAddress, Image.tagAndThenCode),
    (Image.tagFromU8Address, Image.tagFromU8Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<[u8; 32] as PartialEq>::eq` on `0x3FCC5000` and
`0x3FCC6000` with the stack at `0x3FCC8000` meets `arr32Eq_correct`'s
hypotheses. -/
theorem exists_arr32Eq_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.arr32EqCode ∧ RV32.CodeIn m.mem (base + 0xC032) Image.memcmpCode ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base Image.arr32EqCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 (base + 0xC032) Image.memcmpCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 p 32 ∧ RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 q 32 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.arr32EqAddress, witnessMemWrap⟩,
    BitVec.ofNat 32 Image.arr32EqAddress, 0, 0x3FCC5000, 0x3FCC6000, by decide, ?_, ?_, rfl, rfl, rfl, rfl, by decide,
    by decide, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<[u8; 32] as PartialEq>::ne` on `0x3FCC5000` and
`0x3FCC6000` with the stack at `0x3FCC8000` meets `arr32Ne_correct`'s
hypotheses. -/
theorem exists_arr32Ne_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.arr32NeCode ∧ RV32.CodeIn m.mem (base + 0x9F10) Image.memcmpCode ∧ m.pc = base ∧
      RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base Image.arr32NeCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 (base + 0x9F10) Image.memcmpCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 p 32 ∧ RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 q 32 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.arr32NeAddress, witnessMemWrap⟩,
    BitVec.ofNat 32 Image.arr32NeAddress, 0, 0x3FCC5000, 0x3FCC6000, by decide, ?_, ?_, rfl, rfl, rfl, rfl, by decide,
    by decide, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<&[u8] as PartialEq>::ne` on two 2-byte slices with
the stack at `0x3FCC8000` meets `sliceNe_correct`'s hypotheses. -/
theorem exists_sliceNe_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word) (pl ql : Nat), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.sliceNeCode ∧ RV32.CodeIn m.mem (base + 0xFFFFF372) Image.sliceEqCode ∧
      RV32.CodeIn m.mem (base + 0xFFFFDF1C) Image.equalSameLengthCode ∧
      RV32.CodeIn m.mem (base + 0xB2DA) Image.memcmpCode ∧ m.pc = base ∧ RV32.reg m RV32.a0 = p ∧
      RV32.reg m RV32.a1 = BitVec.ofNat 32 pl ∧ RV32.reg m RV32.a2 = q ∧ RV32.reg m RV32.a3 = BitVec.ofNat 32 ql ∧
      pl < 2 ^ 32 ∧ ql < 2 ^ 32 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFEC) 0x14 base Image.sliceNeCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFEC) 0x14 (base + 0xFFFFF372) Image.sliceEqCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFEC) 0x14 (base + 0xFFFFDF1C) Image.equalSameLengthCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFEC) 0x14 (base + 0xB2DA) Image.memcmpCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFEC) 0x14 p pl ∧ RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFEC) 0x14 q ql := by
  let regs : Fin 32 → RV32.Word := fun r =>
    if r = RV32.a0 then 0x3FCC5000 else if r = RV32.a1 then 2 else if r = RV32.a2 then 0x3FCC6000
    else if r = RV32.a3 then 2 else if r = RV32.sp then 0x3FCC8000 else 0
  refine ⟨⟨regs, BitVec.ofNat 32 Image.sliceNeAddress, witnessMemWrap⟩,
    BitVec.ofNat 32 Image.sliceNeAddress, 0, 0x3FCC5000, 0x3FCC6000, 2, 2, by decide, ?_, ?_, ?_, ?_, rfl, rfl, rfl,
    rfl, rfl, by decide, by decide, rfl, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<Choice as ConstantTimeEq>::ct_eq` with the stack
at `0x3FCC8000` meets `choiceCtEq_correct`'s hypotheses. -/
theorem exists_choiceCtEq_machine :
    ∃ (m : RV32.Machine) (base retAddr a b : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.choiceCtEqCode ∧ RV32.CodeIn m.mem (base + 0x9A7E) Image.blackBoxU8Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = a ∧ RV32.reg m RV32.a1 = b ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFEF) 0x11 base Image.choiceCtEqCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFEF) 0x11 (base + 0x9A7E) Image.blackBoxU8Code.length := by
  refine ⟨⟨leafRegs 1 0 0, BitVec.ofNat 32 Image.choiceCtEqAddress, witnessMemWrap⟩,
    BitVec.ofNat 32 Image.choiceCtEqAddress, 0, 1, 0, by decide, ?_, ?_, rfl, rfl, rfl, rfl, by decide, by decide,
    ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<ConstMontyForm<p384 scalar> as ConstantTimeEq>::ct_eq`
on `0x3FCC5000` and `0x3FCC6000` with the stack at `0x3FCC8000` meets
`montyScalarCtEq384_correct`'s hypotheses. -/
theorem exists_montyScalarCtEq384_machine :
    ∃ (m : RV32.Machine) (P sp0 pa pb retAddr : RV32.Word), RV32.MSEnv m.mem P sp0 pa pb ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = pa ∧ RV32.reg m RV32.a1 = pb ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.montyScalarCtEq384Address, witnessMemWrap⟩,
    BitVec.ofNat 32 Image.montyScalarCtEq384Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `UintRef::split_at (.165)` meets `splitAt8_correct`'s
hypotheses. -/
theorem exists_splitAt8_machine :
    ∃ (m : RV32.Machine) (base retAddr out p : RV32.Word), RV32.CodeIn m.mem base Image.splitAt8Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = p ∧ out.toNat % 4 = 0 ∧
      RV32.Sep out 16 base Image.splitAt8Code.length ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.splitAt8Address, witnessMemWrap⟩,
    BitVec.ofNat 32 Image.splitAt8Address, 0, 0x3FCC5000, 0x3FCC6000, ?_, rfl, rfl, rfl, by decide, ?_, rfl,
    by decide⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Result<u8, sec1::Error>::and_then(Tag::from_u8)`
with the result at `0x3FCC5000`, the input at `0x3FCC6000`, and the stack at
`0x3FCC8000` meets `tagAndThen_correct`'s hypotheses. -/
theorem exists_tagAndThen_machine :
    ∃ (m : RV32.Machine) (base retAddr out rp : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.tagAndThenCode ∧ RV32.CodeIn m.mem (base + 0x3E) Image.tagFromU8Code ∧
      RV32.CodeIn m.mem (base + 0x137C4) Image.memcpyStubCode ∧
      RV32.McEnv m.mem (base + 0x137C4 + 8) out rp (RV32.reg m RV32.sp + 0xFFFFFFF0) 0x34 ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = rp ∧ out.toNat % 4 = 0 ∧ rp.toNat % 4 = 0 ∧
      RV32.Sep out 8 (base + 0x3E) Image.tagFromU8Code.length ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.tagAndThenAddress, witnessMemWrap⟩,
    BitVec.ofNat 32 Image.tagAndThenAddress, 0, 0x3FCC5000, 0x3FCC6000, by decide, ?_, ?_, ?_, ?_, rfl, rfl, rfl,
    by decide, by decide, ?_, rfl, by decide⟩
  · code_in
  · code_in
  · code_in
  · constructor
    all_goals first
      | code_in
      | decide
      | exact RV32.sep_of_le (by decide) (by decide)
      | exact (RV32.sep_of_le (by decide) (by decide)).symm
      | decide +kernel
  · exact RV32.sep_of_le (by decide) (by decide)

/-- Memory with the current image's `conditional_select`s and their callers
(including the `CtOption<AffinePoint>` conversions), `Uint<8>::ct_eq`, `NonZeroScalar::new`, their callees, and P-384's zero scalar
where the image loads them, and zeros elsewhere. -/
def witnessMemSel : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.condSelect384Address, Image.condSelect384Code),
    (Image.condSelect256Address, Image.condSelect256Code),
    (Image.ctIntoAffine384Address, Image.ctIntoAffine384Code),
    (Image.ctIntoAffine256Address, Image.ctIntoAffine256Code),
    (Image.unwrapOr384Address, Image.unwrapOr384Code),
    (Image.unwrapOr256Address, Image.unwrapOr256Code),
    (Image.ctMap384Address, Image.ctMap384Code),
    (Image.ctMap256Address, Image.ctMap256Code),
    (Image.uint8CtEqAddress, Image.uint8CtEqCode),
    (Image.p256ScalarCtEqAddress, Image.p256ScalarCtEqCode),
    (Image.nonZero384Address, Image.nonZero384Code),
    (Image.nonZero256Address, Image.nonZero256Code),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.uint12CtAssignAddress, Image.uint12CtAssignCode),
    (Image.sliceCtAssignAddress, Image.sliceCtAssignCode),
    (Image.montyScalarCtEq384Address, Image.montyScalarCtEq384Code),
    (Image.uint12CtEqAddress, Image.uint12CtEqCode),
    (Image.splitAt12Address, Image.splitAt12Code),
    (Image.splitAt8Address, Image.splitAt8Code),
    (Image.limbCtEqAddress, Image.limbCtEqCode),
    (Image.uintRefIsZeroAddress, Image.uintRefIsZeroCode),
    (Image.uintRefIsNonzeroAddress, Image.uintRefIsNonzeroCode),
    (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.choiceNotAddress, Image.choiceNotCode),
    (Image.scalarZero384Address, Image.scalarZero384Data)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-384's field `conditional_select` with the result at `0x3FCC5000`, the operands at
`0x3FCC6000` and `0x3FCC7000`, the choice 0, and the stack at `0x3FCC8000`
meets `condSelect384_correct`'s hypotheses. -/
theorem exists_condSelect384_machine :
    ∃ (m : RV32.Machine) (P sp0 out a b c retAddr : RV32.Word), RV32.CSEnv m.mem P sp0 out a b ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = a ∧ RV32.reg m RV32.a2 = b ∧
      RV32.reg m RV32.a3 = c ∧ (c = 0 ∨ c = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0x3FCC7000, BitVec.ofNat 32 Image.condSelect384Address, witnessMemSel⟩,
    BitVec.ofNat 32 Image.condSelect384Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC7000, 0, 0, ?_, rfl, rfl, rfl,
    rfl, rfl, rfl, .inl rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-256's field `conditional_select` with the result at `0x3FCC5000`, the operands at
`0x3FCC6000` and `0x3FCC7000`, the choice 0, and the stack at `0x3FCC8000`
meets `condSelect256_correct`'s hypotheses. -/
theorem exists_condSelect256_machine :
    ∃ (m : RV32.Machine) (P sp0 out a b c retAddr : RV32.Word), RV32.CS2Env m.mem P sp0 out a b ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = a ∧ RV32.reg m RV32.a2 = b ∧
      RV32.reg m RV32.a3 = c ∧ (c = 0 ∨ c = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0x3FCC7000, BitVec.ofNat 32 Image.condSelect256Address, witnessMemSel⟩,
    BitVec.ofNat 32 Image.condSelect256Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC7000, 0, 0, ?_, rfl, rfl, rfl,
    rfl, rfl, rfl, .inl rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `CtOption<AffinePoint<NistP384>>::unwrap_or` with the result at `0x3FCC5000`, the option at
`0x3FCC6000`, the default at `0x3FCC7000`, and the stack at `0x3FCC8000` meets
`unwrapOr384_correct`'s hypotheses. -/
theorem exists_unwrapOr384_machine :
    ∃ (m : RV32.Machine) (P sp0 out s d retAddr : RV32.Word), RV32.UOEnv m.mem P sp0 out s d ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = s ∧ RV32.reg m RV32.a2 = d ∧
      (m.mem (s + 0x64) = 0 ∨ m.mem (s + 0x64) = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0x3FCC7000, BitVec.ofNat 32 Image.unwrapOr384Address, witnessMemSel⟩,
    BitVec.ofNat 32 Image.unwrapOr384Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC7000, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, .inl (by decide +kernel), rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that converts the option at `0x3FCC6000` with
`CtOption<AffinePoint<NistP384>>::into`, with the result at `0x3FCC5000` and
the stack at `0x3FCC8000`, meets `ctIntoAffine384_correct`'s hypotheses. -/
theorem exists_ctIntoAffine384_machine :
    ∃ (m : RV32.Machine) (out s sp0 retAddr : RV32.Word),
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.ctIntoAffine384Address) Image.ctIntoAffine384Code ∧
      RV32.UOEnv m.mem (BitVec.ofNat 32 Image.unwrapOr384Address) (sp0 + 0xFFFFFFF0) out s (img% p384AffineIdentityAddress) ∧
      m.pc = BitVec.ofNat 32 Image.ctIntoAffine384Address ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = s ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (m.mem (s + 0x64) = 0 ∨ m.mem (s + 0x64) = 1) ∧ 0x90 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧
      out.toNat + 0x65 ≤ 0x40000000 ∧ RV32.Sep out 0x65 (sp0 + 0xFFFFFFF0) 16 ∧
      RV32.Sep s 0x65 (sp0 + 0xFFFFFFF0) 16 ∧ RV32.Sep (img% p384AffineIdentityAddress : RV32.Word) 0x61 (sp0 + 0xFFFFFFF0) 16 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.ctIntoAffine384Address, witnessMemSel⟩,
    0x3FCC5000, 0x3FCC6000, 0x3FCC8000, 0, by code_in, ?_, rfl, rfl, rfl, rfl, rfl, by decide,
    .inl (by decide +kernel), by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that converts the option at `0x3FCC6000` with
`CtOption<AffinePoint<NistP256>>::into`, with the result at `0x3FCC5000` and
the stack at `0x3FCC8000`, meets `ctIntoAffine256_correct`'s hypotheses. -/
theorem exists_ctIntoAffine256_machine :
    ∃ (m : RV32.Machine) (out s sp0 retAddr : RV32.Word),
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.ctIntoAffine256Address) Image.ctIntoAffine256Code ∧
      RV32.UO2Env m.mem (BitVec.ofNat 32 Image.unwrapOr256Address) (sp0 + 0xFFFFFFF0) out s (img% p256AffineIdXAddress) ∧
      m.pc = BitVec.ofNat 32 Image.ctIntoAffine256Address ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧
      RV32.reg m RV32.a1 = s ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      (m.mem (s + 0x44) = 0 ∨ m.mem (s + 0x44) = 1) ∧ 0x80 ≤ sp0.toNat ∧ sp0.toNat ≤ 0x40000000 ∧
      out.toNat + 0x45 ≤ 0x40000000 ∧ RV32.Sep out 0x45 (sp0 + 0xFFFFFFF0) 16 ∧
      RV32.Sep s 0x45 (sp0 + 0xFFFFFFF0) 16 ∧ RV32.Sep (img% p256AffineIdXAddress : RV32.Word) 0x41 (sp0 + 0xFFFFFFF0) 16 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.ctIntoAffine256Address, witnessMemSel⟩,
    0x3FCC5000, 0x3FCC6000, 0x3FCC8000, 0, by code_in, ?_, rfl, rfl, rfl, rfl, rfl, by decide,
    .inl (by decide +kernel), by decide, by decide, by decide, RV32.sep_of_le (by decide) (by decide),
    RV32.sep_of_le (by decide) (by decide), RV32.sep_of_le (by decide) (by decide)⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `CtOption<AffinePoint<NistP256>>::unwrap_or` with the result at `0x3FCC5000`, the option at
`0x3FCC6000`, the default at `0x3FCC7000`, and the stack at `0x3FCC8000` meets
`unwrapOr256_correct`'s hypotheses. -/
theorem exists_unwrapOr256_machine :
    ∃ (m : RV32.Machine) (P sp0 out s d retAddr : RV32.Word), RV32.UO2Env m.mem P sp0 out s d ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = s ∧ RV32.reg m RV32.a2 = d ∧
      (m.mem (s + 0x44) = 0 ∨ m.mem (s + 0x44) = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0x3FCC7000, BitVec.ofNat 32 Image.unwrapOr256Address, witnessMemSel⟩,
    BitVec.ofNat 32 Image.unwrapOr256Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC7000, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, .inl (by decide +kernel), rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `CtOption<MontyFieldElement<p384>>::map` with the result at `0x3FCC5000`, the option at
`0x3FCC6000`, and the stack at `0x3FCC8000` meets `ctMap384_correct`'s
hypotheses. -/
theorem exists_ctMap384_machine :
    ∃ (m : RV32.Machine) (P sp0 out x retAddr : RV32.Word), RV32.CMEnv m.mem P sp0 out x ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = x ∧
      (m.mem (x + 0x30) = 0 ∨ m.mem (x + 0x30) = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.ctMap384Address, witnessMemSel⟩,
    BitVec.ofNat 32 Image.ctMap384Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    .inl (by decide +kernel), rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `CtOption<MontyFieldElement<p256>>::map` with the result at `0x3FCC5000`, the option at
`0x3FCC6000`, and the stack at `0x3FCC8000` meets `ctMap256_correct`'s
hypotheses. -/
theorem exists_ctMap256_machine :
    ∃ (m : RV32.Machine) (P sp0 out x retAddr : RV32.Word), RV32.CM2Env m.mem P sp0 out x ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = x ∧
      (m.mem (x + 0x20) = 0 ∨ m.mem (x + 0x20) = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.ctMap256Address, witnessMemSel⟩,
    BitVec.ofNat 32 Image.ctMap256Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    .inl (by decide +kernel), rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Uint<8>::ct_eq` on `0x3FCC5000` and `0x3FCC6000` with the stack at `0x3FCC8000` meets
`uint8CtEq_correct`'s hypotheses. -/
theorem exists_uint8CtEq_machine :
    ∃ (m : RV32.Machine) (P sp0 p q retAddr : RV32.Word), RV32.U8CEEnv m.mem P sp0 p q ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.uint8CtEqAddress, witnessMemSel⟩,
    BitVec.ofNat 32 Image.uint8CtEqAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls P-256's `Scalar::ct_eq` on `0x3FCC5000` and `0x3FCC6000` with the stack at `0x3FCC8000` meets
`p256ScalarCtEq_correct`'s hypotheses. -/
theorem exists_p256ScalarCtEq_machine :
    ∃ (m : RV32.Machine) (P sp0 p q retAddr : RV32.Word), RV32.P2SEnv m.mem P sp0 p q ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.p256ScalarCtEqAddress, witnessMemSel⟩,
    BitVec.ofNat 32 Image.p256ScalarCtEqAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `NonZeroScalar<NistP384>::new` with the result at `0x3FCC5000` and the scalar at `0x3FCC6000` with the stack at `0x3FCC8000` meets
`nonZero384_correct`'s hypotheses. -/
theorem exists_nonZero384_machine :
    ∃ (m : RV32.Machine) (P sp0 p q retAddr : RV32.Word), RV32.NZEnv m.mem P sp0 p q ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.nonZero384Address, witnessMemSel⟩,
    BitVec.ofNat 32 Image.nonZero384Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `NonZeroScalar<NistP256>::new` with the result at `0x3FCC5000` and the scalar at `0x3FCC6000` with the stack at `0x3FCC8000` meets
`nonZero256_correct`'s hypotheses. -/
theorem exists_nonZero256_machine :
    ∃ (m : RV32.Machine) (P sp0 p q retAddr : RV32.Word), RV32.NZ2Env m.mem P sp0 p q ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.nonZero256Address, witnessMemSel⟩,
    BitVec.ofNat 32 Image.nonZero256Address, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `<[u8; 32] as PartialEq>::eq` in
`c3_crypto`, `FieldElement2625::is_negative`, `__ashldi3`, and their callees
where the image loads them, and zeros elsewhere. -/
def witnessMemB4 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.arr32EqCryptoAddress, Image.arr32EqCryptoCode),
    (Image.memcmpAddress, Image.memcmpCode),
    (Image.feIsNegativeAddress, Image.feIsNegativeCode),
    (Image.feToBytesAddress, Image.feToBytesCode),
    (Image.feReduceAddress, Image.feReduceCode),
    (Image.blackBoxU8Address, Image.blackBoxU8Code),
    (Image.ashldi3Address, Image.ashldi3Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `<[u8; 32] as PartialEq>::eq` in `c3_crypto` on
`0x3FCC5000` and `0x3FCC6000` with the stack at `0x3FCC8000` meets
`arr32EqCrypto_correct`'s hypotheses. -/
theorem exists_arr32EqCrypto_machine :
    ∃ (m : RV32.Machine) (base retAddr p q : RV32.Word), base.toNat % 2 = 0 ∧
      RV32.CodeIn m.mem base Image.arr32EqCryptoCode ∧ RV32.CodeIn m.mem (base + 0x11896) Image.memcmpCode ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = q ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ (RV32.reg m RV32.sp).toNat % 4 = 0 ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 base Image.arr32EqCryptoCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 (base + 0x11896) Image.memcmpCode.length ∧
      RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 p 32 ∧ RV32.Sep (RV32.reg m RV32.sp + 0xFFFFFFFC) 4 q 32 := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.arr32EqCryptoAddress, witnessMemB4⟩,
    BitVec.ofNat 32 Image.arr32EqCryptoAddress, 0, 0x3FCC5000, 0x3FCC6000, by decide, ?_, ?_, rfl, rfl, rfl, rfl,
    by decide, by decide, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `FieldElement2625::is_negative` on the limbs at
`0x3FCC6000` with the stack at `0x3FCC8000` meets `feIsNegative_correct`'s
hypotheses. -/
theorem exists_feIsNegative_machine :
    ∃ (m : RV32.Machine) (P sp0 fp retAddr : RV32.Word), RV32.FINEnv m.mem P sp0 fp ∧ m.pc = P ∧
      RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = fp ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.feIsNegativeAddress, witnessMemB4⟩,
    BitVec.ofNat 32 Image.feIsNegativeAddress, 0x3FCC8000, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `__ashldi3` to shift `0x12345678_9ABCDEF0` left 5
bits meets `ashldi3_correct`'s hypotheses. -/
theorem exists_ashldi3_machine :
    ∃ (m : RV32.Machine) (base retAddr lo hi : RV32.Word) (s : Nat), RV32.CodeIn m.mem base Image.ashldi3Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = lo ∧ RV32.reg m RV32.a1 = hi ∧ RV32.reg m RV32.a2 = BitVec.ofNat 32 s ∧
      s < 64 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x9ABCDEF0 0x12345678 5, BitVec.ofNat 32 Image.ashldi3Address, witnessMemB4⟩,
    BitVec.ofNat 32 Image.ashldi3Address, 0, 0x9ABCDEF0, 0x12345678, 5, ?_, rfl, rfl, rfl, rfl, by decide, rfl,
    by decide⟩
  code_in

/-- Memory with the current image's `Der::algorithm` and the functions it
calls where the image loads them, a reader at `0x3FCC6000` whose unread
bytes start at `0x3FCC7000` and number zero, and zeros elsewhere. -/
def witnessMemAlg : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.derTlvAddress, Image.derTlvCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derNestedAddress, Image.derNestedCode),
    (Image.derSequenceAddress, Image.derSequenceCode),
    (Image.derOidAddress, Image.derOidCode),
    (Image.derAlgorithmAddress, Image.derAlgorithmCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Der::algorithm` with the result at `0x3FCC5000`,
the reader at `0x3FCC6000` over no unread bytes at `0x3FCC7000`, and the
stack at `0x3FCC8000` meets `derAlgorithm_correct`'s hypotheses. -/
theorem exists_derAlgorithm_machine :
    ∃ (m : RV32.Machine) (P sp0 out d p retAddr : RV32.Word) (n : Nat), RV32.AlgEnv m.mem P sp0 out d p n ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = d ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC5000 0x3FCC6000 0, BitVec.ofNat 32 Image.derAlgorithmAddress, witnessMemAlg⟩,
    BitVec.ofNat 32 Image.derAlgorithmAddress, 0x3FCC8000, 0x3FCC5000, 0x3FCC6000, 0x3FCC7000, 0, 0, ?_, rfl, rfl,
    rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `lists_oid` and the functions it calls
where the image loads them, and zeros elsewhere. -/
def witnessMemListsOid : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.listsOidAddress, Image.listsOidCode),
    (Image.derSequenceAddress, Image.derSequenceCode),
    (Image.derNestedAddress, Image.derNestedCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derTlvAddress, Image.derTlvCode),
    (Image.derOidAddress, Image.derOidCode),
    (Image.sliceEqAddress, Image.sliceEqCode),
    (Image.equalSameLengthAddress, Image.equalSameLengthCode),
    (Image.memcmpAddress, Image.memcmpCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `lists_oid` on an empty list at `0x3FCC7000` and an
empty OID at `0x3FCC7100` with the stack at `0x3FCC8000` meets
`listsOid_correct`'s hypotheses. -/
theorem exists_listsOid_machine :
    ∃ (m : RV32.Machine) (P sp0 p q retAddr : RV32.Word) (n ql : Nat), RV32.LOEnv m.mem P sp0 p q n ql ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧
      RV32.reg m RV32.a2 = q ∧ RV32.reg m RV32.a3 = BitVec.ofNat 32 ql ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC7000 0 0x3FCC7100, BitVec.ofNat 32 Image.listsOidAddress, witnessMemListsOid⟩,
    BitVec.ofNat 32 Image.listsOidAddress, 0x3FCC8000, 0x3FCC7000, 0x3FCC7100, 0, 0, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `UintRef::leading_zeros` where the image
loads it, and zeros elsewhere. -/
def witnessMemLz : RV32.Word → BitVec 8 :=
  RV32.regionMem [(Image.leadingZerosAddress, Image.leadingZerosCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `UintRef::leading_zeros` on no limbs at `0x3FCC6000`
with the stack at `0x3FCC8000` meets `leadingZeros_correct`'s hypotheses. -/
theorem exists_leadingZeros_machine :
    ∃ (m : RV32.Machine) (P sp0 p retAddr : RV32.Word) (n : Nat), RV32.CodeIn m.mem P Image.leadingZerosCode ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = p ∧ RV32.reg m RV32.a1 = BitVec.ofNat 32 n ∧
      n < 2 ^ 32 ∧ p.toNat % 4 = 0 ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧
      sp0.toNat % 4 = 0 ∧ RV32.Sep (sp0 + 0xFFFFFFE0) 0x20 P Image.leadingZerosCode.length ∧
      RV32.Sep p (4 * n) (sp0 + 0xFFFFFFE0) 0x20 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.leadingZerosAddress, witnessMemLz⟩,
    BitVec.ofNat 32 Image.leadingZerosAddress, 0x3FCC8000, 0x3FCC6000, 0, 0, ?_, rfl, rfl, rfl, rfl, by decide,
    by decide, rfl, by decide, by decide, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel


/-- Memory with the current image's `from_bytes::load3_at` and `load4_at`
where the image loads them, and zeros elsewhere. -/
def witnessMemFl : RV32.Word → BitVec 8 :=
  RV32.regionMem [(Image.feLoad3Address, Image.feLoad3Code), (Image.feLoad4Address, Image.feLoad4Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `from_bytes::load3_at` on index 0 of the bytes at
`0x3FCC6000` meets `feLoad3_correct`'s hypotheses. -/
theorem exists_feLoad3_machine :
    ∃ (m : RV32.Machine) (base retAddr q i : RV32.Word), RV32.CodeIn m.mem base Image.feLoad3Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = q ∧ RV32.reg m RV32.a1 = i ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.feLoad3Address, witnessMemFl⟩,
    BitVec.ofNat 32 Image.feLoad3Address, 0, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, by decide⟩
  code_in

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `from_bytes::load4_at` on index 0 of the bytes at
`0x3FCC6000` meets `feLoad4_correct`'s hypotheses. -/
theorem exists_feLoad4_machine :
    ∃ (m : RV32.Machine) (base retAddr q i : RV32.Word), RV32.CodeIn m.mem base Image.feLoad4Code ∧
      m.pc = base ∧ RV32.reg m RV32.a0 = q ∧ RV32.reg m RV32.a1 = i ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.feLoad4Address, witnessMemFl⟩,
    BitVec.ofNat 32 Image.feLoad4Address, 0, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, by decide⟩
  code_in

/-- Memory with the current image's `FieldElement2625::ct_eq` and the
functions it calls where the image loads them, and zeros elsewhere. -/
def witnessMemFeCtEq : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.feCtEqAddress, Image.feCtEqCode),
    (Image.feToBytesAddress, Image.feToBytesCode),
    (Image.feReduceAddress, Image.feReduceCode),
    (Image.ctEqSliceAddress, Image.ctEqSliceCode),
    (Image.ctEqU8Address, Image.ctEqU8Code),
    (Image.blackBoxU8Address, Image.blackBoxU8Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `FieldElement2625::ct_eq` on the field elements at
`0x3FCC6000` and `0x3FCC6100` with the stack at `0x3FCC8000` meets
`feCtEq_correct`'s hypotheses. -/
theorem exists_feCtEq_machine :
    ∃ (m : RV32.Machine) (P sp0 xp yp retAddr : RV32.Word), RV32.FCEEnv m.mem P sp0 xp yp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = xp ∧ RV32.reg m RV32.a1 = yp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC6100 0, BitVec.ofNat 32 Image.feCtEqAddress, witnessMemFeCtEq⟩,
    BitVec.ofNat 32 Image.feCtEqAddress, 0x3FCC8000, 0x3FCC6000, 0x3FCC6100, 0, ?_, rfl, rfl, rfl, rfl, rfl,
    by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `EdwardsPoint::as_projective_niels`, the
functions it calls, and `2d` where the image loads them, and zeros
elsewhere. -/
def witnessMemApn : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.asProjNielsAddress, Image.asProjNielsCode),
    (Image.feAddAddress, Image.feAddCode),
    (Image.feSubAddress, Image.feSubCode),
    (Image.feReduceAddress, Image.feReduceCode),
    (Image.feMulAddress, Image.feMulCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.edwardsD2Address, Image.edwardsD2Data)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `EdwardsPoint::as_projective_niels` on the point at
`0x3FCC6000` with the result at `0x3FCC6100` and the stack at `0x3FCC8000`
meets `asProjNiels_correct`'s hypotheses. -/
theorem exists_asProjNiels_machine :
    ∃ (m : RV32.Machine) (P sp0 out ip retAddr : RV32.Word), RV32.APNEnv m.mem P sp0 out ip ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ip ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6100 0x3FCC6000 0, BitVec.ofNat 32 Image.asProjNielsAddress, witnessMemApn⟩,
    BitVec.ofNat 32 Image.asProjNielsAddress, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl,
    by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `tsa::is_sha256`, the functions it
calls, and SHA-256's OID where the image loads them, a reader at
`0x3FCC6000` whose unread bytes start at `0x3FCC7000` and number zero, and
zeros elsewhere. -/
def witnessMemIsSha256 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.isSha256Address, Image.isSha256Code),
    (Image.derAlgorithmAddress, Image.derAlgorithmCode),
    (Image.derSequenceAddress, Image.derSequenceCode),
    (Image.derNestedAddress, Image.derNestedCode),
    (Image.derElementAddress, Image.derElementCode),
    (Image.derTlvAddress, Image.derTlvCode),
    (Image.derOidAddress, Image.derOidCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode),
    (Image.sliceEqAddress, Image.sliceEqCode),
    (Image.equalSameLengthAddress, Image.equalSameLengthCode),
    (Image.memcmpAddress, Image.memcmpCode),
    (Image.sha256OidAddress, Image.sha256OidData),
    (0x3FCC6008, [0x00, 0x70, 0xCC, 0x3F])]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `tsa::is_sha256` with the reader at `0x3FCC6000`
over no unread bytes at `0x3FCC7000` and the stack at `0x3FCC8000` meets
`isSha256_correct`'s hypotheses. -/
theorem exists_isSha256_machine :
    ∃ (m : RV32.Machine) (P sp0 d p retAddr : RV32.Word) (n : Nat), RV32.ISEnv m.mem P sp0 d p n ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = d ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.isSha256Address, witnessMemIsSha256⟩,
    BitVec.ofNat 32 Image.isSha256Address, 0x3FCC8000, 0x3FCC6000, 0x3FCC7000, 0, 0, ?_, rfl, rfl, rfl, rfl,
    by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel


/-- Memory with the current image's `EdwardsPoint ± ProjectiveNielsPoint`
and the field operations they call where the image loads them, and zeros
elsewhere. -/
def witnessMemEdNiels : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.edAddNielsAddress, Image.edAddNielsCode),
    (Image.edSubNielsAddress, Image.edSubNielsCode),
    (Image.feAddAddress, Image.feAddCode),
    (Image.feSubAddress, Image.feSubCode),
    (Image.feReduceAddress, Image.feReduceCode),
    (Image.feMulAddress, Image.feMulCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `EdwardsPoint + ProjectiveNielsPoint` on the points
at `0x3FCC6000` and `0x3FCC6200` with the result at `0x3FCC6100` and the
stack at `0x3FCC8000` meets `edAddNiels_correct`'s hypotheses. -/
theorem exists_edAddNiels_machine :
    ∃ (m : RV32.Machine) (P sp0 out ep np retAddr : RV32.Word), RV32.EANEnv m.mem P sp0 out ep np ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ep ∧
      RV32.reg m RV32.a2 = np ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6100 0x3FCC6000 0x3FCC6200, BitVec.ofNat 32 Image.edAddNielsAddress, witnessMemEdNiels⟩,
    BitVec.ofNat 32 Image.edAddNielsAddress, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0x3FCC6200, 0, ?_, rfl, rfl, rfl,
    rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | (constructor <;> exact RV32.sep_of_le (by decide) (by decide))
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `EdwardsPoint - ProjectiveNielsPoint` on the points
at `0x3FCC6000` and `0x3FCC6200` with the result at `0x3FCC6100` and the
stack at `0x3FCC8000` meets `edSubNiels_correct`'s hypotheses. -/
theorem exists_edSubNiels_machine :
    ∃ (m : RV32.Machine) (P sp0 out ep np retAddr : RV32.Word), RV32.ESNEnv m.mem P sp0 out ep np ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ep ∧
      RV32.reg m RV32.a2 = np ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6100 0x3FCC6000 0x3FCC6200, BitVec.ofNat 32 Image.edSubNielsAddress, witnessMemEdNiels⟩,
    BitVec.ofNat 32 Image.edSubNielsAddress, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0x3FCC6200, 0, ?_, rfl, rfl, rfl,
    rfl, rfl, rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | (constructor <;> exact RV32.sep_of_le (by decide) (by decide))
    | decide +kernel


/-- Memory with the current image's `FieldElement2625::pow22501` and the
field operations it calls where the image loads them, and zeros
elsewhere. -/
def witnessMemPow22501 : RV32.Word → BitVec 8 :=
  RV32.regionMem
    [(Image.pow22501Address, Image.pow22501Code),
    (Image.feSquareAddress, Image.feSquareCode),
    (Image.feSquareInnerAddress, Image.feSquareInnerCode),
    (Image.feReduceAddress, Image.feReduceCode),
    (Image.feMulAddress, Image.feMulCode),
    (Image.fePow2kAddress, Image.fePow2kCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `FieldElement2625::pow22501` on the field element at
`0x3FCC6000` with the result pair at `0x3FCC6100` and the stack at
`0x3FCC8000` meets `pow22501_correct`'s hypotheses. -/
theorem exists_pow22501_machine :
    ∃ (m : RV32.Machine) (P sp0 out xp retAddr : RV32.Word), RV32.PWEnv m.mem P sp0 out xp ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = xp ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6100 0x3FCC6000 0, BitVec.ofNat 32 Image.pow22501Address, witnessMemPow22501⟩,
    BitVec.ofNat 32 Image.pow22501Address, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl,
    by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | (constructor <;> exact RV32.sep_of_le (by decide) (by decide))
    | decide +kernel


/-- Memory with the current image's `FieldElement2625::conditional_assign`
where the image loads it, and zeros elsewhere. -/
def witnessMemFca : RV32.Word → BitVec 8 :=
  RV32.regionMem [(Image.feCondAssignAddress, Image.feCondAssignCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `FieldElement2625::conditional_assign` with `self` at
`0x3FCC6000`, `other` at `0x3FCC6100`, and `choice` 1 meets
`feCondAssign_correct`'s hypotheses. -/
theorem exists_feCondAssign_machine :
    ∃ (m : RV32.Machine) (P s o c retAddr : RV32.Word), RV32.CodeIn m.mem P Image.feCondAssignCode ∧
      m.pc = P ∧ RV32.reg m RV32.a0 = s ∧ RV32.reg m RV32.a1 = o ∧ RV32.reg m RV32.a2 = c ∧ (c = 0 ∨ c = 1) ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ s.toNat % 4 = 0 ∧ o.toNat % 4 = 0 ∧
      s.toNat + 40 < 2 ^ 32 ∧ RV32.Sep s 40 P Image.feCondAssignCode.length ∧ RV32.Sep s 40 o 40 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC6100 1, BitVec.ofNat 32 Image.feCondAssignAddress, witnessMemFca⟩,
    BitVec.ofNat 32 Image.feCondAssignAddress, 0x3FCC6000, 0x3FCC6100, 1, 0, ?_, rfl, rfl, rfl, rfl, .inr rfl, rfl,
    by decide, by decide, by decide, by decide, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `-&FieldElement2625` and `reduce` where
the image loads them, and zeros elsewhere. -/
def witnessMemFeNeg : RV32.Word → BitVec 8 :=
  RV32.regionMem [(Image.feNegAddress, Image.feNegCode), (Image.feReduceAddress, Image.feReduceCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `-&FieldElement2625` on the field element at
`0x3FCC6000` with the result at `0x3FCC6100` and the stack at `0x3FCC8000`
meets `feNeg_correct`'s hypotheses. -/
theorem exists_feNeg_machine :
    ∃ (m : RV32.Machine) (P sp0 out ip retAddr : RV32.Word), RV32.FNEnv m.mem P sp0 out ip ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ip ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6100 0x3FCC6000 0, BitVec.ofNat 32 Image.feNegAddress, witnessMemFeNeg⟩,
    BitVec.ofNat 32 Image.feNegAddress, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl,
    by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with the current image's `Scalar29::pack` where the image loads it,
and zeros elsewhere. -/
def witnessMemScalar29Pack : RV32.Word → BitVec 8 :=
  RV32.regionMem [(Image.scalar29PackAddress, Image.scalar29PackCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Scalar29::pack` on the limbs at `0x3FCC6000` with
the result at `0x3FCC6100` and the stack at `0x3FCC8000` meets
`scalar29Pack_correct`'s hypotheses. -/
theorem exists_scalar29Pack_machine :
    ∃ (m : RV32.Machine) (P sp0 out ap retAddr : RV32.Word), RV32.CodeIn m.mem P Image.scalar29PackCode ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = ap ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ sp0.toNat % 4 = 0 ∧ 0x20 ≤ sp0.toNat ∧
      ap.toNat % 4 = 0 ∧ RV32.Sep (sp0 + 0xFFFFFFE0) 0x20 P Image.scalar29PackCode.length ∧
      RV32.Sep out 32 P Image.scalar29PackCode.length ∧ RV32.Sep out 32 (sp0 + 0xFFFFFFE0) 0x20 ∧
      RV32.Sep ap 36 (sp0 + 0xFFFFFFE0) 0x20 ∧ RV32.Sep out 32 ap 36 := by
  refine ⟨⟨leafRegs 0x3FCC6100 0x3FCC6000 0, BitVec.ofNat 32 Image.scalar29PackAddress, witnessMemScalar29Pack⟩,
    BitVec.ofNat 32 Image.scalar29PackAddress, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm

/-- Memory with a `LimbBuffer` at `0x3FCC6000` over a 3-byte slice at
`0x3FCC6100`, and the current image's `LimbBuffer::increment_limb` and
`memcpy` where the image loads them, and zeros elsewhere. -/
def witnessMemIncrementLimb : RV32.Word → BitVec 8 :=
  RV32.regionMem [(0x3FCC6000, [0x00, 0x61, 0xCC, 0x3F, 3, 0, 0, 0]),
    (Image.incrementLimbAddress, Image.incrementLimbCode),
    (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `LimbBuffer::increment_limb` on the buffer at
`0x3FCC6000`, whose slice is 3 bytes, with the stack at `0x3FCC8000` meets
`incrementLimb_correct`'s hypotheses. -/
theorem exists_incrementLimb_machine :
    ∃ (m : RV32.Machine) (P sp0 s p n retAddr : RV32.Word), RV32.ILEnv m.mem P sp0 s p n ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = s ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.incrementLimbAddress, witnessMemIncrementLimb⟩,
    BitVec.ofNat 32 Image.incrementLimbAddress, 0x3FCC8000, 0x3FCC6000, 0x3FCC6100, 3, 0, ?_, rfl, rfl, rfl, rfl,
    by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

/-- Memory with a scalar at `0x3FCC6000`, and the current image's
`Scalar::non_adjacent_form`, `memset`, `__lshrdi3`, and `__ashldi3` where the
image loads them, and zeros elsewhere. -/
def witnessMemNaf : RV32.Word → BitVec 8 :=
  RV32.regionMem [(0x3FCC6000, [0x13, 0x00, 0x00, 0x00, 0xFF, 0x7F, 0x00, 0x00]),
    (Image.nonAdjacentFormAddress, Image.nonAdjacentFormCode),
    (Image.memsetAddress, Image.memsetCode),
    (Image.lshrdi3Address, Image.lshrdi3Code),
    (Image.ashldi3Address, Image.ashldi3Code)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Scalar::non_adjacent_form(5)` on the scalar at
`0x3FCC6000` with the result at `0x3FCC6100` and the stack at `0x3FCC8000`
meets `nonAdjacentForm_correct`'s hypotheses. -/
theorem exists_nonAdjacentForm_machine :
    ∃ (m : RV32.Machine) (P sp0 out s retAddr : RV32.Word), RV32.NAFEnv m.mem P sp0 out s ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = s ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6100 0x3FCC6000 0, BitVec.ofNat 32 Image.nonAdjacentFormAddress, witnessMemNaf⟩,
    BitVec.ofNat 32 Image.nonAdjacentFormAddress, 0x3FCC8000, 0x3FCC6100, 0x3FCC6000, 0, ?_, rfl, rfl, rfl, rfl,
    rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm

/-- Memory with the current image's `FieldElement2625::conditional_negate`,
`-&FieldElement2625`, `reduce`, and `conditional_assign` where the image loads
them, and zeros elsewhere. -/
def witnessMemFeCondNeg : RV32.Word → BitVec 8 :=
  RV32.regionMem [(Image.feCondNegAddress, Image.feCondNegCode), (Image.feNegAddress, Image.feNegCode),
    (Image.feReduceAddress, Image.feReduceCode), (Image.feCondAssignAddress, Image.feCondAssignCode)]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `FieldElement2625::conditional_negate` with choice 1
on the field element at `0x3FCC6000` and the stack at `0x3FCC8000` meets
`feCondNeg_correct`'s hypotheses. -/
theorem exists_feCondNeg_machine :
    ∃ (m : RV32.Machine) (P sp0 x c retAddr : RV32.Word), RV32.FCNEnv m.mem P sp0 x ∧
      m.pc = P ∧ RV32.reg m RV32.sp = sp0 ∧ RV32.reg m RV32.a0 = x ∧ RV32.reg m RV32.a1 = c ∧
      (c = 0 ∨ c = 1) ∧ RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr := by
  refine ⟨⟨leafRegs 0x3FCC6000 1 0, BitVec.ofNat 32 Image.feCondNegAddress, witnessMemFeCondNeg⟩,
    BitVec.ofNat 32 Image.feCondNegAddress, 0x3FCC8000, 0x3FCC6000, 1, 0, ?_, rfl, rfl, rfl, rfl, .inr rfl,
    rfl, by decide⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel


/-- Memory with the current image's panic code, the two `expect`s,
`NafLookupTable5::select`, the two `CtOption::unwrap`s, and `memcpy` where
the image loads them, and zeros elsewhere. -/
def witnessRegionsPanic : List (Nat × List Nat) :=
  RV32.panicFns ++ [(Image.expectUsizeAddress, Image.expectUsizeCode), (Image.expectTagAddress, Image.expectTagCode),
    (Image.nafSelectAddress, Image.nafSelectCode), (Image.ctUnwrap384Address, Image.ctUnwrap384Code),
    (Image.ctUnwrap256Address, Image.ctUnwrap256Code), (Image.memcpyStubAddress, Image.memcpyStubCode),
    (Image.memcpyBodyAddress, Image.memcpyBodyCode), (Image.tagFromU8Address, Image.tagFromU8Code),
    (Image.encodedPointTagAddress, Image.encodedPointTagCode),
    (Image.encodedPointIsIdentityAddress, Image.encodedPointIsIdentityCode)]

def witnessMemPanic : RV32.Word → BitVec 8 := RV32.regionMem witnessRegionsPanic

set_option maxRecDepth 200000 in
theorem witnessRegionsPanic_apart : RV32.regionsApart witnessRegionsPanic = true := by decide +kernel

theorem witnessMemPanic_code : RV32.PanicCode witnessMemPanic :=
  fun _ hp => RV32.regionMem_codeIn witnessRegionsPanic_apart (List.mem_append_left _ hp)

theorem room_witness : RV32.Room 0x3FCC8000 64 := ⟨by decide, by decide, by decide⟩

/-- For each panic entry point, a machine at it with 64 bytes of stack
meets the `_panics` theorems' hypotheses. -/
theorem exists_panic_machines : ∀ p ∈ RV32.panicFns, ∃ m : RV32.Machine,
    RV32.PanicCode m.mem ∧ m.pc = BitVec.ofNat 32 p.1 ∧ RV32.Room (RV32.reg m RV32.sp) 64 :=
  fun p _ => ⟨⟨leafRegs 0 0 0, BitVec.ofNat 32 p.1, witnessMemPanic⟩, witnessMemPanic_code, rfl, room_witness⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Result<usize, _>::expect` on `0x3FCC6000` meets
`expectUsize_correct`'s hypotheses. -/
theorem exists_expectUsize_machine :
    ∃ (m : RV32.Machine) (p retAddr : RV32.Word), RV32.PanicCode m.mem ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.expectUsizeAddress) Image.expectUsizeCode ∧
      m.pc = BitVec.ofNat 32 Image.expectUsizeAddress ∧ RV32.reg m RV32.a0 = p ∧ p.toNat % 4 = 0 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.Room (RV32.reg m RV32.sp) 48 :=
  ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.expectUsizeAddress, witnessMemPanic⟩, 0x3FCC6000, 0,
    witnessMemPanic_code, by code_in, rfl, rfl, by decide, rfl, by decide, ⟨by decide, by decide, by decide⟩⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `Result<Tag, _>::expect` on `0x3FCC6000` meets
`expectTag_correct`'s hypotheses. -/
theorem exists_expectTag_machine :
    ∃ (m : RV32.Machine) (p retAddr : RV32.Word), RV32.PanicCode m.mem ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.expectTagAddress) Image.expectTagCode ∧
      m.pc = BitVec.ofNat 32 Image.expectTagAddress ∧ RV32.reg m RV32.a0 = p ∧ p.toNat % 4 = 0 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.Room (RV32.reg m RV32.sp) 48 :=
  ⟨⟨leafRegs 0x3FCC6000 0 0, BitVec.ofNat 32 Image.expectTagAddress, witnessMemPanic⟩, 0x3FCC6000, 0,
    witnessMemPanic_code, by code_in, rfl, rfl, by decide, rfl, by decide, ⟨by decide, by decide, by decide⟩⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `EncodedPoint::tag` with the byte 4 and the stack at
`0x3FCC8000` meets `encodedPointTag_correct`'s hypotheses. -/
theorem exists_encodedPointTag_machine :
    ∃ (m : RV32.Machine) (retAddr : RV32.Word) (t : BitVec 8), RV32.PanicCode m.mem ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.encodedPointTagAddress) Image.encodedPointTagCode ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.tagFromU8Address) Image.tagFromU8Code ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.expectTagAddress) Image.expectTagCode ∧
      m.pc = BitVec.ofNat 32 Image.encodedPointTagAddress ∧ RV32.reg m RV32.a0 = t.zeroExtend 32 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.Room (RV32.reg m RV32.sp) 112 :=
  ⟨⟨leafRegs 4 0 0, BitVec.ofNat 32 Image.encodedPointTagAddress, witnessMemPanic⟩, 0, 4,
    witnessMemPanic_code, by code_in, by code_in, by code_in, rfl, by decide, rfl, by decide,
    ⟨by decide, by decide, by decide⟩⟩

/-- A machine that calls `EncodedPoint::is_identity` with the byte 0 and the
stack at `0x3FCC8000` meets `encodedPointIsIdentity_correct`'s hypotheses. -/
theorem exists_encodedPointIsIdentity_machine :
    ∃ (m : RV32.Machine) (retAddr : RV32.Word) (t : BitVec 8), RV32.PanicCode m.mem ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.encodedPointIsIdentityAddress) Image.encodedPointIsIdentityCode ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.encodedPointTagAddress) Image.encodedPointTagCode ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.tagFromU8Address) Image.tagFromU8Code ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.expectTagAddress) Image.expectTagCode ∧
      m.pc = BitVec.ofNat 32 Image.encodedPointIsIdentityAddress ∧ RV32.reg m RV32.a0 = t.zeroExtend 32 ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ RV32.Room (RV32.reg m RV32.sp) 128 :=
  ⟨⟨leafRegs 0 0 0, BitVec.ofNat 32 Image.encodedPointIsIdentityAddress, witnessMemPanic⟩, 0, 0,
    witnessMemPanic_code, by code_in, by code_in, by code_in, by code_in, rfl, by decide, rfl, by decide,
    ⟨by decide, by decide, by decide⟩⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `NafLookupTable5::select(3)` on the table at
`0x3FCC5000` with the result at `0x3FCC6000` meets `nafSelect_correct`'s
hypotheses, including `memcpy`'s for the copy. -/
theorem exists_nafSelect_machine :
    ∃ (m : RV32.Machine) (out tbl x retAddr : RV32.Word), RV32.PanicCode m.mem ∧
      RV32.CodeIn m.mem RV32.nslBase Image.nafSelectCode ∧ RV32.CodeIn m.mem RV32.stubBase Image.memcpyStubCode ∧
      m.pc = RV32.nslBase ∧ RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = tbl ∧ RV32.reg m RV32.a2 = x ∧
      RV32.reg m RV32.ra = retAddr ∧ retAddr &&& ~~~1 = retAddr ∧ x.toNat ≤ 15 ∧
      RV32.McEnv m.mem (RV32.stubBase + 8) out (tbl + BitVec.ofNat 32 (x.toNat / 2 * 160))
        (RV32.reg m RV32.sp + 0xFFFFFFF0) 160 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 3, RV32.nslBase, witnessMemPanic⟩, 0x3FCC6000, 0x3FCC5000, 3, 0,
    witnessMemPanic_code, by code_in, by code_in, rfl, rfl, rfl, rfl, rfl, by decide, by decide, ?_⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- A machine that calls `CtOption<NonZeroScalar<NistP384>>::unwrap` on the
option at `0x3FCC5000` with the result at `0x3FCC6000` meets
`ctUnwrap384_correct`'s hypotheses, including `memcpy`'s for the copy. -/
theorem exists_ctUnwrap384_machine :
    ∃ (m : RV32.Machine) (out s retAddr : RV32.Word), RV32.PanicCode m.mem ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.ctUnwrap384Address) Image.ctUnwrap384Code ∧
      RV32.CodeIn m.mem RV32.stubBase Image.memcpyStubCode ∧ m.pc = BitVec.ofNat 32 Image.ctUnwrap384Address ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = s ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.Room (RV32.reg m RV32.sp) 64 ∧
      RV32.McEnv m.mem (RV32.stubBase + 8) out s (RV32.reg m RV32.sp + 0xFFFFFFF0) 0x30 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 0, BitVec.ofNat 32 Image.ctUnwrap384Address, witnessMemPanic⟩,
    0x3FCC6000, 0x3FCC5000, 0, witnessMemPanic_code, by code_in, by code_in, rfl, rfl, rfl, rfl, by decide,
    room_witness, ?_⟩
  constructor
  all_goals first
    | code_in
    | decide
    | exact RV32.sep_of_le (by decide) (by decide)
    | exact (RV32.sep_of_le (by decide) (by decide)).symm
    | decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- The same for `CtOption<NonZeroScalar<NistP256>>::unwrap`. -/
theorem exists_ctUnwrap256_machine :
    ∃ (m : RV32.Machine) (out s retAddr : RV32.Word), RV32.PanicCode m.mem ∧
      RV32.CodeIn m.mem (BitVec.ofNat 32 Image.ctUnwrap256Address) Image.ctUnwrap256Code ∧
      RV32.CodeIn m.mem RV32.stubBase Image.memcpyStubCode ∧ m.pc = BitVec.ofNat 32 Image.ctUnwrap256Address ∧
      RV32.reg m RV32.a0 = out ∧ RV32.reg m RV32.a1 = s ∧ RV32.reg m RV32.ra = retAddr ∧
      retAddr &&& ~~~1 = retAddr ∧ RV32.Room (RV32.reg m RV32.sp) 64 ∧
      RV32.McEnv m.mem (RV32.stubBase + 8) out s (RV32.reg m RV32.sp + 0xFFFFFFF0) 0x20 := by
  refine ⟨⟨leafRegs 0x3FCC6000 0x3FCC5000 0, BitVec.ofNat 32 Image.ctUnwrap256Address, witnessMemPanic⟩,
    0x3FCC6000, 0x3FCC5000, 0, witnessMemPanic_code, by code_in, by code_in, rfl, rfl, rfl, rfl, by decide,
    room_witness, ?_⟩
  constructor
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

/-- info: 'C3.decodeManifestV1_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.decodeManifestV1_bytes

/-- info: 'C3.decodeManifestV1_parse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.decodeManifestV1_parse

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

/-- info: 'C3.RV32.zeroArray48_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.zeroArray48_correct

/-- info: 'C3.exists_zeroArray48_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_zeroArray48_machine

/-- info: 'C3.RV32.zeroArray64_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.zeroArray64_correct

/-- info: 'C3.exists_zeroArray64_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_zeroArray64_machine

/-- info: 'C3.RV32.toBeBytes12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.toBeBytes12_correct

/-- info: 'C3.exists_toBeBytes12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_toBeBytes12_machine

/-- info: 'C3.RV32.toBeBytes8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.toBeBytes8_correct

/-- info: 'C3.exists_toBeBytes8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_toBeBytes8_machine

/-- info: 'C3.RV32.p256FieldRetrieve_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p256FieldRetrieve_correct

/-- info: 'C3.exists_p256FieldRetrieve_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p256FieldRetrieve_machine

/-- info: 'C3.RV32.p384FromRepr_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384FromRepr_correct

/-- info: 'C3.exists_p384FromRepr_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384FromRepr_machine

/-- info: 'C3.RV32.p256FromRepr_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p256FromRepr_correct

/-- info: 'C3.exists_p256FromRepr_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p256FromRepr_machine

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

/-- info: 'C3.RV32.shaFinish_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.shaFinish_correct

/-- info: 'C3.exists_shaFinish_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_shaFinish_machine

/-- info: 'C3.RV32.pt_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pt_loop

/-- info: 'C3.RV32.sha256Parts_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sha256Parts_correct

/-- info: 'C3.exists_sha256Parts_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sha256Parts_machine

/-- info: 'C3.RV32.merkleNodeHash_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.merkleNodeHash_correct

/-- info: 'C3.exists_merkleNodeHash_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_merkleNodeHash_machine

/-- info: 'C3.RV32.rootFromInclusion_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.rootFromInclusion_correct

/-- info: 'C3.exists_rootFromInclusion_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_rootFromInclusion_machine

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

/-- info: 'C3.RV32.sha512FinBlock_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sha512FinBlock_correct

/-- info: 'C3.exists_sha512FinBlock_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sha512FinBlock_machine

/-- info: 'C3.RV32.sha384UpdateBlocks_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sha384UpdateBlocks_correct

/-- info: 'C3.exists_sha384UpdateBlocks_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sha384UpdateBlocks_machine

/-- info: 'C3.RV32.S5U.sha512Update_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.S5U.sha512Update_correct

/-- info: 'C3.RV32.S5U.upd_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.S5U.upd_join

/-- info: 'C3.exists_sha512Update_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sha512Update_machine

/-- info: 'C3.RV32.S5U.sha512UpdateArr32_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.S5U.sha512UpdateArr32_correct

/-- info: 'C3.exists_sha512UpdateArr32_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sha512UpdateArr32_machine

/-- info: 'C3.RV32.edDecompress_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.edDecompress_correct

/-- info: 'C3.exists_edDecompress_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_edDecompress_machine

/-- info: 'C3.RV32.edVkFromBytes_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.edVkFromBytes_correct

/-- info: 'C3.exists_edVkFromBytes_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_edVkFromBytes_machine

/-- info: 'C3.RV32.pkOk_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pkOk_correct

/-- info: 'C3.exists_pkOk_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_pkOk_machine

/-- info: 'C3.RV32.nafTable_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.nafTable_correct

/-- info: 'C3.exists_nafTable_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_nafTable_machine

/-- info: 'C3.RV32.wnafForm_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.wnafForm_correct

/-- info: 'C3.exists_wnafForm_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_wnafForm_machine

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

/-- info: 'C3.RV32.fieldSquare_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fieldSquare_correct

/-- info: 'C3.exists_fieldSquare_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fieldSquare_machine

/-- info: 'C3.RV32.p256PtDouble_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p256PtDouble_correct

/-- info: 'C3.exists_p256PtDouble_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p256PtDouble_machine

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

/-- info: 'C3.RV32.shr12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.shr12_correct

/-- info: 'C3.exists_shr12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_shr12_machine

/-- info: 'C3.RV32.lincomb12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lincomb12_correct

/-- info: 'C3.exists_lincomb12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lincomb12_machine

/-- info: 'C3.RV32.blackBoxU8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.blackBoxU8_correct

/-- info: 'C3.exists_blackBoxU8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_blackBoxU8_machine

/-- info: 'C3.RV32.lshrdi3_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lshrdi3_correct

/-- info: 'C3.exists_lshrdi3_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lshrdi3_machine

/-- info: 'C3.RV32.memcmp_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.memcmp_correct

/-- info: 'C3.exists_memcmp_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_memcmp_machine

/-- info: 'C3.RV32.uintRefIsNonzero_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uintRefIsNonzero_correct

/-- info: 'C3.exists_uintRefIsNonzero_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uintRefIsNonzero_machine

/-- info: 'C3.RV32.ctEqU8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ctEqU8_correct

/-- info: 'C3.exists_ctEqU8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ctEqU8_machine

/-- info: 'C3.RV32.ctEqSlice_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ctEqSlice_correct

/-- info: 'C3.exists_ctEqSlice_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ctEqSlice_machine

/-- info: 'C3.RV32.absSign2_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.absSign2_correct

/-- info: 'C3.exists_absSign2_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_absSign2_machine

/-- info: 'C3.RV32.fromI64_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fromI64_correct

/-- info: 'C3.exists_fromI64_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fromI64_machine

/-- info: 'C3.RV32.asProjective_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.asProjective_correct

/-- info: 'C3.exists_asProjective_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_asProjective_machine

/-- info: 'C3.RV32.asExtended_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.asExtended_correct

/-- info: 'C3.exists_asExtended_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_asExtended_machine

/-- info: 'C3.RV32.uint12IsNonzero_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uint12IsNonzero_correct

/-- info: 'C3.exists_uint12IsNonzero_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uint12IsNonzero_machine

/-- info: 'C3.RV32.p384Neg_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384Neg_correct

/-- info: 'C3.exists_p384Neg_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384Neg_machine

/-- info: 'C3.RV32.derTlv_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derTlv_correct

/-- info: 'C3.exists_derTlv_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derTlv_machine

/-- info: 'C3.RV32.derElement_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derElement_correct

/-- info: 'C3.exists_derElement_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derElement_machine

/-- info: 'C3.RV32.derOid_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derOid_correct

/-- info: 'C3.exists_derOid_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derOid_machine

/-- info: 'C3.RV32.derNested_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derNested_correct

/-- info: 'C3.exists_derNested_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derNested_machine

/-- info: 'C3.RV32.derSequence_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derSequence_correct

/-- info: 'C3.exists_derSequence_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derSequence_machine

/-- info: 'C3.RV32.equalSameLength_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.equalSameLength_correct

/-- info: 'C3.exists_equalSameLength_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_equalSameLength_machine

/-- info: 'C3.RV32.sliceEq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sliceEq_correct

/-- info: 'C3.exists_sliceEq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sliceEq_machine

/-- info: 'C3.RV32.shr8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.shr8_correct

/-- info: 'C3.exists_shr8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_shr8_machine

/-- info: 'C3.RV32.feToBytes_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feToBytes_correct

/-- info: 'C3.exists_feToBytes_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feToBytes_machine

/-- info: 'C3.RV32.scalar29Sub_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalar29Sub_correct

/-- info: 'C3.RV32.scalar29Index_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalar29Index_correct

/-- info: 'C3.RV32.scalar29IndexMut_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalar29IndexMut_correct

/-- info: 'C3.exists_scalar29Sub_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_scalar29Sub_machine

/-- info: 'C3.RV32.scalar29MontMul_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalar29MontMul_correct

/-- info: 'C3.exists_scalar29MontMul_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_scalar29MontMul_machine

/-- info: 'C3.RV32.p256ScalarMul_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p256ScalarMul_correct

/-- info: 'C3.exists_p256ScalarMul_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p256ScalarMul_machine

/-- info: 'C3.RV32.lincombShift12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lincombShift12_correct

/-- info: 'C3.exists_lincombShift12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lincombShift12_machine

/-- info: 'C3.RV32.lincombShift8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lincombShift8_correct

/-- info: 'C3.exists_lincombShift8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lincombShift8_machine

/-- info: 'C3.RV32.lowest12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lowest12_correct

/-- info: 'C3.exists_lowest12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lowest12_machine

/-- info: 'C3.RV32.lowest8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lowest8_correct

/-- info: 'C3.exists_lowest8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lowest8_machine

/-- info: 'C3.RV32.updateFg12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.updateFg12_correct

/-- info: 'C3.exists_updateFg12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_updateFg12_machine

/-- info: 'C3.RV32.updateFg8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.updateFg8_correct

/-- info: 'C3.exists_updateFg8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_updateFg8_machine

/-- info: 'C3.RV32.lincomb8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lincomb8_correct

/-- info: 'C3.exists_lincomb8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lincomb8_machine

/-- info: 'C3.RV32.mulMont8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.mulMont8_correct

/-- info: 'C3.exists_mulMont8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_mulMont8_machine

/-- info: 'C3.RV32.norm12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.norm12_correct

/-- info: 'C3.exists_norm12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_norm12_machine

/-- info: 'C3.RV32.uint8IsNonzero_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uint8IsNonzero_correct

/-- info: 'C3.exists_uint8IsNonzero_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uint8IsNonzero_machine

/-- info: 'C3.RV32.norm8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.norm8_correct

/-- info: 'C3.exists_norm8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_norm8_machine

/-- info: 'C3.RV32.toUintResize2_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.toUintResize2_correct

/-- info: 'C3.exists_toUintResize2_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_toUintResize2_machine

/-- info: 'C3.RV32.lincombShiftMod12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lincombShiftMod12_correct

/-- info: 'C3.exists_lincombShiftMod12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lincombShiftMod12_machine

/-- info: 'C3.RV32.updateDe12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.updateDe12_correct

/-- info: 'C3.exists_updateDe12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_updateDe12_machine

/-- info: 'C3.RV32.lincombShiftMod8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lincombShiftMod8_correct

/-- info: 'C3.exists_lincombShiftMod8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lincombShiftMod8_machine

/-- info: 'C3.RV32.updateDe8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.updateDe8_correct

/-- info: 'C3.exists_updateDe8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_updateDe8_machine

/-- info: 'C3.RV32.derSet_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derSet_correct

/-- info: 'C3.exists_derSet_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derSet_machine

/-- info: 'C3.RV32.derOctetString_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derOctetString_correct

/-- info: 'C3.exists_derOctetString_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derOctetString_machine

/-- info: 'C3.RV32.derBitString_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derBitString_correct

/-- info: 'C3.exists_derBitString_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derBitString_machine

/-- info: 'C3.RV32.derInteger_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derInteger_correct

/-- info: 'C3.exists_derInteger_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derInteger_machine

/-- info: 'C3.RV32.derBooleanTrue_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derBooleanTrue_correct

/-- info: 'C3.exists_derBooleanTrue_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derBooleanTrue_machine

/-- info: 'C3.RV32.derOptional_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derOptional_correct

/-- info: 'C3.exists_derOptional_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derOptional_machine

/-- info: 'C3.RV32.uint12Eq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uint12Eq_correct

/-- info: 'C3.exists_uint12Eq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uint12Eq_machine

/-- info: 'C3.RV32.uint8Eq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uint8Eq_correct

/-- info: 'C3.exists_uint8Eq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uint8Eq_machine

/-- info: 'C3.RV32.lessThanLe_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lessThanLe_correct

/-- info: 'C3.exists_lessThanLe_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_lessThanLe_machine

/-- info: 'C3.RV32.inScalarRange_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.inScalarRange_correct

/-- info: 'C3.exists_inScalarRange_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_inScalarRange_machine

/-- info: 'C3.RV32.p384ScalarMul_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384ScalarMul_correct

/-- info: 'C3.exists_p384ScalarMul_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384ScalarMul_machine

/-- info: 'C3.RV32.p384ScalarNew_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384ScalarNew_correct

/-- info: 'C3.exists_p384ScalarNew_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384ScalarNew_machine

/-- info: 'C3.RV32.u32Min_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.u32Min_correct

/-- info: 'C3.exists_u32Min_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_u32Min_machine

/-- info: 'C3.RV32.sliceReverse_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sliceReverse_correct

/-- info: 'C3.exists_sliceReverse_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sliceReverse_machine

/-- info: 'C3.RV32.splitAt12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.splitAt12_correct

/-- info: 'C3.exists_splitAt12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_splitAt12_machine

/-- info: 'C3.RV32.choiceNot_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.choiceNot_correct

/-- info: 'C3.exists_choiceNot_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_choiceNot_machine

/-- info: 'C3.RV32.uintRefIsZero_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uintRefIsZero_correct

/-- info: 'C3.exists_uintRefIsZero_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uintRefIsZero_machine

/-- info: 'C3.RV32.limbCtEq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.limbCtEq_correct

/-- info: 'C3.exists_limbCtEq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_limbCtEq_machine

/-- info: 'C3.RV32.uint12CtEq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uint12CtEq_correct

/-- info: 'C3.exists_uint12CtEq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uint12CtEq_machine

/-- info: 'C3.RV32.montRetrieve12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.montRetrieve12_correct

/-- info: 'C3.exists_montRetrieve12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_montRetrieve12_machine

/-- info: 'C3.RV32.p384FieldRetrieve_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p384FieldRetrieve_correct

/-- info: 'C3.exists_p384FieldRetrieve_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p384FieldRetrieve_machine

/-- info: 'C3.RV32.sliceCtAssign_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sliceCtAssign_correct

/-- info: 'C3.exists_sliceCtAssign_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sliceCtAssign_machine

/-- info: 'C3.RV32.uint12CtAssign_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uint12CtAssign_correct

/-- info: 'C3.exists_uint12CtAssign_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uint12CtAssign_machine

/-- info: 'C3.RV32.copyFromSliceU8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.copyFromSliceU8_correct

/-- info: 'C3.exists_copyFromSliceU8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_copyFromSliceU8_machine

/-- info: 'C3.RV32.zipSkipNext_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.zipSkipNext_correct

/-- info: 'C3.exists_zipSkipNext_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_zipSkipNext_machine

/-- info: 'C3.RV32.derScalar48_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derScalar48_correct

/-- info: 'C3.exists_derScalar48_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derScalar48_machine

/-- info: 'C3.RV32.derScalar32_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derScalar32_correct

/-- info: 'C3.exists_derScalar32_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derScalar32_machine

/-- info: 'C3.RV32.ecdsaSignature48_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ecdsaSignature48_correct

/-- info: 'C3.exists_ecdsaSignature48_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ecdsaSignature48_machine

/-- info: 'C3.RV32.derIntegerIs_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derIntegerIs_correct

/-- info: 'C3.exists_derIntegerIs_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derIntegerIs_machine

/-- info: 'C3.RV32.checkpointLine_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.checkpointLine_correct

/-- info: 'C3.exists_checkpointLine_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_checkpointLine_machine

/-- info: 'C3.RV32.tagMessageLen_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tagMessageLen_correct

/-- info: 'C3.exists_tagMessageLen_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_tagMessageLen_machine

/-- info: 'C3.RV32.tagFromU8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tagFromU8_correct

/-- info: 'C3.exists_tagFromU8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_tagFromU8_machine

/-- info: 'C3.RV32.timeDigits2_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.timeDigits2_correct

/-- info: 'C3.exists_timeDigits2_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_timeDigits2_machine

/-- info: 'C3.RV32.timeDigits4_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.timeDigits4_correct

/-- info: 'C3.exists_timeDigits4_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_timeDigits4_machine

/-- info: 'C3.RV32.allAsciiDigit_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.allAsciiDigit_correct

/-- info: 'C3.exists_allAsciiDigit_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_allAsciiDigit_machine

/-- info: 'C3.RV32.derPositiveInteger_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derPositiveInteger_correct

/-- info: 'C3.exists_derPositiveInteger_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derPositiveInteger_machine

/-- info: 'C3.RV32.p256FieldNeg_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p256FieldNeg_correct

/-- info: 'C3.exists_p256FieldNeg_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p256FieldNeg_machine

/-- info: 'C3.RV32.scalarIsZero384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalarIsZero384_correct

/-- info: 'C3.exists_scalarIsZero384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_scalarIsZero384_machine

/-- info: 'C3.RV32.scalarIsZero256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalarIsZero256_correct

/-- info: 'C3.exists_scalarIsZero256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_scalarIsZero256_machine

/-- info: 'C3.RV32.arr32Eq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.arr32Eq_correct

/-- info: 'C3.exists_arr32Eq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_arr32Eq_machine

/-- info: 'C3.RV32.arr32Ne_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.arr32Ne_correct

/-- info: 'C3.exists_arr32Ne_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_arr32Ne_machine

/-- info: 'C3.RV32.sliceNe_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sliceNe_correct

/-- info: 'C3.exists_sliceNe_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_sliceNe_machine

/-- info: 'C3.RV32.choiceCtEq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.choiceCtEq_correct

/-- info: 'C3.exists_choiceCtEq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_choiceCtEq_machine

/-- info: 'C3.RV32.montyScalarCtEq384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.montyScalarCtEq384_correct

/-- info: 'C3.exists_montyScalarCtEq384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_montyScalarCtEq384_machine

/-- info: 'C3.RV32.splitAt8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.splitAt8_correct

/-- info: 'C3.exists_splitAt8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_splitAt8_machine

/-- info: 'C3.RV32.tagAndThen_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tagAndThen_correct

/-- info: 'C3.exists_tagAndThen_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_tagAndThen_machine

/-- info: 'C3.RV32.condSelect384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.condSelect384_correct

/-- info: 'C3.exists_condSelect384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_condSelect384_machine

/-- info: 'C3.RV32.condSelect256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.condSelect256_correct

/-- info: 'C3.exists_condSelect256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_condSelect256_machine

/-- info: 'C3.RV32.unwrapOr384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.unwrapOr384_correct

/-- info: 'C3.exists_unwrapOr384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_unwrapOr384_machine

/-- info: 'C3.RV32.ctIntoAffine384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ctIntoAffine384_correct

/-- info: 'C3.exists_ctIntoAffine384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ctIntoAffine384_machine

/-- info: 'C3.RV32.ctIntoAffine256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ctIntoAffine256_correct

/-- info: 'C3.exists_ctIntoAffine256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ctIntoAffine256_machine

/-- info: 'C3.RV32.unwrapOr256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.unwrapOr256_correct

/-- info: 'C3.exists_unwrapOr256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_unwrapOr256_machine

/-- info: 'C3.RV32.ctMap384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ctMap384_correct

/-- info: 'C3.exists_ctMap384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ctMap384_machine

/-- info: 'C3.RV32.ctMap256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ctMap256_correct

/-- info: 'C3.exists_ctMap256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ctMap256_machine

/-- info: 'C3.RV32.uint8CtEq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.uint8CtEq_correct

/-- info: 'C3.exists_uint8CtEq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_uint8CtEq_machine

/-- info: 'C3.RV32.p256ScalarCtEq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.p256ScalarCtEq_correct

/-- info: 'C3.exists_p256ScalarCtEq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_p256ScalarCtEq_machine

/-- info: 'C3.RV32.nonZero384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.nonZero384_correct

/-- info: 'C3.exists_nonZero384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_nonZero384_machine

/-- info: 'C3.RV32.nonZero256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.nonZero256_correct

/-- info: 'C3.exists_nonZero256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_nonZero256_machine

/-- info: 'C3.RV32.arr32EqCrypto_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.arr32EqCrypto_correct

/-- info: 'C3.exists_arr32EqCrypto_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_arr32EqCrypto_machine

/-- info: 'C3.RV32.feIsNegative_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feIsNegative_correct

/-- info: 'C3.exists_feIsNegative_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feIsNegative_machine

/-- info: 'C3.RV32.ashldi3_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ashldi3_correct

/-- info: 'C3.exists_ashldi3_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ashldi3_machine

/-- info: 'C3.RV32.derAlgorithm_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derAlgorithm_correct

/-- info: 'C3.exists_derAlgorithm_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_derAlgorithm_machine

/-- info: 'C3.RV32.listsOid_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.listsOid_correct

/-- info: 'C3.exists_listsOid_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_listsOid_machine

/-- info: 'C3.RV32.leadingZeros_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.leadingZeros_correct

/-- info: 'C3.exists_leadingZeros_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_leadingZeros_machine

/-- info: 'C3.RV32.feLoad3_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feLoad3_correct

/-- info: 'C3.exists_feLoad3_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feLoad3_machine

/-- info: 'C3.RV32.feLoad4_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feLoad4_correct

/-- info: 'C3.exists_feLoad4_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feLoad4_machine

/-- info: 'C3.RV32.feCtEq_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feCtEq_correct

/-- info: 'C3.exists_feCtEq_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feCtEq_machine

/-- info: 'C3.RV32.asProjNiels_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.asProjNiels_correct

/-- info: 'C3.exists_asProjNiels_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_asProjNiels_machine

/-- info: 'C3.RV32.isSha256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.isSha256_correct

/-- info: 'C3.exists_isSha256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_isSha256_machine

/-- info: 'C3.RV32.edAddNiels_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.edAddNiels_correct

/-- info: 'C3.exists_edAddNiels_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_edAddNiels_machine

/-- info: 'C3.RV32.edSubNiels_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.edSubNiels_correct

/-- info: 'C3.exists_edSubNiels_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_edSubNiels_machine

/-- info: 'C3.RV32.pow22501_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pow22501_correct

/-- info: 'C3.exists_pow22501_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_pow22501_machine

/-- info: 'C3.RV32.feCondAssign_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feCondAssign_correct

/-- info: 'C3.exists_feCondAssign_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feCondAssign_machine

/-- info: 'C3.RV32.feNeg_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feNeg_correct

/-- info: 'C3.exists_feNeg_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feNeg_machine

/-- info: 'C3.RV32.scalar29Pack_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalar29Pack_correct

/-- info: 'C3.exists_scalar29Pack_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_scalar29Pack_machine

/-- info: 'C3.RV32.incrementLimb_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.incrementLimb_correct

/-- info: 'C3.exists_incrementLimb_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_incrementLimb_machine

/-- info: 'C3.RV32.nonAdjacentForm_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.nonAdjacentForm_correct

/-- info: 'C3.exists_nonAdjacentForm_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_nonAdjacentForm_machine

/-- info: 'C3.RV32.feCondNeg_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feCondNeg_correct

/-- info: 'C3.exists_feCondNeg_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_feCondNeg_machine

/-- info: 'C3.RV32.haltLoop_stays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.haltLoop_stays

/-- info: 'C3.RV32.halt_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.halt_panics

/-- info: 'C3.RV32.beginUnwind_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.beginUnwind_panics

/-- info: 'C3.RV32.panicFmt_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.panicFmt_panics

/-- info: 'C3.RV32.assertFailedInner_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.assertFailedInner_panics

/-- info: 'C3.RV32.corePanic_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.corePanic_panics

/-- info: 'C3.RV32.panicBoundsCheck_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.panicBoundsCheck_panics

/-- info: 'C3.RV32.expectFailed_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.expectFailed_panics

/-- info: 'C3.RV32.unwrapFailed_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.unwrapFailed_panics

/-- info: 'C3.RV32.lenMismatchFail_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lenMismatchFail_panics

/-- info: 'C3.RV32.sliceIndexFail_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sliceIndexFail_panics

/-- info: 'C3.RV32.assertFailedUsize_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.assertFailedUsize_panics

/-- info: 'C3.RV32.assertFailedU8_panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.assertFailedU8_panics

/-- info: 'C3.RV32.expectUsize_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.expectUsize_correct

/-- info: 'C3.RV32.expectTag_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.expectTag_correct

/-- info: 'C3.exists_panic_machines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_panic_machines

/-- info: 'C3.exists_expectUsize_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_expectUsize_machine

/-- info: 'C3.exists_expectTag_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_expectTag_machine

/-- info: 'C3.RV32.encodedPointTag_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.encodedPointTag_correct

/-- info: 'C3.exists_encodedPointTag_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_encodedPointTag_machine

/-- info: 'C3.RV32.encodedPointIsIdentity_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.encodedPointIsIdentity_correct

/-- info: 'C3.exists_encodedPointIsIdentity_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_encodedPointIsIdentity_machine

/-- info: 'C3.RV32.nafSelect_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.nafSelect_correct

/-- info: 'C3.exists_nafSelect_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_nafSelect_machine

/-- info: 'C3.RV32.ctUnwrap384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ctUnwrap384_correct

/-- info: 'C3.exists_ctUnwrap384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ctUnwrap384_machine

/-- info: 'C3.RV32.ctUnwrap256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ctUnwrap256_correct

/-- info: 'C3.exists_ctUnwrap256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_ctUnwrap256_machine

/-- info: 'C3.RV32.fillLimbs_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fillLimbs_correct

/-- info: 'C3.exists_fillLimbs_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fillLimbs_machine

/-- info: 'C3.RV32.fl_accV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fl_accV

/-- info: 'C3.RV32.fromBeSliceTrunc12_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fromBeSliceTrunc12_correct

/-- info: 'C3.exists_fromBeSliceTrunc12_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fromBeSliceTrunc12_machine

/-- info: 'C3.RV32.fromBeSliceTrunc8_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fromBeSliceTrunc8_correct

/-- info: 'C3.exists_fromBeSliceTrunc8_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_fromBeSliceTrunc8_machine

/-- info: 'C3.RV32.bytes2scalar384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bytes2scalar384_correct

/-- info: 'C3.exists_bytes2scalar384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_bytes2scalar384_machine

/-- info: 'C3.RV32.bytes2scalar256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bytes2scalar256_correct

/-- info: 'C3.exists_bytes2scalar256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_bytes2scalar256_machine

/-- info: 'C3.RV32.bz_sub_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bz_sub_loop

/-- info: 'C3.RV32.bz_copy_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bz_copy_loop

/-- info: 'C3.RV32.by_sub_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.by_sub_loop

/-- info: 'C3.RV32.by_copy_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.by_copy_loop

/-- info: 'C3.RV32.scalarFromSlice384_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalarFromSlice384_correct

/-- info: 'C3.exists_scalarFromSlice384_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_scalarFromSlice384_machine

/-- info: 'C3.RV32.scalarFromSlice256_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.scalarFromSlice256_correct

/-- info: 'C3.exists_scalarFromSlice256_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_scalarFromSlice256_machine

/-- info: 'C3.RV32.cmp_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.cmp_step

/-- info: 'C3.RV32.bf_cmp_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bf_cmp_loop

/-- info: 'C3.RV32.bg_cmp_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bg_cmp_loop

/-- info: 'C3.RV32.isSmallOrder_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.isSmallOrder_correct

/-- info: 'C3.exists_isSmallOrder_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_isSmallOrder_machine

/-- info: 'C3.RV32.St.callEdDouble' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.St.callEdDouble

/-- info: 'C3.RV32.St.callAsProj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.St.callAsProj

/-- info: 'C3.RV32.St.callAsExt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.St.callAsExt

/-- info: 'C3.RV32.St.callFeMulL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.St.callFeMulL

/-- info: 'C3.RV32.St.callFeCtEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.St.callFeCtEq

/-- info: 'C3.RV32.feBytesOf_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.feBytesOf_eq

/-- info: 'C3.RV32.dateTime_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.dateTime_correct

/-- info: 'C3.RV32.dt_arith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.dt_arith

/-- info: 'C3.RV32.generalizedTime_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.generalizedTime_correct

/-- info: 'C3.RV32.gtTail_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.gtTail_mem

/-- info: 'C3.exists_generalizedTime_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_generalizedTime_machine

/-- info: 'C3.RV32.x509ReadTime_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.x509ReadTime_correct

/-- info: 'C3.RV32.xrt_errByte_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.xrt_errByte_lt

/-- info: 'C3.RV32.derTlvMem_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.derTlvMem_ok

/-- info: 'C3.RV32.readTime_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readTime_ok

/-- info: 'C3.exists_x509ReadTime_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_x509ReadTime_machine

/-- info: 'C3.RV32.timeRfc3339_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.timeRfc3339_correct

/-- info: 'C3.RV32.rfc3339_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.rfc3339_eq

/-- info: 'C3.RV32.rfcRest_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.rfcRest_mem

/-- info: 'C3.RV32.rfcTail_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.rfcTail_mem

/-- info: 'C3.exists_timeRfc3339_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_timeRfc3339_machine

/-- info: 'C3.RV32.Cur.manifestParse_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.manifestParse_correct

/-- info: 'C3.decodeManifest_parse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.decodeManifest_parse

/-- info: 'C3.RV32.Cur.manifestParse_decodes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.manifestParse_decodes

/-- info: 'C3.exists_manifestParseCur_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_manifestParseCur_machine

/-- info: 'C3.RV32.dt_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.dt_check

/-- info: 'C3.RV32.digits2Mem_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.digits2Mem_cases

/-- info: 'C3.RV32.readDigits2_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readDigits2_mem

/-- info: 'C3.RV32.base64DecodeInto_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.base64DecodeInto_correct

/-- info: 'C3.exists_base64DecodeInto_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_base64DecodeInto_machine

/-- info: 'C3.RV32.bdi_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bdi_loop

/-- info: 'C3.RV32.bdi_group' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bdi_group

/-- info: 'C3.RV32.bdi_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bdi_copy

/-- info: 'C3.RV32.bdi_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bdi_bytes

/-- info: 'C3.RV32.bdi_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bdi_fold

/-- info: 'C3.RV32.bdi_pad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bdi_pad

/-- info: 'C3.b64_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.b64_cons

/-- info: 'C3.b64Group_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.b64Group_fold

/-- info: 'C3.b64_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.b64_len

/-- info: 'C3.RV32.base64EncodeTo_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.base64EncodeTo_correct

/-- info: 'C3.exists_base64EncodeTo_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_base64EncodeTo_machine

/-- info: 'C3.RV32.bee_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bee_loop

/-- info: 'C3.RV32.bee_group' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bee_group

/-- info: 'C3.RV32.bee_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bee_tail

/-- info: 'C3.RV32.bee_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bee_call

/-- info: 'C3.base64Encode_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.base64Encode_append

/-- info: 'C3.RV32.ev_len' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.ev_len

/-- info: 'C3.RV32.EvSt.hiM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.hiM

/-- info: 'C3.RV32.EvSt.roM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.roM

/-- info: 'C3.RV32.EvSt.feRo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.feRo

/-- info: 'C3.RV32.EvSt.bytesRo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.bytesRo

/-- info: 'C3.RV32.EvSt.bytesOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.bytesOut

/-- info: 'C3.RV32.EvSt.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.code

/-- info: 'C3.RV32.EvSt.codeRo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.codeRo

/-- info: 'C3.RV32.EvSt.pkEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.pkEnv

/-- info: 'C3.RV32.EvSt.jmp' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.EvSt.jmp

/-- info: 'C3.RV32.EvSt.regs' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.EvSt.regs

/-- info: 'C3.RV32.EvSt.ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.ret

/-- info: 'C3.RV32.EvSt.store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.store

/-- info: 'C3.RV32.EvSt.block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.block

/-- info: 'C3.RV32.EvSt.sw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.sw

/-- info: 'C3.RV32.EvSt.br0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.br0

/-- info: 'C3.RV32.EvSt.slotW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.slotW

/-- info: 'C3.RV32.ev_pro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_pro

/-- info: 'C3.RV32.ev_fin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_fin

/-- info: 'C3.RV32.ev_pkStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_pkStep

/-- info: 'C3.RV32.ev_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_lt

/-- info: 'C3.RV32.ev_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_chk

/-- info: 'C3.RV32.ev_vk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_vk

/-- info: 'C3.RV32.ev_cp1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_cp1

/-- info: 'C3.RV32.ev_cp2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_cp2

/-- info: 'C3.RV32.ev_cp3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_cp3

/-- info: 'C3.RV32.ev_inner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_inner

/-- info: 'C3.RV32.ev_outer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_outer

/-- info: 'C3.RV32.ev_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_loop

/-- info: 'C3.RV32.ev_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_words

/-- info: 'C3.RV32.ev_flag_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_flag_and

/-- info: 'C3.RV32.ev_mask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_mask

/-- info: 'C3.RV32.ev_red' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_red

/-- info: 'C3.RV32.ev_canon' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_canon

/-- info: 'C3.RV32.ev_rcp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_rcp

/-- info: 'C3.RV32.ev_rchk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_rchk

/-- info: 'C3.RV32.EvSt.sb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.sb

/-- info: 'C3.RV32.ev_h1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_h1

/-- info: 'C3.RV32.ev_h2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_h2

/-- info: 'C3.RV32.ev_h3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_h3

/-- info: 'C3.RV32.ev_a3' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.ev_a3

/-- info: 'C3.RV32.ev_flen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_flen

/-- info: 'C3.RV32.ev_fpad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_fpad

/-- info: 'C3.RV32.ev_fend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_fend

/-- info: 'C3.RV32.ev_rd_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_rd_body

/-- info: 'C3.RV32.ev_rd_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_rd_loop

/-- info: 'C3.RV32.ev_rd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_rd

/-- info: 'C3.RV32.ev_final' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_final

/-- info: 'C3.RV32.ev_hash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_hash

/-- info: 'C3.RV32.ev_inner16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_inner16

/-- info: 'C3.RV32.ev_outer16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_outer16

/-- info: 'C3.RV32.ev_loop16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_loop16

/-- info: 'C3.RV32.ev_words16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_words16

/-- info: 'C3.RV32.ev_dw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_dw

/-- info: 'C3.RV32.EvSt.blockW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.blockW

/-- info: 'C3.RV32.ev_fbw1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_fbw1

/-- info: 'C3.RV32.ev_fbw2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_fbw2

/-- info: 'C3.RV32.ev_mm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_mm

/-- info: 'C3.RV32.ev_add_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_add_body

/-- info: 'C3.RV32.ev_add_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_add_loop

/-- info: 'C3.RV32.ev_s29add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_s29add

/-- info: 'C3.RV32.ev_kpack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_kpack

/-- info: 'C3.RV32.ev_srch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_srch

/-- info: 'C3.RV32.ev_p6a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_p6a

/-- info: 'C3.RV32.ev_p6c' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_p6c

/-- info: 'C3.RV32.ev_p6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_p6

/-- info: 'C3.RV32.ev_digA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_digA

/-- info: 'C3.RV32.ev_digB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_digB

/-- info: 'C3.RV32.nafGo_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.nafGo_range

/-- info: 'C3.RV32.nafSpec_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.nafSpec_range

/-- info: 'C3.RV32.ev_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_body

/-- info: 'C3.RV32.ev_ladder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_ladder

/-- info: 'C3.RV32.ev_p8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_p8

/-- info: 'C3.RV32.ev_ra' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.ev_ra

/-- info: 'C3.RV32.EvSt.pkSpec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.pkSpec

/-- info: 'C3.RV32.EvSt.pkOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.pkOk

/-- info: 'C3.RV32.EvSt.ltLe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.ltLe

/-- info: 'C3.RV32.EvSt.memcpy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.memcpy

/-- info: 'C3.RV32.EvSt.memset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.memset

/-- info: 'C3.RV32.EvSt.ctEqU8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.ctEqU8

/-- info: 'C3.RV32.EvSt.vkFromBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.vkFromBytes

/-- info: 'C3.RV32.EvSt.s29sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.s29sub

/-- info: 'C3.RV32.EvSt.s29pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.s29pack

/-- info: 'C3.RV32.EvSt.ctEqSlice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.ctEqSlice

/-- info: 'C3.RV32.EvSt.blackBox' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.blackBox

/-- info: 'C3.RV32.EvSt.decompress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.decompress

/-- info: 'C3.RV32.EvSt.iso' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.iso

/-- info: 'C3.RV32.EvSt.updEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.updEnv

/-- info: 'C3.RV32.EvSt.upd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.upd

/-- info: 'C3.RV32.EvSt.upd32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.upd32

/-- info: 'C3.RV32.EvSt.finBlock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.finBlock

/-- info: 'C3.RV32.EvSt.zero64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.zero64

/-- info: 'C3.RV32.EvSt.montMul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.montMul

/-- info: 'C3.RV32.EvSt.idx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.idx

/-- info: 'C3.RV32.EvSt.idxm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.idxm

/-- info: 'C3.RV32.EvSt.feNeg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.feNeg

/-- info: 'C3.RV32.EvSt.naf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.naf

/-- info: 'C3.RV32.EvSt.nafTbl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.nafTbl

/-- info: 'C3.RV32.EvSt.dbl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.dbl

/-- info: 'C3.RV32.EvSt.ax' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.ax

/-- info: 'C3.RV32.EvSt.ap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.ap

/-- info: 'C3.RV32.EvSt.ean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.ean

/-- info: 'C3.RV32.EvSt.esn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.esn

/-- info: 'C3.RV32.EvSt.nsel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.nsel

/-- info: 'C3.RV32.EvSt.feMul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.feMul

/-- info: 'C3.RV32.EvSt.feSq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.feSq

/-- info: 'C3.RV32.EvSt.pow22501' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.pow22501

/-- info: 'C3.RV32.EvSt.pow2k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.pow2k

/-- info: 'C3.RV32.EvSt.toBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.toBytes

/-- info: 'C3.RV32.EvSt.isNeg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EvSt.isNeg

/-- info: 'C3.RV32.ev_stageA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_stageA

/-- info: 'C3.RV32.ev_stageB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_stageB

/-- info: 'C3.RV32.ev_stageC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ev_stageC

/-- info: 'C3.RV32.ed25519Verify_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ed25519Verify_correct

/-- info: 'C3.RV32.exists_ed25519Verify_machine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.exists_ed25519Verify_machine

/-- info: 'C3.RV32.nafScalar_leL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.nafScalar_leL

/-- info: 'C3.RV32.evPackS_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.evPackS_congr

/-- info: 'C3.RV32.leAcc_leL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.leAcc_leL

/-- info: 'C3.RV32.s29AddC_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.s29AddC_congr

/-- info: 'C3.RV32.lo9_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.lo9_of

/-- info: 'C3.RV32.hi9_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.hi9_of

/-- info: 'C3.RV32.memBytes_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.memBytes_ext

/-- info: 'C3.RV32.witnessRegionsEv_apart' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.witnessRegionsEv_apart

/-- info: 'C3.RV32.Cur.readerU32_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.readerU32_correct

/-- info: 'C3.RV32.Cur.readerMagic_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.readerMagic_correct

/-- info: 'C3.RV32.Cur.manifestPart_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.manifestPart_correct

/-- info: 'C3.RV32.eqArr97_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.eqArr97_correct

/-- info: 'C3.RV32.fulcioIterNext_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fulcioIterNext_correct

/-- info: 'C3.RV32.fulcioEnumNext_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fulcioEnumNext_correct

/-- info: 'C3.RV32.fulcioIterNth_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.fulcioIterNth_correct

/-- info: 'C3.RV32.bundleField_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.bundleField_correct

/-- info: 'C3.RV32.Cur.bootstateDecode_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bootstateDecode_correct

/-- info: 'C3.RV32.Cur.imageParse_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.imageParse_correct

/-- info: 'C3.RV32.Cur.bootWrite_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bootWrite_correct

/-- info: 'C3.RV32.Cur.bt_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bt_inv

/-- info: 'C3.RV32.Cur.bt_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bt_map

/-- info: 'C3.RV32.Cur.bt_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bt_copy

/-- info: 'C3.RV32.Cur.HdrEq.bootMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.HdrEq.bootMem

/-- info: 'C3.RV32.Cur.epr_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.epr_correct

/-- info: 'C3.RV32.Cur.rs_raise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.rs_raise

/-- info: 'C3.RV32.Cur.bt_lock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bt_lock

/-- info: 'C3.RV32.Cur.bt_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bt_body

/-- info: 'C3.RV32.Cur.boot_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.boot_correct

/-- info: 'C3.RV32.BootLevel.btPop_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.BootLevel.btPop_toNat

/-- info: 'C3.RV32.BootLevel.popN_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.BootLevel.popN_mod

/-- info: 'C3.RV32.BootLevel.btPop_level' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.BootLevel.btPop_level

/-- info: 'C3.RV32.BootLevel.btPop_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.BootLevel.btPop_ge

/-- info: 'C3.RV32.Dq.p384Decompress_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Dq.p384Decompress_correct

/-- info: 'C3.RV32.Fs.p384FromSec1_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Fs.p384FromSec1_correct

/-- info: 'C3.RV32.Gs.p256FromSec1_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Gs.p256FromSec1_correct

/-- info: 'C3.RV32.Gd.p256Decompress_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Gd.p256Decompress_correct

/-- info: 'C3.RV32.Pv.p384VerifyPrehash_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Pv.p384VerifyPrehash_correct

/-- info: 'C3.RV32.P2v.p256VerifyPrehash_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.P2v.p256VerifyPrehash_correct

/-- info: 'C3.RV32.P2v.p256VerifyPrehash_correct_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.P2v.p256VerifyPrehash_correct_bound

/-- info: 'C3.RV32.P2v.p256VerifyPrehash_correct_np' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.P2v.p256VerifyPrehash_correct_np

/-- info: 'C3.RV32.P2v.p256_ivf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.P2v.p256_ivf

/-- info: 'C3.RV32.P2v.p2v_p256_z_np' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.P2v.p2v_p256_z_np

/-- info: 'C3.RV32.P2v.p2v_p256_z_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.P2v.p2v_p256_z_or

/-- info: 'C3.RV32.P2v.p2vnp_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.P2v.p2vnp_ne

/-- info: 'C3.RV32.Pv.p384VerifyPrehash_correct_np' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Pv.p384VerifyPrehash_correct_np

/-- info: 'C3.RV32.Pv.pvnp_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Pv.pvnp_model

/-- info: 'C3.RV32.Pv.pvnp_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Pv.pvnp_loop

/-- info: 'C3.RV32.Pv.pvnp_mont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Pv.pvnp_mont

/-- info: 'C3.Models.p256_model_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Models.p256_model_closed

/-- info: 'C3.Models.p384_model_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Models.p384_model_closed

/-- info: 'C3.RV32.EdM.svEdModel_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.EdM.svEdModel_closed

/-- info: 'C3.RV32.Sv.sv_pro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Sv.sv_pro

/-- info: 'C3.RV32.Sv.sv_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Sv.sv_ret

/-- info: 'C3.RV32.Sv.sv_err' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Sv.sv_err

/-- info: 'C3.RV32.Sv.sv_verify_5c' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Sv.sv_verify_5c

/-- info: 'C3.RV32.Sv.sv_verify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Sv.sv_verify

/-- info: 'C3.RV32.Sv.sv_verify_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Sv.sv_verify_at

/-- info: 'C3.RV32.Sv.sv_verify_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Sv.sv_verify_spec

/-- info: 'C3.RV32.Sv.derErrByte_lt' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.Sv.derErrByte_lt

/-- info: 'C3.RV32.Sv.derScalarOf_err_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Sv.derScalarOf_err_lt

/-- info: 'C3.RV32.Sv.ecdsaSigOf_err_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Sv.ecdsaSigOf_err_lt

/-- info: 'C3.RV32.Sv.derAlgOf_err_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Sv.derAlgOf_err_lt

/-- info: 'C3.RV32.Sv.isSha256Of_err_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Sv.isSha256Of_err_lt

/-- info: 'C3.RV32.Sv.listsOidLoop_err_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Sv.listsOidLoop_err_lt

/-- info: 'C3.RV32.Sv.listsOidOf_err_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Sv.listsOidOf_err_lt

/-- info: 'C3.RV32.Sv.derIntIsOf_err_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Sv.derIntIsOf_err_lt

/-- info: 'C3.RV32.tufIndexDocSpec_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufIndexDocSpec_ok

/-- info: 'C3.RV32.tufIndexDoc_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufIndexDoc_correct

/-- info: 'C3.RV32.tufHexValue_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufHexValue_correct

/-- info: 'C3.RV32.allAsciiDigit_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.allAsciiDigit_exact

/-- info: 'C3.RV32.flashPartRead_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.flashPartRead_correct

/-- info: 'C3.RV32.stripPrefix_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.stripPrefix_correct

/-- info: 'C3.RV32.efuseProgramRun_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.efuseProgramRun_correct

/-- info: 'C3.RV32.tufHexDecode_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufHexDecode_correct

/-- info: 'C3.RV32.tufReadDoc_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufReadDoc_correct

/-- info: 'C3.RV32.ecdsaSignature32_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.ecdsaSignature32_correct

/-- info: 'C3.sha384_eq_stream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.sha384_eq_stream

/-- info: 'C3.RV32.sha384Fn_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.sha384Fn_correct
/-- info: 'C3.RV32.jsonSkipWs_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonSkipWs_correct

/-- info: 'C3.RV32.jsonStringEnd_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonStringEnd_correct

/-- info: 'C3.RV32.jsonNumberEnd_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonNumberEnd_correct

/-- info: 'C3.RV32.jsonKeyEnd_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonKeyEnd_correct

/-- info: 'C3.RV32.jsonStr_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonStr_correct

/-- info: 'C3.RV32.jsonMembers_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonMembers_correct

/-- info: 'C3.RV32.jsonElements_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonElements_correct

/-- info: 'C3.RV32.jsonLiteralEnd_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonLiteralEnd_correct

/-- info: 'C3.RV32.jsonU64_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonU64_correct

/-- info: 'C3.RV32.allAsciiDigit_wp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.allAsciiDigit_wp

/-- info: 'C3.RV32.jsonReadItem_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonReadItem_correct

/-- info: 'C3.RV32.jsonNextElement_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonNextElement_correct

/-- info: 'C3.RV32.jsonNextMember_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonNextMember_correct

/-- info: 'C3.RV32.jsonGet_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonGet_correct

/-- info: 'C3.RV32.jsonField_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonField_correct

/-- info: 'C3.RV32.pa_canon' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pa_canon

/-- info: 'C3.RV32.pa_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pa_strict

/-- info: 'C3.RV32.pa_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pa_keys

/-- info: 'C3.RV32.pa_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pa_close

/-- info: 'C3.RV32.pa_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.pa_loop

/-- info: 'C3.RV32.jsonParse_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.jsonParse_correct

/-- info: 'C3.Json.parseModel_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Json.parseModel_ok

/-- info: 'C3.Json.parseModel_ok_canon' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Json.parseModel_ok_canon

/-- info: 'C3.Json.objGet_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.objGet_val

/-- info: 'C3.RV32.tufExpires_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufExpires_correct

/-- info: 'C3.RV32.tufPemSpki_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufPemSpki_correct

/-- info: 'C3.Json.pemSpkiModel_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.pemSpkiModel_sound

/-- info: 'C3.Json.pemSpkiModel_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.pemSpkiModel_complete

/-- info: 'C3.Json.pemSpkiModel_p256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.pemSpkiModel_p256

/-- info: 'C3.Json.pemSpkiModel_p384' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.pemSpkiModel_p384

/-- info: 'C3.RV32.tufParseMetadata_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufParseMetadata_correct

/-- info: 'C3.RV32.tufParseRoot_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufParseRoot_correct

/-- info: 'C3.RV32.tufRoleKeysRead_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufRoleKeysRead_correct

/-- info: 'C3.RV32.tufRoleKeysMet_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufRoleKeysMet_correct

/-- info: 'C3.RV32.tufRoleKeysMet_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufRoleKeysMet_ret

/-- info: 'C3.RV32.tufRoleKeysMet_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufRoleKeysMet_spec

/-- info: 'C3.RV32.tufRoleKeysMet_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.tufRoleKeysMet_result

/-- info: 'C3.RV32.rmr_okBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.rmr_okBit

/-- info: 'C3.RV32.rmr_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.rmr_tag

/-- info: 'C3.Json.parseValue_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.parseValue_bytes

/-- info: 'C3.Json.JVal_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.JVal_bytes

/-- info: 'C3.Json.parseJson_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.parseJson_bytes

/-- info: 'C3.Json.parseHex_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.parseHex_lt

/-- info: 'C3.Json.decodeKey_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.decodeKey_lt

/-- info: 'C3.Json.rkBytes_of_roleKeys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.rkBytes_of_roleKeys

/-- info: 'C3.Json.rkBytes_of_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.rkBytes_of_mem

/-- info: 'C3.RV32.trustedRootDecode_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.trustedRootDecode_correct

/-- info: 'C3.RV32.trustedRootValidFor_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.trustedRootValidFor_correct

/-- info: 'C3.RV32.trustedRootReadChain_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.trustedRootReadChain_correct
/-- info: 'C3.RV32.rce_readChainPos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.rce_readChainPos
/-- info: 'C3.RV32.validForPos_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.validForPos_spec
/-- info: 'C3.RV32.trustedRootValidFor_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.trustedRootValidFor_spec
/-- info: 'C3.RV32.trk_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.trk_decode
/-- info: 'C3.RV32.trk_decodeNone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.trk_decodeNone
/-- info: 'C3.RV32.rcKey_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.rcKey_spec
/-- info: 'C3.RV32.rcParse_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.rcParse_spec
/-- info: 'C3.RV32.readChainPos_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.readChainPos_spec
/-- info: 'C3.RV32.trustedRootReadChain_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.trustedRootReadChain_spec
/-- info: 'C3.Json.Members' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.Members

/-- info: 'C3.Json.Elements' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.Elements

/-- info: 'C3.Json.ObjKeys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.ObjKeys

/-- info: 'C3.Json.ObjGet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.ObjGet

/-- info: 'C3.Json.ObjField' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.ObjField

/-- info: 'C3.Json.StrRes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.StrRes

/-- info: 'C3.Json.U64Val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.U64Val

/-- info: 'C3.Json.CurOpen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.CurOpen


/-- info: 'C3.Json.KeysIncreasingDistinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.KeysIncreasingDistinct

/-- info: 'C3.Json.ParseJsonSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.ParseJsonSome

/-- info: 'C3.Json.ParseModelOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.ParseModelOk

/-- info: 'C3.Json.ParseModelError' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.ParseModelError

/-- info: 'C3.Json.JValUnique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.JValUnique

/-- info: 'C3.Json.CanonEncode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.CanonEncode

/-- info: 'C3.Json.expiresModel_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.expiresModel_spec

/-- info: 'C3.Json.pemSpkiModel_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.pemSpkiModel_spec

/-- info: 'C3.Json.pmModel_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.pmModel_spec

/-- info: 'C3.Json.prModel_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.prModel_spec

/-- info: 'C3.Json.rkModel_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.rkModel_spec

/-- info: 'C3.Json.thresholdMet_roleKeys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.thresholdMet_roleKeys

/-- info: 'C3.RV32.Ac.ac_pro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_pro

/-- info: 'C3.RV32.Ac.ac_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_ret

/-- info: 'C3.RV32.Ac.ac_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_none

/-- info: 'C3.RV32.Ac.ac_fail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_fail

/-- info: 'C3.RV32.Ac.ac_from806' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_from806

/-- info: 'C3.RV32.Ac.ac_reject' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_reject

/-- info: 'C3.RV32.Ac.ac_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_exit

/-- info: 'C3.RV32.Ac.AcInv.wide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcInv.wide

/-- info: 'C3.RV32.Ac.ac_exit_wide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_exit_wide

/-- info: 'C3.decodeImageHeader_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.decodeImageHeader_take

/-- info: 'C3.aci_imgW_err' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.aci_imgW_err

/-- info: 'C3.aci_imgW_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.aci_imgW_ok

/-- info: 'C3.RV32.Ac.aci_manifest_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aci_manifest_len

/-- info: 'C3.RV32.Ac.aci_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aci_decode

/-- info: 'C3.RV32.Ac.acImagePre_of_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acImagePre_of_read

/-- info: 'C3.RV32.Ac.acImage_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acImage_stage

/-- info: 'C3.RV32.Ac.acs_imgW_cnt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_imgW_cnt

/-- info: 'C3.RV32.Ac.acs_st2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_st2
/-- info: 'C3.RV32.Ac.acf_seg_cmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acf_seg_cmp

/-- info: 'C3.RV32.Ac.acf_seg_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acf_seg_write

/-- info: 'C3.RV32.Ac.acf_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acf_exit

/-- info: 'C3.RV32.Ac.ac_finish_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_finish_stage
/-- info: 'C3.RV32.Cur.bmr_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmr_read

/-- info: 'C3.RV32.Cur.bmr_enc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmr_enc

/-- info: 'C3.RV32.BootMainContract.bmc_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.BootMainContract.bmc_decode

/-- info: 'C3.RV32.BootMainContract.bmc_hdr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.BootMainContract.bmc_hdr

/-- info: 'C3.RV32.BootMainContract.bmc_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.BootMainContract.bmc_accept

/-- info: 'C3.RV32.Cur.BmKeep.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.BmKeep.step

/-- info: 'C3.RV32.Cur.BmKeep.out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.BmKeep.out

/-- info: 'C3.RV32.Cur.BmKeep.codeIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.BmKeep.codeIn

/-- info: 'C3.RV32.Cur.bm_romcall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bm_romcall

/-- info: 'C3.RV32.Cur.BmEnd.pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.BmEnd.pre

/-- info: 'C3.RV32.Cur.bmt_hdr_move' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_hdr_move

/-- info: 'C3.RV32.Cur.bmt_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_tail

/-- info: 'C3.RV32.Cur.bmt_burn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_burn

/-- info: 'C3.RV32.Cur.bmt_mask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_mask

/-- info: 'C3.RV32.Cur.bmt_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_copy

/-- info: 'C3.RV32.Cur.bmt_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_max

/-- info: 'C3.RV32.Cur.bmt_acc_move' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_acc_move

/-- info: 'C3.RV32.Cur.bmp_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmp_first

/-- info: 'C3.RV32.Cur.bmp_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmp_other

/-- info: 'C3.RV32.Cur.bmw_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmw_call

/-- info: 'C3.RV32.Cur.bmc_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmc_call

/-- info: 'C3.RV32.Cur.bmt_lo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_lo

/-- info: 'C3.RV32.Cur.bmt_lo_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_lo_eq

/-- info: 'C3.RV32.Cur.bmt_mod_add' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_mod_add

/-- info: 'C3.RV32.Cur.bmt_addlo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_addlo

/-- info: 'C3.RV32.Cur.bmt_sublo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_sublo

/-- info: 'C3.RV32.Cur.bmt_xorlo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_xorlo

/-- info: 'C3.RV32.Cur.bmt_and1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_and1

/-- info: 'C3.RV32.Cur.bmt_low_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmt_low_and

/-- info: 'C3.RV32.Cur.bmd_plan_trial' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_plan_trial

/-- info: 'C3.RV32.Cur.bmd_word_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_word_byte

/-- info: 'C3.RV32.Cur.bmd_sat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_sat

/-- info: 'C3.RV32.Cur.bmd_boots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_boots

/-- info: 'C3.RV32.Cur.bmd_rec_tr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_rec_tr

/-- info: 'C3.RV32.Cur.bmd_rec_nt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_rec_nt

/-- info: 'C3.RV32.Cur.bmd_dec_acc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_dec_acc

/-- info: 'C3.RV32.Cur.bmd_dec_rej' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_dec_rej

/-- info: 'C3.RV32.Cur.bmd_dec_oth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_dec_oth

/-- info: 'C3.RV32.Cur.BmdPre.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.BmdPre.keep

/-- info: 'C3.RV32.Cur.bmd_kin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_kin

/-- info: 'C3.RV32.Cur.bmd_lowS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_lowS

/-- info: 'C3.RV32.Cur.bmd_acc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_acc

/-- info: 'C3.RV32.Cur.bmd_ffnz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_ffnz

/-- info: 'C3.RV32.Cur.bmd_room' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_room

/-- info: 'C3.RV32.Cur.bmd_halt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_halt

/-- info: 'C3.RV32.Cur.bmd_oth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_oth

/-- info: 'C3.RV32.Cur.bmd_rej' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_rej

/-- info: 'C3.RV32.Cur.bmd_main' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmd_main

/-- info: 'C3.RV32.Cur.BmqPre.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.BmqPre.keep

/-- info: 'C3.RV32.Cur.bmq_word_lo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_word_lo

/-- info: 'C3.RV32.Cur.bmq_s6_lo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_s6_lo

/-- info: 'C3.RV32.Cur.bmq_kin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_kin

/-- info: 'C3.RV32.Cur.bmq_keep3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_keep3

/-- info: 'C3.RV32.Cur.bmq_rec_ex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_rec_ex

/-- info: 'C3.RV32.Cur.bmq_exw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_exw

/-- info: 'C3.RV32.Cur.bmq_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_none

/-- info: 'C3.RV32.Cur.bmq_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_live

/-- info: 'C3.RV32.Cur.bmq_exp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_exp

/-- info: 'C3.RV32.Cur.bmq_plan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmq_plan

/-- info: 'C3.RV32.Cur.bme_kin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_kin

/-- info: 'C3.RV32.Cur.bme_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_below

/-- info: 'C3.RV32.Cur.bme_low' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_low

/-- info: 'C3.RV32.Cur.bme_memset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_memset

/-- info: 'C3.RV32.Cur.BmePre.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.BmePre.keep

/-- info: 'C3.RV32.Cur.bme_andc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_andc

/-- info: 'C3.RV32.Cur.bme_hiload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_hiload

/-- info: 'C3.RV32.Cur.bme_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_tail

/-- info: 'C3.RV32.Cur.bme_d8' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_d8

/-- info: 'C3.RV32.Cur.bme_srl3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_srl3

/-- info: 'C3.RV32.Cur.bme_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_word

/-- info: 'C3.RV32.Cur.bme_F4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_F4

/-- info: 'C3.RV32.Cur.bme_c1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_c1

/-- info: 'C3.RV32.Cur.bme_c0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_c0

/-- info: 'C3.RV32.Cur.bme_def' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_def

/-- info: 'C3.RV32.Cur.bme_zt' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_zt

/-- info: 'C3.RV32.Cur.bme_zne' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_zne

/-- info: 'C3.RV32.Cur.bme_sel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bme_sel

/-- info: 'C3.RV32.Cur.bms_ok4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_ok4

/-- info: 'C3.RV32.Cur.bms_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_bytes

/-- info: 'C3.RV32.Cur.bms_ld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_ld

/-- info: 'C3.RV32.Cur.bms_sn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_sn

/-- info: 'C3.RV32.Cur.bms_a4' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_a4

/-- info: 'C3.RV32.Cur.bms_a5' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_a5

/-- info: 'C3.RV32.Cur.bms_a6' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_a6

/-- info: 'C3.RV32.Cur.bms_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_copy

/-- info: 'C3.RV32.Cur.bms_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_congr

/-- info: 'C3.RV32.Cur.bms_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_list

/-- info: 'C3.RV32.Cur.bms_bsx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_bsx

/-- info: 'C3.RV32.Cur.bms_lo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_lo

/-- info: 'C3.RV32.Cur.bms_Fbig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_Fbig

/-- info: 'C3.RV32.Cur.bms_m70' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_m70

/-- info: 'C3.RV32.Cur.bms_frd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_frd

/-- info: 'C3.RV32.Cur.bms_bsd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_bsd

/-- info: 'C3.RV32.Cur.bms_halt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_halt

/-- info: 'C3.RV32.Cur.bms_hiF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_hiF

/-- info: 'C3.RV32.Cur.bms_off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_off

/-- info: 'C3.RV32.Cur.bms_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_reads

/-- info: 'C3.RV32.Cur.bms_frmem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_frmem

/-- info: 'C3.RV32.Cur.bms_spc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_spc

/-- info: 'C3.RV32.Cur.bms_swok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_swok

/-- info: 'C3.RV32.Cur.bms_swfr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_swfr

/-- info: 'C3.RV32.Cur.bms_spF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_spF

/-- info: 'C3.RV32.Cur.bms_ptr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_ptr

/-- info: 'C3.RV32.Cur.bms_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bms_entry

/-- info: 'C3.RV32.Cur.bootMain_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bootMain_correct
/-- info: 'C3.RV32.Ac.acp_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acp_stage
/-- info: 'C3.RV32.Ac.acIndexStage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acIndexStage

/-- info: 'C3.RV32.Ac.acx_post' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acx_post

/-- info: 'C3.RV32.Ac.acx_to4e4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acx_to4e4

/-- info: 'C3.RV32.Ac.acx_to440' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acx_to440

/-- info: 'C3.RV32.Ac.acx_t1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acx_t1

/-- info: 'C3.RV32.Ac.acx_t2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acx_t2

/-- info: 'C3.RV32.Ac.acx_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acx_loop
/-- info: 'C3.RV32.Ac.acceptRead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acceptRead
/-- info: 'C3.Json.act_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Json.act_finish

/-- info: 'C3.RV32.Ac.act_89a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.act_89a

/-- info: 'C3.RV32.Ac.act_836' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.act_836

/-- info: 'C3.RV32.Ac.act_metSpec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.act_metSpec

/-- info: 'C3.RV32.Ac.ActRk.congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ActRk.congr

/-- info: 'C3.RV32.Ac.act_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.act_stage
/-- info: 'C3.RV32.Ac.aco_verifyTuf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_verifyTuf

/-- info: 'C3.RV32.Ac.aco_sepN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_sepN

/-- info: 'C3.RV32.Ac.aco_sepD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_sepD

/-- info: 'C3.RV32.Ac.aco_num' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_num

/-- info: 'C3.RV32.Ac.aco_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_bv

/-- info: 'C3.RV32.Ac.aco_bvB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_bvB

/-- info: 'C3.RV32.Ac.aco_fixS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_fixS

/-- info: 'C3.RV32.Ac.aco_fix_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_fix_out

/-- info: 'C3.RV32.Ac.aco_fixK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_fixK

/-- info: 'C3.RV32.Ac.aco_ldK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_ldK

/-- info: 'C3.RV32.Ac.AcoKeep.trans' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.Ac.AcoKeep.trans

/-- info: 'C3.RV32.Ac.aco_wLow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_wLow

/-- info: 'C3.RV32.Ac.aco_wScr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_wScr

/-- info: 'C3.RV32.Ac.aco_wW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_wW




/-- info: 'C3.RV32.Ac.aco_st8S' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_st8S

/-- info: 'C3.RV32.Ac.aco_slotAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_slotAdd

/-- info: 'C3.RV32.Ac.aco_addSlot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_addSlot


/-- info: 'C3.RV32.Ac.aco_ne' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_ne

/-- info: 'C3.RV32.Ac.aco_rkC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_rkC

/-- info: 'C3.RV32.Ac.aco_rk0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_rk0

/-- info: 'C3.RV32.Ac.aco_rkOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_rkOk

/-- info: 'C3.RV32.Ac.aco_spki' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_spki

/-- info: 'C3.RV32.Ac.aco_dk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_dk

/-- info: 'C3.RV32.Ac.aco_rkwf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_rkwf

/-- info: 'C3.RV32.Ac.aco_ver' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_ver

/-- info: 'C3.RV32.Ac.aco_memcpy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_memcpy

/-- info: 'C3.RV32.Ac.aco_mcRegs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_mcRegs

/-- info: 'C3.RV32.Ac.aco_mcMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_mcMem

/-- info: 'C3.RV32.Ac.AcoCtx.envK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcoCtx.envK

/-- info: 'C3.RV32.Ac.AcoCtx.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcoCtx.code

/-- info: 'C3.RV32.Ac.AcoKR.a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcoKR.a

/-- info: 'C3.RV32.Ac.AcoCtx.sp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcoCtx.sp

/-- info: 'C3.RV32.Ac.AcoCtx.ainv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcoCtx.ainv

/-- info: 'C3.RV32.Ac.aco_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_pre

/-- info: 'C3.RV32.Ac.aco_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_leaf

/-- info: 'C3.RV32.Ac.aco_leaf2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_leaf2

/-- info: 'C3.RV32.Ac.aco_jmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_jmp

/-- info: 'C3.RV32.Ac.aco_ze8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_ze8

/-- info: 'C3.RV32.Ac.aco_zeq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_zeq

/-- info: 'C3.RV32.Ac.aco_ld88' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_ld88

/-- info: 'C3.RV32.Ac.aco_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_exit

/-- info: 'C3.RV32.Ac.aco_so' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_so

/-- info: 'C3.RV32.Ac.aco_expC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_expC

/-- info: 'C3.RV32.Ac.aco_mc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_mc

/-- info: 'C3.RV32.Ac.aco_F' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_F

/-- info: 'C3.RV32.Ac.aco_ds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_ds

/-- info: 'C3.RV32.Ac.aco_ro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_ro

/-- info: 'C3.RV32.Ac.aco_inSep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_inSep

/-- info: 'C3.RV32.Ac.aco_met' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_met

/-- info: 'C3.RV32.Ac.aco_rk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_rk

/-- info: 'C3.RV32.Ac.aco_tex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_tex

/-- info: 'C3.RV32.Ac.aco_pr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_pr

/-- info: 'C3.RV32.Ac.aco_nameSep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_nameSep

/-- info: 'C3.RV32.Ac.aco_tbkC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_tbkC

/-- info: 'C3.RV32.Ac.aco_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_last

/-- info: 'C3.RV32.Ac.aco_lastE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_lastE

/-- info: 'C3.RV32.Ac.aco_E' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_E

/-- info: 'C3.RV32.Ac.aco_zfe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_zfe

/-- info: 'C3.RV32.Ac.aco_zx8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_zx8

/-- info: 'C3.RV32.Ac.aco_zlt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_zlt

/-- info: 'C3.RV32.Ac.aco_D' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_D

/-- info: 'C3.RV32.Ac.aco_fe32' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_fe32

/-- info: 'C3.RV32.Ac.aco_and8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_and8

/-- info: 'C3.RV32.Ac.aco_w8' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_w8

/-- info: 'C3.RV32.Ac.aco_C' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_C

/-- info: 'C3.RV32.Ac.aco_foldStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_foldStep

/-- info: 'C3.RV32.Ac.aco_stC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_stC

/-- info: 'C3.RV32.Ac.aco_B2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_B2

/-- info: 'C3.RV32.Ac.aco_idxSumC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_idxSumC

/-- info: 'C3.RV32.Ac.aco_tidC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_tidC

/-- info: 'C3.RV32.Ac.aco_tidK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_tidK

/-- info: 'C3.RV32.Ac.aco_codeSep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_codeSep

/-- info: 'C3.RV32.Ac.aco_rd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_rd

/-- info: 'C3.RV32.Ac.aco_rdE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_rdE

/-- info: 'C3.RV32.Ac.aco_stK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_stK

/-- info: 'C3.RV32.Ac.aco_stG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_stG

/-- info: 'C3.RV32.Ac.aco_getD' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_getD

/-- info: 'C3.RV32.Ac.aco_B' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_B

/-- info: 'C3.RV32.Ac.aco_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aco_loop

/-- info: 'C3.RV32.Ac.acRootsStage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acRootsStage
/-- info: 'C3.RV32.Ac.ac_extract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_extract

/-- info: 'C3.RV32.Ac.ace_extract_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_extract_spec

/-- info: 'C3.RV32.Ac.AceKeysIn.sv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AceKeysIn.sv

/-- info: 'C3.RV32.Ac.ace_mcpy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_mcpy

/-- info: 'C3.RV32.Ac.AceKeysIn.move' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AceKeysIn.move

/-- info: 'C3.RV32.Ac.ace_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_tail

/-- info: 'C3.Json.ace_parseModel' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Json.ace_parseModel

/-- info: 'C3.Json.ace_objField' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.Json.ace_objField

/-- info: 'C3.RV32.Ac.ace_f1A6A' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_f1A6A

/-- info: 'C3.RV32.Ac.ace_f1A66' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_f1A66

/-- info: 'C3.RV32.Ac.ace_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_stage

/-- info: 'C3.RV32.Ac.ace_d38' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_d38

/-- info: 'C3.RV32.Ac.ace_d04' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_d04

/-- info: 'C3.RV32.Ac.ace_zl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_zl

/-- info: 'C3.RV32.Ac.ace_cec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_cec

/-- info: 'C3.RV32.Ac.ace_c6e' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_c6e

/-- info: 'C3.RV32.Ac.ace_hm0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_hm0

/-- info: 'C3.RV32.Ac.ace_c32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_c32

/-- info: 'C3.RV32.Ac.ace_c24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_c24

/-- info: 'C3.RV32.Ac.ace_c12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_c12

/-- info: 'C3.RV32.Ac.ace_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_head

/-- info: 'C3.RV32.Ac.acedp_distinct_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acedp_distinct_iff

/-- info: 'C3.RV32.Ac.acedp_nCheck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acedp_nCheck

/-- info: 'C3.RV32.Ac.acedp_kCheck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acedp_kCheck

/-- info: 'C3.RV32.Ac.acedp_cmpN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acedp_cmpN

/-- info: 'C3.RV32.Ac.acedp_cmp97' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acedp_cmp97

/-- info: 'C3.RV32.Ac.acedp_cmp32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acedp_cmp32

/-- info: 'C3.RV32.Ac.ace_dup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_dup

/-- info: 'C3.RV32.Ac.ac_extract_loops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ac_extract_loops
/-- info: 'C3.RV32.Ac.acb_app4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_app4

/-- info: 'C3.RV32.Ac.acb_mb2' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_mb2

/-- info: 'C3.RV32.Ac.acb_mb4' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_mb4

/-- info: 'C3.RV32.Ac.acb_readU32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_readU32

/-- info: 'C3.RV32.Ac.acb_field_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_field_spec

/-- info: 'C3.RV32.Ac.acb_header_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_header_spec

/-- info: 'C3.RV32.Ac.acb_leNat8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_leNat8

/-- info: 'C3.RV32.Ac.acb_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_u64

/-- info: 'C3.RV32.Ac.acb_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_decode

/-- info: 'C3.RV32.Ac.acb_codeHi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_codeHi

/-- info: 'C3.RV32.Ac.AcBundleEnv.hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcBundleEnv.hi

/-- info: 'C3.RV32.Ac.acb_sep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_sep

/-- info: 'C3.RV32.Ac.acb_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_mono

/-- info: 'C3.RV32.Ac.acb_VW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_VW

/-- info: 'C3.RV32.Ac.acb_FcV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_FcV

/-- info: 'C3.RV32.Ac.acb_stack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_stack

/-- info: 'C3.RV32.Ac.acb_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_hi

/-- info: 'C3.RV32.Ac.acb_buf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_buf

/-- info: 'C3.RV32.Ac.acb_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_at

/-- info: 'C3.RV32.Ac.acb_ld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_ld

/-- info: 'C3.RV32.Ac.acb_ldBuf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_ldBuf

/-- info: 'C3.RV32.Ac.acb_bytesBuf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_bytesBuf

/-- info: 'C3.RV32.Ac.acb_al' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_al

/-- info: 'C3.RV32.Ac.acb_spAl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_spAl

/-- info: 'C3.RV32.Ac.acb_ldS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_ldS

/-- info: 'C3.RV32.Ac.acb_ofNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_ofNat

/-- info: 'C3.RV32.Ac.acb_sub0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_sub0

/-- info: 'C3.RV32.Ac.acb_ne' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_ne

/-- info: 'C3.RV32.Ac.acb_stackCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_stackCode

/-- info: 'C3.RV32.Ac.acb_bufSep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_bufSep

/-- info: 'C3.RV32.Ac.acb_os' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_os

/-- info: 'C3.RV32.Ac.acb_fieldMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_fieldMem

/-- info: 'C3.RV32.Ac.acb_s4' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_s4

/-- info: 'C3.RV32.Ac.acb_s8' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_s8

/-- info: 'C3.RV32.Ac.acb_o4' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_o4

/-- info: 'C3.RV32.Ac.AcbBuf.hbuf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbBuf.hbuf

/-- info: 'C3.RV32.Ac.AcbBuf.bs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbBuf.bs

/-- info: 'C3.RV32.Ac.acb_fcall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_fcall

/-- info: 'C3.RV32.Ac.acb_magicR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_magicR

/-- info: 'C3.RV32.Ac.acb_versionR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_versionR

/-- info: 'C3.RV32.Ac.acb_mcall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_mcall

/-- info: 'C3.RV32.Ac.acb_vcall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_vcall

/-- info: 'C3.RV32.Ac.acb_cpy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_cpy

/-- info: 'C3.RV32.Ac.acb_zb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_zb

/-- info: 'C3.RV32.Ac.acb_t6a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_t6a

/-- info: 'C3.RV32.Ac.acb_t66' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_t66

/-- info: 'C3.RV32.Ac.acb_ne1' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_ne1

/-- info: 'C3.RV32.Ac.acb_Mi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_Mi

/-- info: 'C3.RV32.Ac.acb_st8' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_st8

/-- info: 'C3.RV32.Ac.acb_st32' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_st32

/-- info: 'C3.RV32.Ac.AcbKw.kw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbKw.kw

/-- info: 'C3.RV32.Ac.AcbK.kw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbK.kw

/-- info: 'C3.RV32.Ac.AcbG.hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbG.hi

/-- info: 'C3.RV32.Ac.AcbG.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbG.code

/-- info: 'C3.RV32.Ac.AcbG.env' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbG.env

/-- info: 'C3.RV32.Ac.AcbG.buf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbG.buf

/-- info: 'C3.RV32.Ac.AcbG.inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbG.inv

/-- info: 'C3.RV32.Ac.AcbG.invW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbG.invW

/-- info: 'C3.RV32.Ac.AcbG.resW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbG.resW

/-- info: 'C3.RV32.Ac.acb_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_bind

/-- info: 'C3.RV32.Ac.acb_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_ret

/-- info: 'C3.RV32.Ac.acb_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_stage

/-- info: 'C3.RV32.Ac.acb_x6a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_x6a

/-- info: 'C3.RV32.Ac.acb_x66' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_x66

/-- info: 'C3.RV32.Ac.acb_spk' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_spk

/-- info: 'C3.RV32.Ac.acb_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_pre

/-- info: 'C3.RV32.Ac.AcbK.regs' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbK.regs

/-- info: 'C3.RV32.Ac.acb_fstep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_fstep

/-- info: 'C3.RV32.Ac.acb_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_chk

/-- info: 'C3.RV32.Ac.acbI_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbI_end

/-- info: 'C3.RV32.Ac.acb_cm' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_cm

/-- info: 'C3.RV32.Ac.acb_lst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_lst

/-- info: 'C3.RV32.Ac.acb_lsb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_lsb

/-- info: 'C3.RV32.Ac.acb_ldC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_ldC

/-- info: 'C3.RV32.Ac.acb_hiC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_hiC

/-- info: 'C3.RV32.Ac.acb_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_init

/-- info: 'C3.RV32.Ac.AcbK.call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcbK.call

/-- info: 'C3.RV32.Ac.acb_dd0' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_dd0

/-- info: 'C3.RV32.Ac.acb_rdr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_rdr

/-- info: 'C3.RV32.Ac.acb_hdr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_hdr

/-- info: 'C3.RV32.Ac.acb_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_map

/-- info: 'C3.RV32.Ac.acb_fld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_fld

/-- info: 'C3.RV32.Ac.acb_blk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_blk

/-- info: 'C3.RV32.Ac.acb_lsl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_lsl

/-- info: 'C3.RV32.Ac.acbA2_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbA2_end

/-- info: 'C3.RV32.Ac.acb_sl' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_sl

/-- info: 'C3.RV32.Ac.acb_f2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_f2

/-- info: 'C3.RV32.Ac.acb_lws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_lws

/-- info: 'C3.RV32.Ac.acbA1_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbA1_end

/-- info: 'C3.RV32.Ac.acb_lw18b0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_lw18b0

/-- info: 'C3.RV32.Ac.acb_seg1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_seg1

/-- info: 'C3.RV32.Ac.acbA3_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbA3_end

/-- info: 'C3.RV32.Ac.acb_lw18fc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_lw18fc

/-- info: 'C3.RV32.Ac.acb_li1900' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_li1900

/-- info: 'C3.RV32.Ac.acb_w8' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_w8

/-- info: 'C3.RV32.Ac.acb_seg2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_seg2

/-- info: 'C3.RV32.Ac.acbB_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbB_end

/-- info: 'C3.RV32.Ac.acb_blkB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_blkB

/-- info: 'C3.RV32.Ac.acbA4_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbA4_end

/-- info: 'C3.RV32.Ac.acb_lw1952' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_lw1952

/-- info: 'C3.RV32.Ac.acb_and1956' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_and1956

/-- info: 'C3.RV32.Ac.acb_m32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_m32

/-- info: 'C3.RV32.Ac.acb_FcS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_FcS

/-- info: 'C3.RV32.Ac.acb_seg3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_seg3

/-- info: 'C3.RV32.Ac.acbA5_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbA5_end

/-- info: 'C3.RV32.Ac.acb_lw197e' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_lw197e

/-- info: 'C3.RV32.Ac.acb_seg4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_seg4

/-- info: 'C3.RV32.Ac.acbA6_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbA6_end

/-- info: 'C3.RV32.Ac.acbC_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbC_end

/-- info: 'C3.RV32.Ac.acb_890' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_890

/-- info: 'C3.RV32.Ac.acb_seg5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_seg5

/-- info: 'C3.RV32.Ac.acbF_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acbF_end

/-- info: 'C3.RV32.Ac.acb_aadd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_aadd

/-- info: 'C3.RV32.Ac.acb_sb4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_sb4

/-- info: 'C3.RV32.Ac.acb_fs32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_fs32

/-- info: 'C3.RV32.Ac.acb_fs8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_fs8

/-- info: 'C3.RV32.Ac.acb_seg6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_seg6

/-- info: 'C3.RV32.Ac.acb_sq' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_sq

/-- info: 'C3.RV32.Ac.acb_bdIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_bdIn

/-- info: 'C3.RV32.Ac.acb_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_field

/-- info: 'C3.RV32.Ac.acb_rootHdr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_rootHdr

/-- info: 'C3.RV32.Ac.acb_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_root

/-- info: 'C3.RV32.Ac.acb_digest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acb_digest

/-- info: 'C3.RV32.Ac.acBundleStage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acBundleStage

/-- info: 'C3.RV32.Cur.wdg_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.wdg_correct

/-- info: 'C3.RV32.Cur.clk_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.clk_correct

/-- info: 'C3.RV32.Cur.resetMem_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.resetMem_out

/-- info: 'C3.RV32.Cur.rst_path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.rst_path

/-- info: 'C3.RV32.Cur.EprAt.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.EprAt.code

/-- info: 'C3.RV32.Cur.eprAt_of_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.eprAt_of_code

/-- info: 'C3.RV32.Cur.EprAt.out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.EprAt.out

/-- info: 'C3.RV32.Cur.EfOut.code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.EfOut.code

/-- info: 'C3.RV32.Cur.EfOut.panic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.EfOut.panic

/-- info: 'C3.RV32.Cur.rs_chkv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.rs_chkv

/-- info: 'C3.RV32.Cur.rs_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.rs_chk

/-- info: 'C3.RV32.Cur.rs_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.rs_tail

/-- info: 'C3.RV32.Cur.rs_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.rs_iter

/-- info: 'C3.RV32.Cur.rs_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.rs_loop

/-- info: 'C3.RV32.Cur.bt_bootMem_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bt_bootMem_hi

/-- info: 'C3.RV32.Cur.reset_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_word

/-- info: 'C3.RV32.Cur.reset_level' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_level

/-- info: 'C3.RV32.Cur.reset_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_correct

/-- info: 'C3.RV32.Ac.acets_rcErr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_rcErr

/-- info: 'C3.acs_parts_le' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.acs_parts_le

/-- info: 'C3.acs_expires_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.acs_expires_lt

/-- info: 'C3.RV32.Ac.acs_accept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_accept

/-- info: 'C3.RV32.Ac.acs_hdr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_hdr

/-- info: 'C3.RV32.Ac.AcsCtx.Ok.failW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcsCtx.Ok.failW

/-- info: 'C3.RV32.Ac.acs_fin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_fin

/-- info: 'C3.RV32.Ac.acs_bun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_bun

/-- info: 'C3.RV32.Ac.acs_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_ext

/-- info: 'C3.RV32.Ac.acs_tgt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_tgt

/-- info: 'C3.RV32.Ac.acs_rootsEnv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_rootsEnv

/-- info: 'C3.RV32.Ac.acs_roots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_roots

/-- info: 'C3.RV32.Ac.acs_fold_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_fold_bytes

/-- info: 'C3.RV32.Ac.acs_src' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_src

/-- info: 'C3.RV32.Ac.acs_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_pin

/-- info: 'C3.RV32.Ac.acs_decode_docs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_decode_docs

/-- info: 'C3.RV32.Ac.acs_indexStage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_indexStage

/-- info: 'C3.RV32.Ac.acs_doc_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_doc_at

/-- info: 'C3.RV32.Ac.acs_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_index

/-- info: 'C3.RV32.Ac.acs_image' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_image

/-- info: 'C3.RV32.Ac.acs_front' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_front

/-- info: 'C3.RV32.Ac.acs_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_spec

/-- info: 'C3.RV32.Ac.acs_contract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acs_contract

/-- info: 'C3.RV32.Ac.acl_envs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acl_envs

/-- info: 'C3.RV32.Ac.acl_acsE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acl_acsE

/-- info: 'C3.RV32.Cur.bmc_pop_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bmc_pop_lt

/-- info: 'C3.RV32.Ac.acets_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_stage

/-- info: 'C3.RV32.Ac.acets_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_loop

/-- info: 'C3.RV32.Ac.acets_p1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_p1

/-- info: 'C3.RV32.Ac.acets_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_exit

/-- info: 'C3.RV32.Ac.acets_p2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_p2

/-- info: 'C3.RV32.Ac.acets_rc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_rc

/-- info: 'C3.RV32.Ac.acets_p3a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_p3a

/-- info: 'C3.RV32.Ac.acets_p3b' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_p3b

/-- info: 'C3.RV32.Ac.acets_p4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_p4

/-- info: 'C3.RV32.Ac.acets_p4b' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_p4b

/-- info: 'C3.RV32.Ac.acets_p5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_p5

/-- info: 'C3.RV32.Ac.acets_back' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acets_back

/-- info: 'C3.RV32.Ac.ace_ca' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_ca

/-- info: 'C3.RV32.Ac.ace_ca_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.ace_ca_stage

/-- info: 'C3.RV32.Ac.aceca_pass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aceca_pass

/-- info: 'C3.RV32.Ac.aceca_dd2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aceca_dd2

/-- info: 'C3.RV32.Ac.aceca_e12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aceca_e12

/-- info: 'C3.RV32.Ac.aceca_back' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aceca_back

/-- info: 'C3.RV32.Ac.aceca_rc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aceca_rc

/-- info: 'C3.RV32.Ac.aceca_e2e' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aceca_e2e

/-- info: 'C3.RV32.Ac.aceca_e40' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aceca_e40

/-- info: 'C3.RV32.Ac.aceca_e7a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.aceca_e7a
/-- info: 'C3.RV32.piecesIn_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.piecesIn_mem

/-- info: 'C3.RV32.PiecesIn.congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.PiecesIn.congr

/-- info: 'C3.RV32.CodeIn.sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.CodeIn.sub

/-- info: 'C3.RV32.imagePieces_ok' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.imagePieces_ok

/-- info: 'C3.RV32.imagePieces_within' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.imagePieces_within

/-- info: 'C3.RV32.loaded_imageMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.loaded_imageMem

/-- info: 'C3.RV32.Loaded.congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Loaded.congr

/-- info: 'C3.RV32.Loaded.bootMain' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Loaded.bootMain

/-- info: 'C3.RV32.Loaded.p384R2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Loaded.p384R2

/-- info: 'C3.RV32.Cur.loaded_rstCode' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.loaded_rstCode

/-- info: 'C3.RV32.Cur.loaded_bsCode' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.loaded_bsCode

/-- info: 'C3.RV32.Cur.loaded_bwCode' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.loaded_bwCode

/-- info: 'C3.RV32.Cur.loaded_panicCode' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.loaded_panicCode

/-- info: 'C3.RV32.Cur.loaded_eprAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.loaded_eprAt

/-- info: 'C3.RV32.Cur.loaded_resetMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.loaded_resetMem

/-- info: 'C3.RV32.Cur.loaded_bmHyp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.loaded_bmHyp

/-- info: 'C3.RV32.Cur.reset_correct_loaded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_correct_loaded

/-- info: 'C3.RV32.Cur.reset_hlo' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_hlo

/-- info: 'C3.RV32.Cur.reset_hlo_c0' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_hlo_c0

/-- info: 'C3.RV32.chip_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.chip_step

/-- info: 'C3.RV32.chip_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.chip_steps

/-- info: 'C3.RV32.chip_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.chip_run

/-- info: 'C3.RV32.chipSim_init' does not depend on any axioms -/
#guard_msgs in #print axioms C3.RV32.chipSim_init

/-- info: 'C3.RV32.aliasOk_regions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.aliasOk_regions

/-- info: 'C3.RV32.Ac.acetl_tlog_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acetl_tlog_stage

/-- info: 'C3.RV32.Ac.acetl_pass' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acetl_pass

/-- info: 'C3.RV32.Ac.acetl_tEF2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acetl_tEF2

/-- info: 'C3.RV32.Ac.acetl_tF9E' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acetl_tF9E

/-- info: 'C3.RV32.Ac.acetl_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acetl_skip

/-- info: 'C3.RV32.Ac.acetl_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acetl_close

/-- info: 'C3.RV32.Ac.acetl_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acetl_end

/-- info: 'C3.RV32.Ac.acetl_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.acetl_pre

/-- info: 'C3.RV32.PanicIf.panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.PanicIf.panics

/-- info: 'C3.RV32.PanicIf.absurd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.PanicIf.absurd

/-- info: 'C3.RV32.PanicIf.of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.PanicIf.of_steps

/-- info: 'C3.RV32.panicHaltCode_not_deliberate' depends on axioms: [propext] -/
#guard_msgs in #print axioms C3.RV32.panicHaltCode_not_deliberate

/-- info: 'C3.RV32.HaltsWith.panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.HaltsWith.panics

/-- info: 'C3.RV32.HaltsWith.of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.HaltsWith.of_steps

/-- info: 'C3.RV32.HaltsDeliberately.panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.HaltsDeliberately.panics

/-- info: 'C3.RV32.HaltsDeliberately.of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.HaltsDeliberately.of_steps

/-- info: 'C3.RV32.HaltOut.panics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.HaltOut.panics

/-- info: 'C3.RV32.HaltOut.of_steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.HaltOut.of_steps

/-- info: 'C3.RV32.HaltOut.np' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.HaltOut.np

/-- info: 'C3.RV32.HaltOut.deliberate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.HaltOut.deliberate

/-- info: 'C3.RV32.halt_haltCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.halt_haltCode

/-- info: 'C3.RV32.beginUnwind_haltCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.beginUnwind_haltCode

/-- info: 'C3.RV32.P2v.p256VerifyPrehash_correct_pi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.P2v.p256VerifyPrehash_correct_pi

/-- info: 'C3.RV32.Pv.pvModel_none_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Pv.pvModel_none_inv

/-- info: 'C3.RV32.Pv.p384VerifyPrehash_correct_pi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Pv.p384VerifyPrehash_correct_pi

/-- info: 'C3.RV32.WP.callGenPI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.WP.callGenPI

/-- info: 'C3.RV32.Sv.sv_p2F' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Sv.sv_p2F

/-- info: 'C3.RV32.Ac.AcStagePI.acStage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Ac.AcStagePI.acStage

/-- info: 'C3.RV32.BootMainContract.Closure0ContractPI.weaken' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.BootMainContract.Closure0ContractPI.weaken

/-- info: 'C3.RV32.Cur.bootMain_correct_boots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bootMain_correct_boots

/-- info: 'C3.RV32.Cur.bootMainCorrect_of_pi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.bootMainCorrect_of_pi

/-- info: 'C3.RV32.Cur.reset_correct_loaded_boots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_correct_loaded_boots

/-- info: 'C3.RV32.Cur.resetCorrectLoaded_of_pi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.resetCorrectLoaded_of_pi

/-- info: 'C3.RV32.Cur.resetCorrectLoaded_np_of_pi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.resetCorrectLoaded_np_of_pi
