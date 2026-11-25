import C3BootProofs.Proofs.Reset
import C3BootProofs.Proofs.LoadedImage
import C3BootProofs.Proofs.AcceptLoaded

/-!
# From the memory that the ROM loader leaves

`reset_correct` takes the code of every function that runs as hypotheses
about the memory `M0` at reset (`RstCode M0`, and `BmHyp`'s `BmEnv`).
This file derives all of them from `Loaded M0`, which says that `M0` holds
the pinned image's pieces at their link addresses, so that
`reset_correct_loaded` assumes only `Loaded M0`, the eFuse controller's
contract, the ROM (`RomHyp`), how much stack the ROM routines use, and the
two facts about the first closure that `acs_contract` still assumes.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

theorem loaded_rstCode {M : Word → BitVec 8} (h : Loaded M) : RstCode M :=
  ⟨h.startEntry, h.setupFn, h.watchdogArm, h.clockRun160⟩

theorem loaded_bsCode {M : Word → BitVec 8} (h : Loaded M) : BSCode M :=
  ⟨h.bootstateDecode, h.crc32, h.readerMagic, h.readerArray4, h.readerBytes, h.readerVersion1, h.readerU16,
    h.readerReserved, h.readerU32, h.readerU8⟩

theorem loaded_memcpyBody {M : Word → BitVec 8} (h : Loaded M) :
    CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode := by
  have e : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word) = BitVec.ofNat 32 memcpyBodyAddress := by decide
  rw [e]; exact h.memcpyBody

theorem loaded_bwCode {M : Word → BitVec 8} (h : Loaded M) : BWCode M :=
  ⟨h.bootMainClosure1, h.memset, h.copyFromSliceU8, h.memcpyStub, loaded_memcpyBody h, h.crc32, h.bsMagic,
    h.bsVersion⟩

theorem loaded_panicCode {M : Word → BitVec 8} (h : Loaded M) : PanicCode M := by
  intro p hp
  simp only [panicFns, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.halt
  · exact h.beginUnwind
  · exact h.panicFmt
  · exact h.assertFailedInner
  · exact h.corePanic
  · exact h.panicBoundsCheck
  · exact h.expectFailed
  · exact h.unwrapFailed
  · exact h.lenMismatchFail
  · exact h.sliceIndexFail
  · exact h.assertFailedUsize
  · exact h.assertFailedU8

/-- `efuse_program_run`'s code from the image, with the eFuse controller's
contract for it. -/
theorem loaded_eprAt {M : Word → BitVec 8} (h : Loaded M) (ctl : EfuseCtl efuseProgramRunCode) : EprAt M :=
  ⟨efuseProgramRunCode, h.efuseProgramRun, by decide, ctl⟩

/-- The reset path keeps the image: `resetMem` changes only the stack word
at 0x3FCDC70C and peripheral registers. -/
theorem loaded_resetMem {M0 : Word → BitVec 8} (h : Loaded M0) : Loaded (resetMem M0) :=
  h.congr fun x hx => resetMem_out M0 x (by omega) (by omega) (by omega)

theorem reset_codeIn {M0 : Word → BitVec 8} {b : Word} {c : List Nat} (h : CodeIn M0 b c)
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + c.length ≤ 0x60000000) : CodeIn (resetMem M0) b c := fun i hi => by
  have e : (b + BitVec.ofNat 32 i).toNat = b.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [resetMem_out M0 _ (.inr (by omega)) (.inl (by omega)) (.inl (by omega))]
  exact h i hi

/-- The reset path keeps the ROM's flash-chip pointer word at 0x3FCDFFF0. -/
theorem reset_bmPtr (M0 : Word → BitVec 8) : memLoad32 (resetMem M0) bmPtr = memLoad32 M0 bmPtr :=
  memLoad32_congr fun j hj => by
    have e : (bmPtr + BitVec.ofNat 32 j).toNat = 0x3FCDFFF0 + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show bmPtr.toNat = 0x3FCDFFF0 from rfl]; omega
    exact resetMem_out M0 (bmPtr + BitVec.ofNat 32 j) (.inr (by omega)) (.inl (by omega)) (.inl (by omega))

theorem reset_decision (flash : Nat → BitVec 8) (M0 : Word → BitVec 8) (c : Slot → Option Nat) :
    bmDecision flash (resetMem M0) c = bmDecision flash M0 c := by
  unfold bmDecision; rw [reset_level]

theorem reset_sound (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (M0 : Word → BitVec 8)
    (c : Slot → Option Nat) : BmSound flash pinned policy (resetMem M0) c = BmSound flash pinned policy M0 c := by
  unfold BmSound; rw [reset_level]

/-- **What `reset_correct_loaded` assumes of the ROM**, with memory `M0` at
reset: its code `romCode` at `romBase`, between 0x40000000 and the
peripheral registers; its flash reads (`RomRead`), which use `R` bytes of
stack, at most 0x38D0; the routines that `boot_main` and its callees call,
each within `romStack` bytes of stack, at most 0x3A50, where the write routine may only be entered with
the record that `bmDecision` writes for a sound slot check and the erase
routine with that copy's sector; and the flash-chip pointer that the ROM
keeps at 0x3FCDFFF0, word-aligned and pointing below 0x40000000 and above
the image's read-only data. -/
structure RomHyp (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (M0 : Word → BitVec 8)
    (R romStack : Nat) (romBase : Word) (romCode : List Nat) : Prop where
  code : CodeIn M0 romBase romCode
  hrb : 0x40000000 ≤ romBase.toNat
  hrl : romBase.toNat + romCode.length ≤ 0x60000000
  read : RomRead flash R romBase romCode
  log : RomFn romBase romCode 0x40000040 romStack fun _ => True
  unlock : RomFn romBase romCode 0x40000140 romStack fun _ => True
  erase : RomFn romBase romCode 0x40000128 romStack fun n => reg n a0 = bwAddr (bmCopy (bmRecs flash).2) >>> 12
  write : RomFn romBase romCode 0x4000012C romStack fun n =>
    reg n a0 = bwAddr (bmCopy (bmRecs flash).2) ∧ reg n a2 = 32 ∧
      ∃ w, (∃ c, BmSound flash pinned policy M0 c ∧ (bmDecision flash M0 c).write = some w) ∧
        decodeRecord ((List.range 32).map fun i => (n.mem (reg n a1 + BitVec.ofNat 32 i)).toNat) = some w
  suspend : RomFn romBase romCode 0x40000524 romStack fun _ => True
  invalidate : RomFn romBase romCode 0x400004D8 romStack fun _ => True
  resume : RomFn romBase romCode 0x40000528 romStack fun _ => True
  hR : R % 4 = 0
  hrs : 16 ≤ romStack
  hrs4 : romStack % 4 = 0
  hpa : (memLoad32 M0 bmPtr).toNat % 4 = 0
  hpl : 0x3FCC8000 ≤ (memLoad32 M0 bmPtr).toNat + 4
  hph : (memLoad32 M0 bmPtr).toNat + 8 ≤ 0x40000000

/-- `BmHyp` at `boot_main`'s entry, from the image, the eFuse contract, the
ROM, and the first closure's contract. -/
theorem loaded_bmHyp {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat} {E : (Word → BitVec 8) → Prop}
    (L : Loaded M0) (ctl : EfuseCtl efuseProgramRunCode) (rom : RomHyp flash pinned policy M0 R romStack romBase romCode)
    (c0 : Closure0Contract flash R romBase romCode pinned policy stack0 E)
    (hE : ∀ M, BmKeep (resetMem M0) M (0x3FCDC700 - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) →
      E M)
    (hlo : 0x3FCC8000 + bmK R romStack stack0 ≤ 0x3FCDC700) :
    BmHyp flash pinned policy (resetMem M0) 0x3FCDC700 R romStack stack0 romBase romCode E := by
  have L' := loaded_resetMem L
  refine ⟨⟨L'.bootMain, L'.memset, L'.memcpyStub, loaded_memcpyBody L', L'.flashRead, L'.romFlashReadWords,
    loaded_bsCode L', loaded_bwCode L', L'.bootMainClosure0, L'.bootFn, loaded_eprAt L' ctl, loaded_panicCode L',
    reset_codeIn rom.code rom.hrb rom.hrl, rom.hrb, rom.hrl, by decide, hlo, by decide, rom.hR, rom.hrs, rom.hrs4,
    ?_, ?_, ?_⟩, rom.read, rom.log, rom.unlock, rom.erase, ?_, rom.suspend, rom.invalidate, rom.resume, c0, hE⟩
  · rw [reset_bmPtr]; exact rom.hpa
  · rw [reset_bmPtr]; exact rom.hpl
  · rw [reset_bmPtr]; exact rom.hph
  · simp only [reset_decision, reset_sound]; exact rom.write

/-- Memory outside RAM is outside `boot_main`'s stack. -/
theorem rl_stackSep {K : Nat} (hlo : 0x3FCC8000 + K ≤ 0x3FCDC700) {x : Word} (hx : Ac.AcsOutRam x) :
    Sep (0x3FCDC700 - BitVec.ofNat 32 K) K x 1 := by
  have e : (0x3FCDC700 - BitVec.ofNat 32 K : Word).toNat = 0x3FCDC700 - K := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp only [BitVec.reduceToNat]; omega
  exact (Ac.acs_ram_sep (by omega) (by omega) hx).symm

/-- Memory outside RAM is outside the ROM's flash-size word. -/
theorem rl_ptrSep {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {R romStack : Nat} {romBase : Word} {romCode : List Nat} (rom : RomHyp flash pinned policy M0 R romStack romBase romCode)
    {x : Word} (hx : Ac.AcsOutRam x) : Sep (memLoad32 (resetMem M0) bmPtr + 4) 4 x 1 := by
  have := rom.hpl; have := rom.hph
  have e : (memLoad32 (resetMem M0) bmPtr + 4 : Word).toNat = (memLoad32 M0 bmPtr).toNat + 4 := by
    rw [reset_bmPtr, BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
  exact (Ac.acs_ram_sep (by omega) (by omega) hx).symm

/-- **The bootloader boots only what `decideBoot` boots, from the memory
that the ROM loader leaves.** `reset_correct`, with its code hypotheses
derived from `Loaded M0`.

What the theorem assumes:

* `Loaded M0`: the ROM loader has copied the pinned image's segments to
  RAM, so `M0` holds every extracted function and piece of read-only data
  at its link address.
* `ctl`: the eFuse controller meets `EfuseCtl` through the image's
  `efuse_program_run`.
* `rom`: the ROM's code, flash reads, and routines, and its flash-chip
  pointer (`RomHyp`).
* `hlo`: the `bmK R romStack 0x5C10` bytes of stack below 0x3FCDC700 that
  `boot_main`, the ROM, and the first closure use stay above the image's
  read-only data, which ends below 0x3FCC8000.

The pinned root and the policy are the image's, `acPinnedRootData` and
`imagePolicy`. The conclusion is `reset_correct`'s. -/
theorem reset_correct_loaded {flash : Nat → BitVec 8}
    {M0 : Word → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat} (L : Loaded M0)
    (ctl : EfuseCtl efuseProgramRunCode) (rom : RomHyp flash acPinnedRootData Ac.imagePolicy M0 R romStack romBase romCode)
    (hlo : 0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700)
    (m : Machine) (hm : m.mem = M0) (hpc : m.pc = RST) :
    Panics m ∨ ∃ m', Steps m m' ∧
      ∃ (check : Slot → Option Nat) (slot : Slot) (target : Nat) (mf : Manifest) (sv t : Nat) (h : ImageHeader)
        (Mb : Word → BitVec 8),
        (∀ s l, check s = some l →
          ∃ mf t, bmcAccept flash acPinnedRootData Ac.imagePolicy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum s)) = some (mf, l, t)) ∧
        (decideBoot (bmRecs flash).1 (bmLevel M0) check).outcome = .boot slot target ∧
        bmcAccept flash acPinnedRootData Ac.imagePolicy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum slot)) = some (mf, sv, t) ∧
        decodeImageHeader (bmcImage flash (BitVec.ofNat 32 (bmSlotNum slot)) mf) mf.image.length = some h ∧
        target ≤ level (Fuses.ofNat (((memLoad32 m'.mem efuseRd).toNat >>> 14) % 65536)) ∧
        (∃ X, memLoad32 m'.mem efuseRd = memLoad32 M0 efuseRd ||| X) ∧
        m'.pc = BitVec.ofNat 32 h.entryPoint &&& ~~~1 ∧
        reg m' a0 = BitVec.ofNat 32 (bmSlotNum slot) ∧
        BmKeep (resetMem M0) Mb (0x3FCDC700 - BitVec.ofNat 32 (bmK R romStack 0x5C10))
          (bmK R romStack 0x5C10) ∧
        HdrAt Mb (bmAcc 0x3FCDC700) h ∧
        ∀ x, Sep (0x3FCDC700 - BitVec.ofNat 32 (bmK R romStack 0x5C10)) (bmK R romStack 0x5C10) x 1 →
          (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat) →
          m'.mem x = bootMem flash Mb (bmAcc 0x3FCDC700)
            (BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset)) x :=
  reset_correct (loaded_rstCode L)
    (loaded_bmHyp L ctl rom
      (Ac.acs_contract rom.log (by unfold bmK at hlo; omega) (by unfold bmK at hlo; omega) rom.hR rom.hrb
        (by have := rom.hrl; omega))
      (fun _ hK => Ac.acl_acsE (loaded_resetMem L) (reset_codeIn rom.code rom.hrb rom.hrl) rom.hrb
        (by have := rom.hrl; omega) fun x hx => hK x (rl_stackSep hlo hx) (rl_ptrSep rom hx))
      hlo) m hm hpc

/-! ## The stack bound `hlo`

Between the read-only data's end at 0x3FCC8000 and the stack top at
0x3FCDC700 there are 0x14700 bytes. `boot_main` takes 0xBE80 of them for
its frame and 0x150 for the deepest frame it opens on the way to a callee,
which leaves 0x8730 bytes for `R`, `romStack`, and `stack0`. -/

/-- `hlo` holds when the ROM's flash-read stack `R`, its other routines'
stack `romStack`, and the first closure's stack `stack0` total at most
0x8730 bytes. -/
theorem reset_hlo {R romStack stack0 : Nat} (h : R + romStack + stack0 ≤ 0x8730) :
    0x3FCC8000 + bmK R romStack stack0 ≤ 0x3FCDC700 := by
  have e : 0x3FCC8000 + bmK R romStack stack0 = 0x3FCD3FD0 + (R + romStack + stack0) := by
    simp only [bmK, ← Nat.add_assoc]
  rw [e]
  exact Nat.add_le_add_left h 0x3FCD3FD0

/-- `hlo` with the first closure's stack at 0x5C10 bytes, the most that its
stages use below its frame's top (`AcceptSlot.lean`): the ROM's flash
read and its other routines may then use 0x2B20 bytes together. The
closure's stages separately need `R ≤ 0x38D0` and a `printf` stack of at
most 0x3A50 bytes, which this bound implies. -/
theorem reset_hlo_c0 {R romStack : Nat} (h : R + romStack ≤ 0x2B20) :
    0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700 :=
  reset_hlo (Nat.add_le_add_right h 0x5C10)

end C3.RV32.Cur
