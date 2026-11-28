import C3BootProofs.Proofs.ResetPI
import C3BootProofs.Proofs.SramAlias
import C3BootProofs.Theorems.Formats
import C3BootProofs.Theorems.Trace

/-!
# Headline theorems

This file is the reader's entry point to the end-to-end bootloader proofs.
It composes the machine-code theorem from reset (`reset_correct_loaded_np`),
the eFuse level equivalence (`BootLevel.btPop_level`), the PMS eFuse-lock
postcondition (`EfuseLocked`), the signed-page bound (`mapped_pages_signed`),
and the SRAM-aliasing lift (`SramAlias.chip_run`) into two self-contained
statements:

* `headline_boot`: on the flat RV32IMC `Machine` model, started at `_start`
  (`RST`, `0x403A0000`) from any memory satisfying `Loaded M0`, `EfuseCtl`,
  `RomHyp`, the stack bound, and `InvBounds`, the bootloader either halts
  with a deliberate error code (`0xE1`–`0xE5`) or jumps to the exact entry
  point of a slot chosen by `decideBoot` with a sound slot check, having
  raised the eFuse security level to at least `target`, locked the eFuse
  controller via PMS, mapped only signed flash pages, and loaded RAM and
  MMU state according to `bootMem`.
* `headline_chip`: under the SRAM alias obligation `AliasOk`, the same
  guarantee holds on the aliased ESP32-C3 `Chip` model (`SramAlias.Chip`).
-/

namespace C3.Headline

open C3 C3.Image C3.RV32 C3.RV32.Cur C3.RV32.BootMainContract

/-- The security level stored in the eFuse `SECURE_VERSION` field (bits
14..29 of `efuseRd`), expressed via `Spec/Level`'s `level`. -/
def efuseLevel (M : Word → BitVec 8) : Nat :=
  level (Fuses.ofNat (((memLoad32 M efuseRd).toNat >>> 14) % 65536))

/-- `boot_main`'s bit-count `bmLevel` equals `Spec/Level`'s `efuseLevel`. -/
theorem bmLevel_eq_efuseLevel (M : Word → BitVec 8) : bmLevel M = efuseLevel M :=
  BootLevel.btPop_level (memLoad32 M efuseRd)

/-- **The jump state of a verified boot from reset.** At `m'`:
* `decideBoot` selects `(slot, target)` under a sound slot check `check`
  against the reset eFuse level `efuseLevel M0`;
* `slot` passes full TUF + Sigstore + manifest + image verification
  (`bmcAccept`), and its image header `h` decodes;
* every 64 KiB flash page mapped for any flash segment of `h` ends inside
  the signed image (`mf.image.length`);
* the eFuse level at the jump is at least `target`, no eFuse bits were
  cleared, and the eFuse PMS lock registers are configured and locked
  (`EfuseLocked m'.mem`);
* `m'.pc` is `h.entryPoint` (exact, since accepted entry points are even),
  `a0` holds the booted slot index, and memory outside `boot_main`'s stack
  and peripherals matches `bootMem`. -/
def HeadlineJump (flash : Nat → BitVec 8) (M0 : Word → BitVec 8) (R romStack : Nat) (m' : Machine) : Prop :=
  ∃ (check : Slot → Option Nat) (slot : Slot) (target : Nat) (mf : Manifest) (sv t : Nat)
    (h : ImageHeader) (Mb : Word → BitVec 8),
    (∀ s l, check s = some l →
      ∃ mf t, bmcAccept flash acPinnedRootData Ac.imagePolicy (efuseLevel M0)
        (BitVec.ofNat 32 (bmSlotNum s)) = some (mf, l, t)) ∧
    (decideBoot (bmRecs flash).1 (efuseLevel M0) check).outcome = .boot slot target ∧
    bmcAccept flash acPinnedRootData Ac.imagePolicy (efuseLevel M0)
      (BitVec.ofNat 32 (bmSlotNum slot)) = some (mf, sv, t) ∧
    decodeImageHeader (bmcImage flash (BitVec.ofNat 32 (bmSlotNum slot)) mf) mf.image.length = some h ∧
    (∀ s ∈ h.segments, s.kind.isFlash = true → ∀ k, k < s.length / flashPage →
      s.offset + (k + 1) * flashPage ≤ mf.image.length) ∧
    target ≤ efuseLevel m'.mem ∧
    (∃ X, memLoad32 m'.mem efuseRd = memLoad32 M0 efuseRd ||| X) ∧
    EfuseLocked m'.mem ∧
    m'.pc = BitVec.ofNat 32 h.entryPoint ∧
    reg m' a0 = BitVec.ofNat 32 (bmSlotNum slot) ∧
    BmKeep (resetMem M0) Mb (0x3FCDC700 - BitVec.ofNat 32 (bmK R romStack 0x5C10))
      (bmK R romStack 0x5C10) ∧
    HdrAt Mb (bmAcc 0x3FCDC700) h ∧
    ∀ x, Sep (0x3FCDC700 - BitVec.ofNat 32 (bmK R romStack 0x5C10)) (bmK R romStack 0x5C10) x 1 →
      (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat) →
      m'.mem x = bootMem flash Mb (bmAcc 0x3FCDC700)
        (BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset)) x

/-- **End-to-end bootloader theorem on `Machine` (panic-free under `InvBounds`).** -/
theorem headline_boot {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {R romStack : Nat}
    {romBase : Word} {romCode : List Nat}
    (L : Loaded M0) (ctl : EfuseCtl efuseProgramRunCode)
    (rom : RomHyp flash acPinnedRootData Ac.imagePolicy M0 R romStack romBase romCode)
    (hlo : 0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700)
    (hB : InvBounds) (m : Machine) (hm : m.mem = M0) (hpc : m.pc = RST) :
    HaltsDeliberately m ∨ ∃ m', Steps m m' ∧ HeadlineJump flash M0 R romStack m' := by
  rcases reset_correct_loaded_np L ctl rom hlo hB m hm hpc with hd | hb
  · exact .inl hd
  · obtain ⟨m', hs, check, slot, target, mf, sv, t, h, Mb, hchk, hdec, hacc, hhdr, hlev, rest⟩ := hb
    rw [bmLevel_eq_efuseLevel] at hchk hdec hacc
    exact .inr ⟨m', hs, check, slot, target, mf, sv, t, h, Mb, hchk, hdec, hacc, hhdr,
      fun _ hs' hf _ hk => mapped_pages_signed hhdr hs' hf hk, hlev, rest⟩

/-- **End-to-end bootloader theorem on the SRAM-aliased `Chip`**, under the
SRAM alias obligation `AliasOk`. -/
theorem headline_chip {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {R romStack : Nat}
    {romBase : Word} {romCode : List Nat}
    (L : Loaded M0) (ctl : EfuseCtl efuseProgramRunCode)
    (rom : RomHyp flash acPinnedRootData Ac.imagePolicy M0 R romStack romBase romCode)
    (hlo : 0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700)
    (hB : InvBounds) {m : Machine} {c : Chip}
    (hm : m.mem = M0) (hpc : m.pc = RST)
    (hc : ChipSim c m) (ok : ∀ m', Steps m m' → AliasOk m m') :
    (∃ code, Deliberate code ∧ ∃ m', Steps m m' ∧ HaltCode m' code ∧ ∃ c', Steps c c' ∧ ChipSim c' m') ∨
    (∃ m', Steps m m' ∧ HeadlineJump flash M0 R romStack m' ∧ ∃ c', Steps c c' ∧ ChipSim c' m') := by
  rcases headline_boot L ctl rom hlo hB m hm hpc with ⟨code, hdel, hw⟩ | hb
  · exact .inl ⟨code, hdel, chip_run hw ok hc⟩
  · exact .inr (chip_run hb ok hc)

end C3.Headline
