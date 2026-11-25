import C3BootProofs.Proofs.PanicFree
import C3BootProofs.Proofs.TufRoleKeysMet
import C3BootProofs.Proofs.SvSpec
import C3BootProofs.Proofs.ResetLoaded

/-!
# The refined contracts, from `RoleKeys::met` to reset

`PanicFree.lean` defines `InvBounds`, `PanicIf`, and `HaltOut`, and gives
the threading rule. This file states, as propositions, the contracts that
follow that rule, from `RoleKeys::met` up to `reset_correct_loaded`. Each
one is a current theorem's statement with its panic disjunct refined:

| Target | Refines | Panic disjunct |
|---|---|---|
| `TufRoleKeysMetRetPI` | `tufRoleKeysMet_ret` | `rmHI` for `rmH` |
| `Sv.SvVerifySpecPI` | `Sv.sv_verify_spec` | `PanicIf n` for `Panics n` |
| `Ac.AcStagePI` | `Ac.AcStage` | `¬ InvBounds ∧ Halting n'` for `Halting n'` |
| `BootMainContract.Closure0ContractPI` | `Closure0Contract` | `PanicIf m` for `Panics m` |
| `Cur.BootMainCorrectPI` | `Cur.bootMain_correct` | `HaltOut m` for `Panics m` |
| `Cur.ResetCorrectLoadedPI` | `Cur.reset_correct_loaded` | `HaltOut m` for `Panics m` |
| `Cur.ResetCorrectLoadedNP` | none: the panic-free headline | none, under `InvBounds` |

The theorems that prove them are to be named after the theorem they refine
with the suffix `_pi`, such as `tufRoleKeysMet_ret_pi :
TufRoleKeysMetRetPI`, and the headline `reset_correct_loaded_np :
ResetCorrectLoadedNP`. Four are stated beside the theorems that prove
them: `Sv.SvVerifySpecPI` in `SvSpec.lean` (`Sv.sv_verify_spec_pi`),
`TufRoleKeysMetRetPI` in `TufRoleKeysMet.lean` (`tufRoleKeysMet_ret_pi`),
`Ac.AcStagePI` in `AcceptStages.lean`, and
`BootMainContract.Closure0ContractPI` in `AcceptSpec.lean`
(`Ac.acs_contract_pi`).

`Cur.BootsSlot` is the boot outcome that `bootMain_correct` and
`reset_correct_loaded` share; `bootMain_correct_boots` and
`reset_correct_loaded_boots` check that it is theirs. This file proves the
weakenings: each refined contract gives the current statement, and
`resetCorrectLoaded_np_of_pi` gives the headline from
`ResetCorrectLoadedPI`.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-- **The machine boots a slot**: from `m`, it reaches the entry point of
the slot that `decideBoot` boots with a sound slot check, as
`bootMain_correct` and `reset_correct_loaded` say. The eFuse level and the
records come from memory `Ml`, and the memory `Mb` that `boot` loads from
keeps `Mk` outside the `K`-byte stack below `top`. -/
def BootsSlot (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (Ml Mk : Word → BitVec 8)
    (top : Word) (K : Nat) (m : Machine) : Prop :=
  ∃ m', Steps m m' ∧
    ∃ (check : Slot → Option Nat) (slot : Slot) (target : Nat) (mf : Manifest) (sv t : Nat) (h : ImageHeader)
      (Mb : Word → BitVec 8),
      (∀ s l, check s = some l →
        ∃ mf t, bmcAccept flash pinned policy (bmLevel Ml) (BitVec.ofNat 32 (bmSlotNum s)) = some (mf, l, t)) ∧
      (decideBoot (bmRecs flash).1 (bmLevel Ml) check).outcome = .boot slot target ∧
      bmcAccept flash pinned policy (bmLevel Ml) (BitVec.ofNat 32 (bmSlotNum slot)) = some (mf, sv, t) ∧
      decodeImageHeader (bmcImage flash (BitVec.ofNat 32 (bmSlotNum slot)) mf) mf.image.length = some h ∧
      target ≤ level (Fuses.ofNat (((memLoad32 m'.mem efuseRd).toNat >>> 14) % 65536)) ∧
      (∃ X, memLoad32 m'.mem efuseRd = memLoad32 Ml efuseRd ||| X) ∧
      m'.pc = BitVec.ofNat 32 h.entryPoint &&& ~~~1 ∧
      reg m' a0 = BitVec.ofNat 32 (bmSlotNum slot) ∧
      BmKeep Mk Mb (top - BitVec.ofNat 32 K) K ∧
      HdrAt Mb (bmAcc top) h ∧
      ∀ x, Sep (top - BitVec.ofNat 32 K) K x 1 →
        (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat) →
        m'.mem x = bootMem flash Mb (bmAcc top)
          (BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset)) x

/-- `bootMain_correct`'s conclusion is `Panics m ∨ BootsSlot …`. -/
theorem bootMain_correct_boots {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy}
    {M0 : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    (m : Machine) (hm : m.mem = M0) (hpc : m.pc = BM) (hsp : reg m sp = top) :
    Panics m ∨ BootsSlot flash pinned policy M0 M0 top (bmK R romStack stack0) m :=
  bootMain_correct X m hm hpc hsp

/-- **`bootMain_correct` with its halt refined**: given `BmHyp` and the
refined contract of the first closure, `boot_main` halts at a deliberate
`halt`, panics only if an inversion bound fails, or boots a slot. -/
def BootMainCorrectPI : Prop :=
  ∀ {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy}
    {M0 : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (_X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    (_c0 : Closure0ContractPI flash R romBase romCode pinned policy stack0 E)
    (m : Machine) (_hm : m.mem = M0) (_hpc : m.pc = BM) (_hsp : reg m sp = top),
    HaltOut m ∨ BootsSlot flash pinned policy M0 M0 top (bmK R romStack stack0) m

theorem bootMainCorrect_of_pi (h : BootMainCorrectPI) {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy}
    {M0 : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    (c0 : Closure0ContractPI flash R romBase romCode pinned policy stack0 E)
    (m : Machine) (hm : m.mem = M0) (hpc : m.pc = BM) (hsp : reg m sp = top) :
    Panics m ∨ BootsSlot flash pinned policy M0 M0 top (bmK R romStack stack0) m :=
  (h X c0 m hm hpc hsp).imp_left HaltOut.panics

/-- `reset_correct_loaded`'s conclusion is `Panics m ∨ BootsSlot …`. -/
theorem reset_correct_loaded_boots {flash : Nat → BitVec 8}
    {M0 : Word → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat} (L : Loaded M0)
    (ctl : EfuseCtl efuseProgramRunCode) (rom : RomHyp flash acPinnedRootData Ac.imagePolicy M0 R romStack romBase romCode)
    (hlo : 0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700)
    (m : Machine) (hm : m.mem = M0) (hpc : m.pc = RST) :
    Panics m ∨ BootsSlot flash acPinnedRootData Ac.imagePolicy M0 (resetMem M0) 0x3FCDC700
      (bmK R romStack 0x5C10) m :=
  reset_correct_loaded L ctl rom hlo m hm hpc

/-- **`reset_correct_loaded` with its halt refined**: from reset, with the
same hypotheses, the bootloader halts at a deliberate `halt`, panics only if
an inversion bound fails, or boots a slot. -/
def ResetCorrectLoadedPI : Prop :=
  ∀ {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat}
    (_L : Loaded M0) (_ctl : EfuseCtl efuseProgramRunCode)
    (_rom : RomHyp flash acPinnedRootData Ac.imagePolicy M0 R romStack romBase romCode)
    (_hlo : 0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700)
    (m : Machine) (_hm : m.mem = M0) (_hpc : m.pc = RST),
    HaltOut m ∨ BootsSlot flash acPinnedRootData Ac.imagePolicy M0 (resetMem M0) 0x3FCDC700
      (bmK R romStack 0x5C10) m

/-- **The bootloader never panics, given the inversion bounds.** From
reset, with `reset_correct_loaded`'s hypotheses and `InvBounds`, the
bootloader halts at a `halt` call with a deliberate code (0xE1 to 0xE5), or
boots a slot that `decideBoot` boots with a sound slot check. -/
def ResetCorrectLoadedNP : Prop :=
  ∀ {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat}
    (_L : Loaded M0) (_ctl : EfuseCtl efuseProgramRunCode)
    (_rom : RomHyp flash acPinnedRootData Ac.imagePolicy M0 R romStack romBase romCode)
    (_hlo : 0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700) (_hB : InvBounds)
    (m : Machine) (_hm : m.mem = M0) (_hpc : m.pc = RST),
    HaltsDeliberately m ∨ BootsSlot flash acPinnedRootData Ac.imagePolicy M0 (resetMem M0) 0x3FCDC700
      (bmK R romStack 0x5C10) m

theorem resetCorrectLoaded_of_pi (h : ResetCorrectLoadedPI) {flash : Nat → BitVec 8}
    {M0 : Word → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat} (L : Loaded M0)
    (ctl : EfuseCtl efuseProgramRunCode) (rom : RomHyp flash acPinnedRootData Ac.imagePolicy M0 R romStack romBase romCode)
    (hlo : 0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700)
    (m : Machine) (hm : m.mem = M0) (hpc : m.pc = RST) :
    Panics m ∨ BootsSlot flash acPinnedRootData Ac.imagePolicy M0 (resetMem M0) 0x3FCDC700
      (bmK R romStack 0x5C10) m :=
  (h L ctl rom hlo m hm hpc).imp_left HaltOut.panics

theorem resetCorrectLoaded_np_of_pi (h : ResetCorrectLoadedPI) : ResetCorrectLoadedNP :=
  fun L ctl rom hlo hB m hm hpc => (h L ctl rom hlo m hm hpc).imp_left (HaltOut.np hB)

end C3.RV32.Cur
