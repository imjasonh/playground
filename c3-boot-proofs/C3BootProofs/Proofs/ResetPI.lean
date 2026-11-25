import C3BootProofs.Proofs.PanicFreeTargets

/-!
# `boot_main` and reset, with their halts

`bootMain_correct_pi` proves `BootMainCorrectPI`: `boot_main`'s own halts
are the deliberate ones, 0xE4 at 0xD2 when a boot-state record can't be
read and 0xE5 at 0x270 when neither slot passes, and `boot`'s are 0xE1 at
0x29C when the raised eFuse level doesn't read back and 0xE2 at 0x290 when
a flash read of the image fails. Its only panic is the first closure's,
which `Closure0ContractPI` allows only when an inversion bound fails.

`reset_correct_loaded_pi` proves `ResetCorrectLoadedPI` from
`AcsContractPI`, the refined form of the first closure's contract
`Ac.acs_contract`, with that theorem's hypotheses. `Ac.acs_contract_pi`
proves that contract, so `reset_correct_loaded_np` states the headline
without panics, under the inversion bounds.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

theorem bootMain_correct_pi : BootMainCorrectPI :=
  fun X c0 m hm hpc hsp => bootMain_correct_q (Q := ¬ InvBounds) ⟨X, c0⟩ m hm hpc hsp

/-- **The first closure's refined contract**, from `Ac.acs_contract`'s
hypotheses: the closure's contract with 0x5C10 bytes of stack and memory
condition `AcsE`, whose panic disjunct is `PanicIf`. -/
def AcsContractPI : Prop :=
  ∀ {flash : Nat → BitVec 8} {R romStack : Nat} {romBase : Word} {romCode : List Nat} {pinned : Bytes}
    {policy : Policy} (_log : RomFn romBase romCode 0x40000040 romStack fun _ => True) (_hrs : romStack ≤ 0x3A50)
    (_hR : R ≤ 0x3A50 - 0x180) (_hR4 : R % 4 = 0) (_rb : 0x40000000 ≤ romBase.toNat)
    (_rl : romBase.toNat + romCode.length ≤ 2 ^ 32),
    Closure0ContractPI flash R romBase romCode pinned policy 0x5C10 (Ac.AcsE romBase romCode pinned policy)

/-- **`reset_correct_loaded` with its halts refined**, given the first
closure's refined contract: from reset, the bootloader halts at a
deliberate `halt`, panics only if an inversion bound fails, or boots a
slot. -/
theorem reset_correct_loaded_pi (hacs : AcsContractPI) : ResetCorrectLoadedPI := by
  intro flash M0 R romStack romBase romCode L ctl rom hlo m hm hpc
  have c0 : Closure0ContractPI flash R romBase romCode acPinnedRootData Ac.imagePolicy 0x5C10
      (Ac.AcsE romBase romCode acPinnedRootData Ac.imagePolicy) :=
    hacs rom.log (by unfold bmK at hlo; omega) (by unfold bmK at hlo; omega) rom.hR rom.hrb
      (by have := rom.hrl; omega)
  have X := loaded_bmHyp L ctl rom c0.weaken
    (fun _ hK => Ac.acl_acsE (loaded_resetMem L) (reset_codeIn rom.code rom.hrb rom.hrl) rom.hrb
      (by have := rom.hrl; omega) fun x hx => hK x (rl_stackSep hlo hx) (rl_ptrSep rom hx))
    hlo
  exact reset_correct_q (Q := ¬ InvBounds) (loaded_rstCode L) ⟨X, c0⟩ m hm hpc

/-- **The panic-free headline.** From reset, with `reset_correct_loaded`'s
hypotheses and the inversion bounds `InvBounds`, the bootloader halts at a
`halt` call with a deliberate code, or boots a slot that `decideBoot` boots
with a sound slot check. -/
theorem reset_correct_loaded_np : ResetCorrectLoadedNP :=
  resetCorrectLoaded_np_of_pi
    (reset_correct_loaded_pi fun log hrs hR hR4 rb rl => Ac.acs_contract_pi log hrs hR hR4 rb rl)

end C3.RV32.Cur
