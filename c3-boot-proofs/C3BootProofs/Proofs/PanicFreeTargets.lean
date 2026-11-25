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
ResetCorrectLoadedNP`.

`Cur.BootsSlot` is the boot outcome that `bootMain_correct` and
`reset_correct_loaded` share; `bootMain_correct_boots` and
`reset_correct_loaded_boots` check that it is theirs. This file proves the
weakenings: each refined contract gives the current statement, and
`resetCorrectLoaded_np_of_pi` gives the headline from
`ResetCorrectLoadedPI`.
-/

namespace C3.RV32

open C3.Image C3.Json

/-- `rmH`, the `RoleKeys::met` postcondition's halting case, when some
inversion bound fails. -/
abbrev rmHI : Post := fun pc M g => ¬ InvBounds ∧ rmH pc M g

/-- **`tufRoleKeysMet_ret` with its panic refined**: `RoleKeys::met` halts
only if an inversion bound fails (`rmHI`), or it returns as
`tufRoleKeysMet_ret` says. `tufRoleKeysMet_correct`, `tufRoleKeysMet_spec`,
and `tufRoleKeysMet_result` refine the same way. -/
def TufRoleKeysMetRetPI : Prop :=
  ∀ (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat} {es : List RkEntry}
    (_hpc : m.pc = TRM) (_ha0 : reg m a0 = R) (_ha1 : reg m a1 = A) (_hsp : reg m sp = s + BitVec.ofNat 32 0x3920)
    (_hra : reg m ra = retAddr) (_hret : retAddr &&& ~~~1 = retAddr) (_hal : s.toNat % 16 = 0)
    (_hlo : 0x3FC80000 ≤ s.toNat) (_hhi : s.toNat + 0x3920 ≤ 0x3FCE0000)
    (_hds : Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize))
    (_hro : Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize))
    (_hc : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = m.mem x) → RmCode M)
    (_halR : R.toNat % 4 = 0) (_hRw : R.toNat + 0x540 ≤ 0x40000000) (_hSR : Sep s 0x3920 R 0x540)
    (_hMw : MP.toNat + ML ≤ 0x40000000) (_hML : ML < 2 ^ 31) (_hSM : Sep s 0x3920 MP ML)
    (_hS0 : SP.toNat ≠ 0) (_hSw : SP.toNat + SL ≤ 0x40000000) (_hSL : SL < 2 ^ 31) (_hSS : Sep s 0x3920 SP SL)
    (_halA : A.toNat % 4 = 0) (_hSA : Sep s 0x3920 A 16) (_hA0 : memLoad32 m.mem A = MP)
    (_hA4 : memLoad32 m.mem (A + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML)
    (_hA8 : memLoad32 m.mem (A + BitVec.ofNat 32 8) = SP)
    (_hAC : memLoad32 m.mem (A + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL) (_hR : RkAt m.mem R t es) (_hw : RkWf es),
    ∃ m', Steps m m' ∧
        (rmHI m'.pc m'.mem (reg m') ∨
          (m'.pc = retAddr ∧ (∀ x, Sep x 1 s 0x3920 → m'.mem x = m.mem x) ∧ (∀ r, r ∉ jClob → reg m' r = reg m r) ∧
            (reg m' a0 = 0 → reg m' a1 ≠ 0 →
              MetSound (memBytes m.mem SP SL) (memBytes m.mem MP ML) t (es.map nbE)) ∧
            (reg m' a0 = 0 ∨ reg m' a0 = 1) ∧ (reg m' a0 ≠ 0 → (reg m' a1 &&& 0xFF).toNat < 0x27)))

end C3.RV32

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd C3.RV32.P2v

/-- **`sv_verify_spec` with its panic refined**: `sigstore::verify` returns
`Err`, panics only if an inversion bound fails, or computes
`sigstoreVerify`. -/
def SvVerifySpecPI : Prop :=
  ∀ {Me : Word → BitVec 8} {n : Machine} {B : Word} {bundle : Bundle} {root : SigstoreRoot}
    (_Bd : SvBundleAt B Me (reg n a1) bundle) (_R : SvRootAt B Me (reg n a2) root)
    (_C : CodeIn Me SV sigstoreVerifyCode)
    (_E : SvCode Me)
    (_FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (_s : St Me SV n 0 (reg n))
    (_rsp : reg n sp = B + 0x2660)
    (_hret : ((fun k => reg n (savedReg k))) 0 &&& ~~~1 = ((fun k => reg n (savedReg k))) 0)
    (_hO : SvOut B (reg n a0))
    (_D0 : P2Data Me)
    (_SD0 : SvData Me)
    (_HE0 : HfEnv Me)
    (_RS : SvRoSep B)
    (_PE0 : PvEnv7 Me)
    (_PE0' : P2vEnv Me)
    (_dg_in : SvIn B (reg n a3) 32)
    (_S2 : SvSha2Code Me)
    (_CK0 : SvCkCode Me)
    (_EE0 : EvEnv Me)
    (_hiv : (s5Hv Me (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (_RK0 : SvRkCode Me)
    (_hOk : SvOutOk B (reg n a0))
    (_OD : SvOidData Me)
    (_ND : CodeIn Me (BitVec.ofNat 32 b2sOrder256Address) b2sOrder256Data)
    (_UD : CodeIn Me (BitVec.ofNat 32 p256OneAddress) p256OneData)
    (_LD : CodeIn Me (BitVec.ofNat 32 edOrderAddress) edOrderData)
    (_PD : CodeIn Me (BitVec.ofNat 32 edPrimeAddress) edPrimeData)
    (_PmD : CodeIn Me (BitVec.ofNat 32 edPm1Address) edPm1Data)
    (_E1D : CodeIn Me (BitVec.ofNat 32 edOneAddress) edOneData)
    (_EdD : CodeIn Me (BitVec.ofNat 32 edDAddress) edDData)
    (_SmD : CodeIn Me (BitVec.ofNat 32 edSqrtM1Address) edSqrtM1Data)
    (_D2D : CodeIn Me (BitVec.ofNat 32 edwardsD2Address) edwardsD2Data)
    (_BsD : CodeIn Me (BitVec.ofNat 32 edBaseAddress) edBaseData)
    (_KRD : CodeIn Me (BitVec.ofNat 32 edMontRAddress) edMontRData)
    (_KRRD : CodeIn Me (BitVec.ofNat 32 edMontRRAddress) edMontRRData)
    (_RD : SvRekorData Me),
    SvErrRet B (reg n a0) (fun k => reg n (savedReg k)) n ∨ PanicIf n ∨
      ∃ v, sigstoreVerify bundle root (memBytes Me (reg n a3) 32) = some v ∧
        SvOkRet B (reg n a0) (fun k => reg n (savedReg k)) n (BitVec.ofNat 32 (v.signedTime % 2 ^ 32))
          (BitVec.ofNat 32 (v.signedTime / 2 ^ 32)) (BitVec.ofNat 32 (v.logIndex % 2 ^ 32))
          (BitVec.ofNat 32 (v.logIndex / 2 ^ 32))

end C3.RV32.Sv

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

/-- **`AcStage` with its halt refined**: from `n0`, the closure halts only
if an inversion bound fails, reaches an exit, or reaches offset `o'` in a
state that `Q` holds of. -/
def AcStagePI (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (n0 : Machine) (o' : Nat)
    (Q : Machine → Prop) : Prop :=
  ∃ n', Steps n0 n' ∧ ((¬ InvBounds ∧ Halting n') ∨
    (AcInv B Bf g t v M0 n' ∧ (AcFail B r n' ∨ (n'.pc = AC + BitVec.ofNat 32 o' ∧ Q n'))))

theorem AcStagePI.acStage {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n0 : Machine}
    {o' : Nat} {Q : Machine → Prop} (h : AcStagePI B Bf g t r v M0 n0 o' Q) : AcStage B Bf g t r v M0 n0 o' Q :=
  let ⟨n', c, hn⟩ := h; ⟨n', c, hn.imp_left And.right⟩

end C3.RV32.Ac

namespace C3.RV32.BootMainContract

open C3 C3.Image C3.RV32.Cur

/-- **`Closure0Contract` with its panic refined**: the closure returns as
`Closure0Contract` says, or it panics, and then some inversion bound
fails. -/
def Closure0ContractPI (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat)
    (pinned : Bytes) (policy : Policy) (stack : Nat) (E : (Word → BitVec 8) → Prop) : Prop :=
  RomRead flash R romBase romCode →
  ∀ (m : Machine) (res bufs slot level : Word),
    CodeIn m.mem (BitVec.ofNat 32 bootMainClosure0Address) bootMainClosure0Code → E m.mem →
    m.pc = BitVec.ofNat 32 bootMainClosure0Address → stack ≤ (reg m sp).toNat →
    reg m a0 = res → reg m a1 = level → reg m a2 = bufs → reg m a3 = slot → slot.toNat < 2 →
    C0Args stack (reg m sp) res bufs level (reg m ra) →
    Sep res 0x12C bufs 0xB954 → Sep res 0x12C (reg m sp - BitVec.ofNat 32 stack) stack →
    Sep bufs 0xB954 (reg m sp - BitVec.ofNat 32 stack) stack →
    (∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
      (∀ x, Sep (reg m sp - BitVec.ofNat 32 stack) stack x 1 → Sep res 0x12C x 1 →
        Sep bufs 0xB954 x 1 → m'.mem x = m.mem x) ∧
      (m'.mem (res + 0xC) = 0xFF ∨
        ∃ mf sv t, bmcAccept flash pinned policy level.toNat slot = some (mf, sv, t) ∧
          m'.mem (res + 0xC) ≠ 0xFF ∧ m'.mem (res + 0x128) = BitVec.ofNat 8 sv ∧
          memLoad32 m'.mem (res + 0x120) = BitVec.ofNat 32 (bmcBase slot + mf.image.offset) ∧
          AccOk flash slot mf m'.mem res)) ∨
    PanicIf m

theorem Closure0ContractPI.weaken {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat}
    {pinned : Bytes} {policy : Policy} {stack : Nat} {E : (Word → BitVec 8) → Prop}
    (h : Closure0ContractPI flash R romBase romCode pinned policy stack E) :
    Closure0Contract flash R romBase romCode pinned policy stack E :=
  fun hr m res bufs slot level h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
    (h hr m res bufs slot level h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13).imp_right PanicIf.panics

end C3.RV32.BootMainContract

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
