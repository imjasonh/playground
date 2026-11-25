import C3BootProofs.Proofs.Boot
import C3BootProofs.Spec.Accept

/-!
# The contract of `boot_main`'s first closure

`boot_main` calls its first closure, `bootMainClosure0` at 0x403a00a6, once
for each slot it tries, at offsets 0x208 and 0x262. The closure is
`|slot| check(slot, efuse_level, &mut buffers)`, and its specification is
`acceptTufSlot`. `Closure0Contract` states what `boot_main`'s proof assumes
of the call, so that proof can take the closure's theorem as a hypothesis.

The call's arguments:

* `a0` is the result, an `Option<(Accepted, u32)>` of 0x12C bytes. The byte
  at +0xC is 0xFF for `None`. `Accepted` is the first 0x120 bytes, which
  `boot_main` copies and passes to `boot`; the word at +0x120 is the image's
  flash address, and the byte at +0x128 is the image's security version.
* `a1` is the eFuse level.
* `a2` is the `Buffers`, 0xB954 bytes.
* `a3` is the slot: 0 for slot A and 1 for slot B.
-/

namespace C3.RV32.BootMainContract
open C3 C3.Image

/-- The flash address of slot `slot`'s first byte. -/
def bmcBase (slot : Word) : Nat := if slot = 0 then 0x30000 else 0x210000

/-- `len` bytes of flash from `a`. -/
def bmcFlash (flash : Nat → BitVec 8) (a len : Nat) : Bytes :=
  (List.range len).map fun i => (flash (a + i)).toNat

/-- What `acceptTufSlot` says of slot `slot` at eFuse level `level`: the
slot's manifest, then the image's security version and signing time, or
`none` when the manifest doesn't decode or the slot is rejected. -/
def bmcAccept (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (level : Nat)
    (slot : Word) : Option (Manifest × Nat × Nat) := do
  let mf ← decodeManifest (bmcFlash flash (bmcBase slot) 32)
  let part (p : Part) := bmcFlash flash (bmcBase slot + p.offset) p.length
  let r ← acceptTufSlot (part mf.image) (part mf.bundle) (part mf.tuf) pinned policy level
  pure (mf, r)

/-- **The closure's contract.** Called at its entry with the closure's code
in memory, memory that satisfies `E` (the callees' code and data), at least
`stack` bytes of stack, and the result, the `Buffers`, and the stack apart:
the closure returns to `ra` with the registers that `romKeep` names kept and
memory unchanged outside the stack, the result, and the `Buffers`, or it
panics. On return, the result is `None` when `bmcAccept` is `none`.
Otherwise it holds the image's flash address and security version, and its
`Accepted` part satisfies `AccOk`, which states what `boot` needs of the
header. -/
def Closure0Contract (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat)
    (pinned : Bytes) (policy : Policy) (stack : Nat) (E : (Word → BitVec 8) → Prop)
    (AccOk : (Word → BitVec 8) → Word → Prop) : Prop :=
  RomRead flash R romBase romCode →
  ∀ (m : Machine) (res bufs slot level : Word),
    CodeIn m.mem (BitVec.ofNat 32 bootMainClosure0Address) bootMainClosure0Code → E m.mem →
    m.pc = BitVec.ofNat 32 bootMainClosure0Address → stack ≤ (reg m sp).toNat →
    reg m a0 = res → reg m a1 = level → reg m a2 = bufs → reg m a3 = slot → slot.toNat < 2 →
    Sep res 0x12C bufs 0xB954 → Sep res 0x12C (reg m sp - BitVec.ofNat 32 stack) stack →
    Sep bufs 0xB954 (reg m sp - BitVec.ofNat 32 stack) stack →
    (∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
      (∀ x, Sep (reg m sp - BitVec.ofNat 32 stack) stack x 1 → Sep res 0x12C x 1 →
        Sep bufs 0xB954 x 1 → m'.mem x = m.mem x) ∧
      match bmcAccept flash pinned policy level.toNat slot with
      | none => m'.mem (res + 0xC) = 0xFF
      | some (mf, sv, _) =>
        m'.mem (res + 0xC) ≠ 0xFF ∧ m'.mem (res + 0x128) = BitVec.ofNat 8 sv ∧
          memLoad32 m'.mem (res + 0x120) = BitVec.ofNat 32 (bmcBase slot + mf.image.offset) ∧
          AccOk m'.mem res) ∨
    Panics m

end C3.RV32.BootMainContract
