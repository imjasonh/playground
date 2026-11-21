import C3BootProofs.Spec.Level
import C3BootProofs.Spec.BootState

/-!
# The boot decision

`decideBoot` follows `c3_verify::boot::decide`: which slot to boot, which
record to write, and the level to reach before the jump.
-/

namespace C3

/-- What the bootloader does once it has checked slots. -/
inductive Outcome where
  /-- Raise the eFuse level to `levelTarget`, then load `slot` and jump. -/
  | boot (slot : Slot) (levelTarget : Nat)
  /-- No slot passed its checks. -/
  | halt
  deriving DecidableEq, Repr

/-- At most one record to write, then the outcome. -/
structure Decision where
  write : Option State
  outcome : Outcome
  deriving DecidableEq, Repr

/-- Decides one boot. `check` returns the level of a slot that passes every
check, including the level rules against `efuseLevel`. The Rust code
writes the record through a callback at fixed points between the checks;
this gives only which record it writes. -/
def decideBoot (s : State) (efuseLevel : Nat) (check : Slot → Option Nat) : Decision :=
  let p := plan s
  let boot (slot : Slot) (l : Nat) :=
    Outcome.boot slot (burnTarget l (s.isConfirmed slot) efuseLevel)
  match check p.first with
  | some l => ⟨if p.isTrial then some s.withTrialBootUsed else p.writeFirst, boot p.first l⟩
  | none =>
    let write := if p.isTrial then some s.withoutTrial else p.writeFirst
    match check p.first.other with
    | some l => ⟨write, boot p.first.other l⟩
    | none => ⟨write, .halt⟩

/-- The slots the bootloader accepts at eFuse level `efuseLevel`. `slots`
gives the level of each slot that passes the format, signature, key-set
chain, trust-root, and transparency checks; a slot is accepted when, in
addition, its level is between the eFuse level and 16. -/
def accepted (slots : Slot → Option Nat) (efuseLevel : Nat) (s : Slot) : Option Nat :=
  match slots s with
  | some l => if efuseLevel ≤ l ∧ l ≤ maxLevel then some l else none
  | none => none

end C3
