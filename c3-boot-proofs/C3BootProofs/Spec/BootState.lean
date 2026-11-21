/-!
# The boot-state record

The record is a hint that the application writes: which slot to prefer,
which slot is on trial, and which slots it confirmed. Nothing here decides
whether a slot is authentic. These definitions follow
`c3-boot/verify/src/bootstate.rs` after a copy decodes.
-/

namespace C3

/-- One of the two OTA slots. -/
inductive Slot where
  | a
  | b
  deriving DecidableEq, Repr

/-- The other slot. -/
def Slot.other : Slot → Slot
  | .a => .b
  | .b => .a

/-- The slot's bit in the record's `confirmed` field. -/
def Slot.bit : Slot → Nat
  | .a => 1
  | .b => 2

/-- A slot on trial, with the trial boots it has left. -/
structure Trial where
  slot : Slot
  bootsLeft : Nat
  deriving DecidableEq, Repr

/-- A decoded boot-state record. -/
structure State where
  generation : Nat
  preferred : Slot
  trial : Option Trial
  /-- Bit 0 for slot A and bit 1 for slot B. -/
  confirmed : Nat
  deriving DecidableEq, Repr

/-- The largest generation, which `next` saturates at. -/
def maxGeneration : Nat := 2 ^ 32 - 1

namespace State

/-- The state used when neither copy decodes. -/
def default : State := ⟨0, .a, none, 0⟩

/-- Whether the record marks `slot` confirmed. -/
def isConfirmed (s : State) (slot : Slot) : Bool :=
  s.confirmed &&& slot.bit != 0

/-- The same state at the next generation. -/
def next (s : State) : State :=
  { s with generation := min (s.generation + 1) maxGeneration }

/-- The state to write before jumping to a trial slot. -/
def withTrialBootUsed (s : State) : State :=
  { s.next with trial := s.trial.map fun t => { t with bootsLeft := t.bootsLeft - 1 } }

/-- The state to write to end a trial. -/
def withoutTrial (s : State) : State :=
  { s.next with trial := none }

end State

/-- The first slot to try, and any state to write before trying it. -/
structure Plan where
  first : Slot
  isTrial : Bool
  writeFirst : Option State

/-- Tries a trial slot with boots left first. An expired trial is ended,
and the preferred slot is tried first. -/
def plan (s : State) : Plan :=
  match s.trial with
  | some t => if 0 < t.bootsLeft then ⟨t.slot, true, none⟩ else ⟨s.preferred, false, some s.withoutTrial⟩
  | none => ⟨s.preferred, false, none⟩

end C3
