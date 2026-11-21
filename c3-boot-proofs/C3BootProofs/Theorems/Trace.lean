import C3BootProofs.Theorems.Boot

/-!
# Many boots with power loss

A device is its eFuse field, the boot-state record in use, and the result
of checking each slot's flash contents. A trace is a sequence of steps:

- `write`: the application, or an attacker who controls flash, writes any
  record and any slot contents.
- `interrupted`: a boot that loses power, or halts, at any point. It may
  have burned any eFuse bits and left any record. The bootloader's halt
  when an eFuse bit fails to program is one of these.
- `jumped`: a boot that runs to the jump. It writes the decision's record,
  or leaves the old one if the write failed, and raises the level to the
  decision's target, one bit at a time.

These are the plan's `rollback`, `boots_safe`, `availability`, and the
level half of `trust_root_monotone`'s `efuseMonotone`, at the level of the
decision logic. The machine-code proofs connect them to the binary.
-/

namespace C3

/-- The state that persists across boots. -/
structure Device where
  fuses : Fuses
  record : State
  /-- The level of each slot that passes every check except the level
  rules against the eFuses. -/
  slots : Slot → Option Nat

/-- One step of a trace, with the slot and level it jumped to, if any. -/
inductive Step : Device → Device → Option (Slot × Nat) → Prop where
  | write (d : Device) (record : State) (slots : Slot → Option Nat) :
      Step d { d with record := record, slots := slots } none
  | interrupted (d : Device) (m : Fuses) (record : State) :
      Step d { d with fuses := burn d.fuses m, record := record } none
  | jumped (d : Device) (w : Option State) (slot : Slot) (t l : Nat) (record : State)
      (hd : decideBoot d.record (level d.fuses) (accepted d.slots (level d.fuses)) =
        ⟨w, .boot slot t⟩)
      (hl : accepted d.slots (level d.fuses) slot = some l)
      (hr : record = w.getD d.record ∨ record = d.record) :
      Step d { d with fuses := raise d.fuses t, record := record } (some (slot, l))

/-- One step, with the device before and after it. -/
structure Event where
  before : Device
  after : Device
  jump : Option (Slot × Nat)

/-- Every event is a step, and each event starts where the previous one
ended. -/
def Admissible (es : List Event) : Prop :=
  (∀ e ∈ es, Step e.before e.after e.jump) ∧
    ∀ (i : Nat) (h : i + 1 < es.length), (es[i]'(by omega)).after = (es[i + 1]'h).before

theorem Step.level_mono {d d' : Device} {j : Option (Slot × Nat)} (h : Step d d' j) :
    level d.fuses ≤ level d'.fuses := by
  cases h with
  | write => exact Nat.le_refl _
  | interrupted m => exact level_burn d.fuses m
  | jumped w slot t => exact level_le_raise d.fuses t

theorem Step.length_eq {d d' : Device} {j : Option (Slot × Nat)} (h : Step d d' j) :
    d'.fuses.length = d.fuses.length := by
  cases h with
  | write => rfl
  | interrupted m => exact length_burn d.fuses m
  | jumped w slot t => exact length_raise d.fuses t

/-- What a jump guarantees about the step that made it. -/
theorem Step.jump_facts {d d' : Device} {slot : Slot} {l : Nat}
    (h : Step d d' (some (slot, l))) :
    accepted d.slots (level d.fuses) slot = some l ∧
      ∃ t, t = burnTarget l (d.record.isConfirmed slot) (level d.fuses) ∧
        d'.fuses = raise d.fuses t := by
  cases h with
  | jumped w _ t _ record hd hl hr =>
    refine ⟨hl, t, ?_, rfl⟩
    obtain ⟨l', hl', ht⟩ := decideBoot_boot hd
    rw [hl] at hl'
    cases hl'
    exact ht

theorem Admissible.step {es : List Event} (h : Admissible es) (i : Nat) (hi : i < es.length) :
    Step (es[i]'hi).before (es[i]'hi).after (es[i]'hi).jump :=
  h.1 _ (List.getElem_mem hi)

theorem Admissible.before_mono {es : List Event} (h : Admissible es) :
    ∀ (i j : Nat) (hij : i ≤ j) (hj : j < es.length),
      level (es[i]'(by omega)).before.fuses ≤ level (es[j]'hj).before.fuses
  | i, 0, hij, hj => by
    have : i = 0 := by omega
    subst this
    exact Nat.le_refl _
  | i, j + 1, hij, hj => by
    by_cases hi : i = j + 1
    · subst hi
      exact Nat.le_refl _
    · have ih := h.before_mono i j (by omega) (by omega)
      have hs := (h.step j (by omega)).level_mono
      have hc := h.2 j hj
      rw [hc] at hs
      omega

theorem Admissible.length_eq {es : List Event} (h : Admissible es) (h0 : 0 < es.length)
    (hwf : (es[0]'h0).before.fuses.length = maxLevel) :
    ∀ (j : Nat) (hj : j < es.length), (es[j]'hj).before.fuses.length = maxLevel
  | 0, _ => hwf
  | j + 1, hj => by
    have ih := h.length_eq h0 hwf j (by omega)
    have hs := (h.step j (by omega)).length_eq
    rw [h.2 j hj] at hs
    omega

/-- No step lowers the security level. -/
theorem efuse_monotone {es : List Event} (h : Admissible es) {i j : Nat} (hij : i ≤ j)
    (hj : j < es.length) :
    level (es[i]'(by omega)).before.fuses ≤ level (es[j]'hj).after.fuses :=
  Nat.le_trans (h.before_mono i j hij hj) (h.step j hj).level_mono

/-- Once a step ends with the level at some value, no later boot, nor the
boot of that same step, runs a slot whose level is below it. -/
theorem rollback {es : List Event} (h : Admissible es) {i j : Nat} (hij : i ≤ j)
    (hj : j < es.length) {slot : Slot} {l : Nat}
    (hjump : (es[j]'hj).jump = some (slot, l)) :
    level (es[i]'(by omega)).after.fuses ≤ l := by
  have hs := h.step j hj
  rw [hjump] at hs
  obtain ⟨hl, t, ht, hf⟩ := hs.jump_facts
  obtain ⟨_, hle, _⟩ := accepted_some hl
  have htl : t ≤ l := by rw [ht]; exact burnTarget_le _ _ _ hle
  by_cases hij' : i = j
  · subst hij'
    rw [hf]
    have := level_raise_le (es[i]'hj).before.fuses t
    omega
  · have hstep := (h.step i (by omega)).level_mono
    have hc := h.2 i (by omega)
    have hm := h.before_mono (i + 1) j (by omega) hj
    have : level (es[i]'(by omega)).after.fuses ≤ level (es[i + 1]'(by omega)).before.fuses := by
      rw [hc]
      exact Nat.le_refl _
    omega

/-- Every jump goes to a slot the bootloader accepted at the level it read,
and only after the level reached that slot's burn target. -/
theorem boots_safe {es : List Event} (h : Admissible es) (h0 : 0 < es.length)
    (hwf : (es[0]'h0).before.fuses.length = maxLevel) {j : Nat} (hj : j < es.length)
    {slot : Slot} {l : Nat} (hjump : (es[j]'hj).jump = some (slot, l)) :
    accepted (es[j]'hj).before.slots (level (es[j]'hj).before.fuses) slot = some l ∧
      burnTarget l ((es[j]'hj).before.record.isConfirmed slot)
          (level (es[j]'hj).before.fuses) ≤
        level (es[j]'hj).after.fuses := by
  have hs := h.step j hj
  rw [hjump] at hs
  obtain ⟨hl, t, ht, hf⟩ := hs.jump_facts
  refine ⟨hl, ?_⟩
  obtain ⟨_, hle, hmax⟩ := accepted_some hl
  rw [hf, ← ht]
  apply le_level_raise
  rw [h.length_eq h0 hwf j hj, ht]
  exact Nat.le_trans (burnTarget_le _ _ _ hle) hmax

/-- A boot that runs to completion jumps whenever some slot is accepted. -/
theorem availability (d : Device)
    (h : ∃ slot l, accepted d.slots (level d.fuses) slot = some l) :
    ∃ d' slot l, Step d d' (some (slot, l)) := by
  obtain ⟨w, slot, t, hd⟩ := decideBoot_available (s := d.record) h
  obtain ⟨l, hl, _⟩ := decideBoot_boot hd
  exact ⟨_, slot, l, Step.jumped d w slot t l d.record hd hl (Or.inr rfl)⟩

end C3
