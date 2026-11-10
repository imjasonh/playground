import C3BootProofs.Theorems.Trace

/-!
# Audit

Each theorem's axioms are pinned, so a proof that comes to depend on
`sorryAx` or a new axiom fails the build. The non-vacuity theorem shows that
the trace theorems' hypotheses can hold together with a jump.
-/

namespace C3

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
