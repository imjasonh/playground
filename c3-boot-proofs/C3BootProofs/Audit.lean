import C3BootProofs.Theorems.TrustRoot

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

/-- A trace whose slot results come from flash contents that pass the
trust-root checks can jump, so `trust_root_monotone`'s hypotheses can hold
together. The verifier here accepts every signature; the differential test
exercises the signature rules. -/
theorem exists_trust_root_jump :
    ∃ (es : List Event) (flash : Nat → Slot → Option (Contents Nat Unit Unit)),
      Admissible es ∧
      (∀ (j : Nat) (hj : j < es.length),
        (es[j]'hj).before.slots = slotsOf (fun _ _ _ => true) [0, 1] (flash j)) ∧
      ∃ (j : Nat) (hj : j < es.length) (slot : Slot) (l : Nat),
        (es[j]'hj).jump = some (slot, l) := by
  let c : Contents Nat Unit Unit := ⟨[], ⟨0, (), [⟨0, ()⟩, ⟨1, ()⟩]⟩, 0, true⟩
  let fl : Slot → Option (Contents Nat Unit Unit) := fun _ => some c
  let d : Device := ⟨Fuses.ofNat 0, State.default, slotsOf (fun _ _ _ => true) [0, 1] fl⟩
  have h : ∃ slot l, accepted d.slots (level d.fuses) slot = some l := ⟨.a, 0, by decide⟩
  obtain ⟨d', slot, l, hs⟩ := availability d h
  refine ⟨[⟨d, d', some (slot, l)⟩], fun _ => fl, ⟨?_, ?_⟩, ?_, 0, by simp, slot, l, rfl⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact hs
  · intro i hi
    simp at hi
  · intro j hj
    have : j = 0 := by simp at hj; omega
    subst this
    rfl

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

/-- info: 'C3.trust_root_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.trust_root_monotone

/-- info: 'C3.exists_trust_root_jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.exists_trust_root_jump
