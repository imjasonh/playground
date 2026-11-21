import C3BootProofs.Spec.Boot
import C3BootProofs.Theorems.Level

/-!
# Facts about one boot decision

The bootloader boots only a slot that `check` accepted, with the burn
target for that slot, and it boots some slot whenever `check` accepts one.
-/

namespace C3

/-- A boot decision names a slot that `check` accepted, and its level
target is the burn target for that slot. -/
theorem decideBoot_boot {s : State} {e : Nat} {check : Slot → Option Nat}
    {w : Option State} {slot : Slot} {t : Nat}
    (h : decideBoot s e check = ⟨w, .boot slot t⟩) :
    ∃ l, check slot = some l ∧ t = burnTarget l (s.isConfirmed slot) e := by
  unfold decideBoot at h
  simp only at h
  split at h
  · rename_i l hl
    simp only [Decision.mk.injEq, Outcome.boot.injEq] at h
    obtain ⟨_, rfl, rfl⟩ := h
    exact ⟨l, hl, rfl⟩
  · split at h
    · rename_i l hl
      simp only [Decision.mk.injEq, Outcome.boot.injEq] at h
      obtain ⟨_, rfl, rfl⟩ := h
      exact ⟨l, hl, rfl⟩
    · simp at h

/-- If `check` accepts some slot, the bootloader boots some slot. -/
theorem decideBoot_available {s : State} {e : Nat} {check : Slot → Option Nat}
    (h : ∃ slot l, check slot = some l) :
    ∃ w slot t, decideBoot s e check = ⟨w, .boot slot t⟩ := by
  obtain ⟨slot, l, hl⟩ := h
  unfold decideBoot
  simp only
  split
  · exact ⟨_, _, _, rfl⟩
  · rename_i hfirst
    split
    · exact ⟨_, _, _, rfl⟩
    · rename_i hother
      exfalso
      cases hp : (plan s).first <;> cases slot <;> simp_all [Slot.other]

theorem accepted_some {slots : Slot → Option Nat} {e : Nat} {s : Slot} {l : Nat}
    (h : accepted slots e s = some l) : slots s = some l ∧ e ≤ l ∧ l ≤ maxLevel := by
  unfold accepted at h
  split at h
  · rename_i l' hs
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hs, hc.1, hc.2⟩
    · simp at h
  · simp at h

end C3
