import C3BootProofs.Spec.Level

/-!
# Facts about the security level

Burns and raises never lower the level, and a raise reaches its target and
goes no higher.
-/

namespace C3

theorem level_burn : ∀ (f m : Fuses), level f ≤ level (burn f m)
  | [], _ => by simp [burn, level]
  | _ :: _, [] => Nat.le_refl _
  | a :: f, b :: m => by
    have ih := level_burn f m
    cases a <;> cases b <;> simp [burn, level] <;> omega

theorem length_burn : ∀ (f m : Fuses), (burn f m).length = f.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: f, _ :: m => by simp [burn, length_burn f m]

theorem level_le_length : ∀ (f : Fuses), level f ≤ f.length
  | [] => by simp [level]
  | b :: f => by
    have := level_le_length f
    cases b <;> simp [level] <;> omega

theorem length_setFirstClear : ∀ (f : Fuses), (setFirstClear f).length = f.length
  | [] => rfl
  | false :: _ => rfl
  | true :: f => by simp [setFirstClear, length_setFirstClear f]

theorem level_setFirstClear_le : ∀ (f : Fuses), level (setFirstClear f) ≤ level f + 1
  | [] => by simp [setFirstClear, level]
  | false :: _ => by simp [setFirstClear, level]; omega
  | true :: f => by
    have := level_setFirstClear_le f
    simp [setFirstClear, level]
    omega

theorem level_le_setFirstClear : ∀ (f : Fuses), level f ≤ level (setFirstClear f)
  | [] => by simp [setFirstClear, level]
  | false :: _ => by simp [setFirstClear, level]
  | true :: f => by
    have := level_le_setFirstClear f
    simp [setFirstClear, level]
    omega

theorem level_setFirstClear :
    ∀ (f : Fuses), level f < f.length → level (setFirstClear f) = level f + 1
  | [], h => by simp [level] at h
  | false :: _, _ => by simp [setFirstClear, level]; omega
  | true :: f, h => by
    simp [level] at h
    have := level_setFirstClear f (by omega)
    simp [setFirstClear, level, this]
    omega

theorem level_raise_go_le (target : Nat) :
    ∀ (n : Nat) (f : Fuses), level (raise.go target n f) ≤ max (level f) target
  | 0, f => by simp only [raise.go]; omega
  | n + 1, f => by
    unfold raise.go
    split
    · omega
    · have ih := level_raise_go_le target n (setFirstClear f)
      have := level_setFirstClear_le f
      omega

theorem level_le_raise_go (target : Nat) :
    ∀ (n : Nat) (f : Fuses), level f ≤ level (raise.go target n f)
  | 0, f => by simp only [raise.go]; omega
  | n + 1, f => by
    unfold raise.go
    split
    · omega
    · have ih := level_le_raise_go target n (setFirstClear f)
      have := level_le_setFirstClear f
      omega

theorem le_level_raise_go (target : Nat) :
    ∀ (n : Nat) (f : Fuses), target ≤ f.length → target ≤ level f + n →
      target ≤ level (raise.go target n f)
  | 0, f, _, h2 => by simp only [raise.go]; omega
  | n + 1, f, h1, h2 => by
    unfold raise.go
    split
    · assumption
    · have hlt : level f < f.length := by omega
      have e := level_setFirstClear f hlt
      have l := length_setFirstClear f
      exact le_level_raise_go target n (setFirstClear f) (by omega) (by omega)

theorem length_raise_go (target : Nat) :
    ∀ (n : Nat) (f : Fuses), (raise.go target n f).length = f.length
  | 0, _ => rfl
  | n + 1, f => by
    unfold raise.go
    split
    · rfl
    · rw [length_raise_go target n (setFirstClear f), length_setFirstClear]

/-- A raise goes no higher than its target or the current level. -/
theorem level_raise_le (f : Fuses) (t : Nat) : level (raise f t) ≤ max (level f) t :=
  level_raise_go_le t f.length f

/-- A raise never lowers the level. -/
theorem level_le_raise (f : Fuses) (t : Nat) : level f ≤ level (raise f t) :=
  level_le_raise_go t f.length f

/-- A raise to a target the field can hold reaches it. -/
theorem le_level_raise (f : Fuses) (t : Nat) (h : t ≤ f.length) : t ≤ level (raise f t) :=
  le_level_raise_go t f.length f h (by omega)

theorem length_raise (f : Fuses) (t : Nat) : (raise f t).length = f.length :=
  length_raise_go t f.length f

theorem le_burnTarget (l : Nat) (c : Bool) (e : Nat) : e ≤ burnTarget l c e := by
  unfold burnTarget
  split
  · rename_i h
    simp at h
    omega
  · omega

theorem burnTarget_le (l : Nat) (c : Bool) (e : Nat) (h : e ≤ l) : burnTarget l c e ≤ l := by
  unfold burnTarget
  split <;> omega

end C3
