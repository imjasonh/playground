theorem pick_left {c : Prop} [Decidable c] (hc : c) (t e : Nat) :
    (if c then t else e) = t := by
  rw [if_pos hc] -- want "`if_pos` is deprecated; use `ite_eq_left`"

theorem pick_right {c : Prop} [Decidable c] (hnc : ¬c) (t e : Nat) :
    (if c then t else e) = e :=
  if_neg hnc -- want "`if_neg` is deprecated; use `ite_eq_right`"

theorem both (t e : Nat) : (if True then t else e) = t ∧ (if False then t else e) = e :=
  ⟨if_true t e, if_false t e⟩ -- want "`if_true` is deprecated; use `ite_true`" -- want "`if_false` is deprecated; use `ite_false`"

theorem decided (x : Nat) (h : x < 4) : (if 2 < 4 then x else 0) < 4 := by
  dsimp only; rw [if_pos (by decide)]; exact h -- want "`if_pos` is deprecated; use `ite_eq_left`"

theorem in_simp (a b : Nat) (h : a = b) : (if a = b then 1 else 0) = 1 := by
  simp only [if_pos h, @if_neg] -- want "`if_pos` is deprecated" -- want "`if_neg` is deprecated"
