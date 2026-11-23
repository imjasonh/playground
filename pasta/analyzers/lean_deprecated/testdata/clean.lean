/-- Mentions of if_pos in a doc comment are prose, not uses. -/
theorem pick_left {c : Prop} [Decidable c] (hc : c) (t e : Nat) :
    (if c then t else e) = t := by
  rw [ite_eq_left hc] -- if_pos was the old name

namespace Mine

theorem if_pos' (n : Nat) : n = n := rfl

end Mine

theorem qualified (n : Nat) : n = n := Mine.if_pos' n

def label : String := "if_neg"
