import C3BootProofs.Proofs.JsonParseModel

/-!
# `json::parse`: what an `.ok` result says

`parseModel_ok` is the contract that callers of `jsonParse_correct` use:
the value starts after the leading whitespace, lies within the document,
and only whitespace follows it. In canonical mode it is the whole
document (`parseModel_ok_canon`).
-/

namespace C3.Json

/-- The value that `parse` reports: it starts at `start`, ends within the
document, and only whitespace (none in canonical mode) follows it. -/
def ParseEnd (c : Bool) (d : Bytes) (start : Nat) (v : Nat × Nat) : Prop :=
  v.1 = start ∧ start + v.2 ≤ d.length ∧ wsIn c d (start + v.2) = d.length

theorem closeLoop_done (c : Bool) (d : Bytes) (start : Nat) {a e : Nat} :
    ∀ j stk pos, closeLoop c d start j stk pos = .ok (.done a e) →
      a = start ∧ start ≤ e ∧ e ≤ d.length ∧ wsIn c d e = d.length := by
  intro j
  induction j with
  | zero => intro stk pos h; cases h
  | succ j ih =>
    intro stk pos h
    unfold closeLoop at h
    split at h
    · split at h
      · cases h
      · cases h; omega
    · split at h
      · cases h
      split at h
      · split at h
        · cases h
        · exact ih _ _ h
      split at h
      · split at h
        · split at h
          · cases h
          split at h
          · cases h
          · exact ih _ _ h
        · cases h
      split at h
      · split at h
        · split at h
          · cases h
          · cases h
        · cases h
      · cases h

theorem afterClose_ok {r : Except Nat PStep} {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    {v : Nat × Nat} (h : afterClose r next = .ok v) :
    (∃ a e, r = .ok (.done a e) ∧ v = (a, e - a)) ∨ ∃ stk p, r = .ok (.cont stk p) ∧ next stk p = .ok v := by
  unfold afterClose at h
  split at h
  · cases h
  · cases h; exact Or.inl ⟨_, _, rfl, rfl⟩
  · exact Or.inr ⟨_, _, rfl, h⟩

theorem afterClose_end {c : Bool} {d : Bytes} {start j : Nat} {stk : List (Bool × Nat)} {pos : Nat}
    {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)} {v : Nat × Nat}
    (hn : ∀ stk p, next stk p = .ok v → ParseEnd c d start v)
    (h : afterClose (closeLoop c d start j stk pos) next = .ok v) : ParseEnd c d start v := by
  rcases afterClose_ok h with ⟨a, e, hr, hv⟩ | ⟨stk', p, -, hp⟩
  · obtain ⟨ha, hs, he, hw⟩ := closeLoop_done c d start j stk pos hr
    subst hv ha
    refine ⟨rfl, by simp only; omega, ?_⟩
    simp only; rw [Nat.add_sub_cancel' hs]; exact hw
  · exact hn _ _ hp

theorem parseLoop_end (c : Bool) (d : Bytes) (start : Nat) {v : Nat × Nat} :
    ∀ k stk pos, parseLoop c d start k stk pos = .ok v → ParseEnd c d start v := by
  intro k
  induction k with
  | zero => intro stk pos h; cases h
  | succ k ih =>
    intro stk pos h
    have hn : ∀ stk p, parseLoop c d start k stk p = .ok v → ParseEnd c d start v := ih
    unfold parseLoop at h
    split at h
    · cases h
    split at h
    · split at h
      · cases h
      · exact afterClose_end hn h
    split at h
    · split at h
      · cases h
      split at h
      · split at h
        · exact afterClose_end hn h
        · exact ih _ _ h
      split at h
      · exact afterClose_end hn h
      split at h
      · cases h
      · exact ih _ _ h
    split at h
    · split at h
      · cases h
      · exact afterClose_end hn h
    split at h
    · split at h
      · cases h
      · exact afterClose_end hn h
    · cases h

/-- An `.ok (a, l)` result of `parseModel`: the value starts at `a`, after
the leading whitespace (none in canonical mode), its `l` bytes lie within
the document, and only whitespace follows them. -/
theorem parseModel_ok {c : Bool} {d : Bytes} {a l : Nat} (h : parseModel c d = .ok (a, l)) :
    a = wsIn c d 0 ∧ a + l ≤ d.length ∧ wsIn c d (a + l) = d.length := by
  obtain ⟨ha, hl, hw⟩ := parseLoop_end c d _ _ _ _ h
  simp only at ha hl hw
  subst ha
  exact ⟨rfl, hl, hw⟩

/-- In canonical mode an `.ok (a, l)` result is the whole document. -/
theorem parseModel_ok_canon {d : Bytes} {a l : Nat} (h : parseModel true d = .ok (a, l)) :
    a = 0 ∧ l = d.length := by
  obtain ⟨ha, -, hw⟩ := parseModel_ok h
  simp only [wsIn, ↓reduceIte] at ha hw
  exact ⟨ha, by omega⟩

end C3.Json
