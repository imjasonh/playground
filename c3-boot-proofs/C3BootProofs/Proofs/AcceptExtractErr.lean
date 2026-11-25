import C3BootProofs.Proofs.JsonParseModel

/-!
# The error bytes of `parse` and `field`

Every error that `parse` and `field` return is `0x20` or `0x21`, so each is
a code that the closure's rejection log has a message for.
-/

namespace C3.Json

/-- `r` is a value or an error byte below 0x27. -/
def AceErr {α : Type} (r : Except Nat α) : Prop := ∀ e, r = .error e → e < 0x27

theorem aceErr_ok {α : Type} (a : α) : AceErr (.ok a : Except Nat α) := fun _ h => by cases h

theorem aceErr_err {α : Type} {e : Nat} (h : e < 0x27) : AceErr (.error e : Except Nat α) := fun _ h' => by
  cases h'; exact h

theorem ace_keysUnique (o key : Bytes) : ∀ k u pos, AceErr (keysUnique o key k u pos)
  | 0, _, _ => aceErr_ok _
  | k + 1, u, pos => by
    simp only [keysUnique]
    split
    · exact aceErr_err (by decide)
    · exact aceErr_ok _
    · exact ace_keysUnique o key k _ _

theorem ace_keysStrict (o : Bytes) : ∀ k pos, AceErr (keysStrict o k pos)
  | 0, _ => aceErr_ok _
  | k + 1, pos => by
    simp only [keysStrict]
    split
    · exact aceErr_err (by decide)
    · exact aceErr_ok _
    · split
      · rename_i e he
        exact aceErr_err (ace_keysUnique _ _ _ _ _ e he)
      · split
        · exact ace_keysStrict o k _
        · exact aceErr_err (by decide)

theorem ace_keysCanon (o : Bytes) : ∀ k prev pos, AceErr (keysCanon o k prev pos)
  | 0, _, _ => aceErr_ok _
  | k + 1, prev, pos => by
    simp only [keysCanon]
    split
    · exact aceErr_err (by decide)
    · exact aceErr_ok _
    · split
      · exact ace_keysCanon o k _ _
      · split
        · exact ace_keysCanon o k _ _
        · exact aceErr_err (by decide)

theorem ace_checkKeys (c : Bool) (o : Bytes) : AceErr (checkKeys c o) := by
  unfold checkKeys
  split
  · exact aceErr_err (by decide)
  · split
    · exact ace_keysCanon o _ _ _
    · exact ace_keysStrict o _ _

theorem ace_closeLoop (c : Bool) (d : Bytes) (start : Nat) : ∀ j stk pos, AceErr (closeLoop c d start j stk pos)
  | 0, _, _ => aceErr_ok _
  | j + 1, stk, pos => by
    simp only [closeLoop]
    split
    · split
      · exact aceErr_err (by decide)
      · exact aceErr_ok _
    · split
      · exact aceErr_err (by decide)
      · split
        · split
          · exact aceErr_err (by decide)
          · exact ace_closeLoop c d start j _ _
        · split
          · split
            · split
              · exact aceErr_err (by decide)
              · split
                · rename_i e he
                  exact aceErr_err (ace_checkKeys _ _ e he)
                · exact ace_closeLoop c d start j _ _
            · exact aceErr_err (by decide)
          · split
            · split
              · split
                · exact aceErr_err (by decide)
                · exact aceErr_ok _
              · exact aceErr_ok _
            · exact aceErr_err (by decide)

theorem ace_afterClose {r : Except Nat PStep} {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hr : AceErr r) (hn : ∀ stk p, AceErr (next stk p)) : AceErr (afterClose r next) := by
  cases r with
  | error e => simp only [afterClose]; exact aceErr_err (hr e rfl)
  | ok s =>
    cases s with
    | done a e => simp only [afterClose]; exact aceErr_ok _
    | cont stk p => simp only [afterClose]; exact hn stk p

theorem ace_parseLoop (c : Bool) (d : Bytes) (start : Nat) : ∀ k stk pos, AceErr (parseLoop c d start k stk pos)
  | 0, _, _ => aceErr_err (by decide)
  | k + 1, stk, pos => by
    have ih := ace_parseLoop c d start k
    have hc := ace_closeLoop c d start 17
    simp only [parseLoop]
    split
    · exact aceErr_err (by decide)
    · split
      · split
        · exact aceErr_err (by decide)
        · exact ace_afterClose (hc _ _) ih
      · split
        · split
          · exact aceErr_err (by decide)
          · split
            · split
              · exact ace_afterClose (hc _ _) ih
              · exact ih _ _
            · split
              · exact ace_afterClose (hc _ _) ih
              · split
                · exact aceErr_err (by decide)
                · exact ih _ _
        · split
          · split
            · exact aceErr_err (by decide)
            · exact ace_afterClose (hc _ _) ih
          · split
            · split
              · exact aceErr_err (by decide)
              · exact ace_afterClose (hc _ _) ih
            · exact aceErr_err (by decide)

theorem ace_objField (d key : Bytes) : AceErr (objField d key) := by
  unfold objField objGet
  split
  · rename_i e he
    split at he
    · cases he; exact aceErr_err (by decide)
    · unfold getOut at he
      split at he
      · cases he; exact aceErr_err (by decide)
      · cases he
  · exact aceErr_err (by decide)
  · exact aceErr_ok _

/-- **`parse`'s error bytes are below 0x27.** -/
theorem ace_parseModel (c : Bool) (d : Bytes) : AceErr (parseModel c d) := ace_parseLoop c d _ _ _ _

end C3.Json
