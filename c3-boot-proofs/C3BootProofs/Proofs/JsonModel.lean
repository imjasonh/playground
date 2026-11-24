import C3BootProofs.Spec.Json

/-!
# `c3_verify::json` by positions

The compiled JSON functions work on a document and a position in it, the
way `json.rs` reads. These functions say what each one computes, on the
document's bytes `d` and positions as natural numbers. The machine-code
theorems are stated with them, and `JsonSpec.lean` relates them to
`Spec/Json.lean`.
-/

namespace C3.Json

/-- How many whitespace bytes `l` starts with. -/
def wsLen : Bytes → Nat
  | [] => 0
  | b :: l => if isWs b then wsLen l + 1 else 0

/-- `skip_ws`: the position after the whitespace at `pos`. -/
def skipWs (d : Bytes) (pos : Nat) : Nat := pos + wsLen (d.drop pos)

theorem wsLen_nil : wsLen [] = 0 := rfl

theorem wsLen_cons_ws {b : Nat} {l : Bytes} (h : isWs b = true) : wsLen (b :: l) = wsLen l + 1 := by
  simp only [wsLen, h, ↓reduceIte]

theorem wsLen_cons_not {b : Nat} {l : Bytes} (h : isWs b = false) : wsLen (b :: l) = 0 := by
  simp only [wsLen, h, Bool.false_eq_true, ↓reduceIte]

theorem wsLen_le : ∀ l : Bytes, wsLen l ≤ l.length
  | [] => Nat.le_refl _
  | b :: l => by
    cases h : isWs b
    · rw [wsLen_cons_not h]; exact Nat.zero_le _
    · rw [wsLen_cons_ws h, List.length_cons]; exact Nat.succ_le_succ (wsLen_le l)

theorem drop_wsLen : ∀ l : Bytes, l.drop (wsLen l) = l.dropWhile isWs
  | [] => rfl
  | b :: l => by
    cases h : isWs b
    · rw [wsLen_cons_not h, List.drop_zero, List.dropWhile_cons, h]; rfl
    · rw [wsLen_cons_ws h, List.drop_succ_cons, drop_wsLen l, List.dropWhile_cons, h]; rfl

end C3.Json
