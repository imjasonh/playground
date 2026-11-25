import C3BootProofs.Spec.Json

/-!
# `c3_verify::json` by positions

The compiled JSON functions work on a document and a position in it, the
way `json.rs` reads. These functions say what each one computes, on the
document's bytes `d` and positions as natural numbers. The machine-code
theorems are stated with them. No proof yet relates them to
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

/-- The index, counting from `i`, of the quote that closes a string whose
body starts at `l`. `none` at a backslash, at the end, or, in strict mode,
at a control byte. -/
def strScan (c : Bool) : Bytes → Nat → Option Nat
  | [], _ => none
  | b :: l, i =>
    if b == 34 then some i else if b == 92 then none else if !c && b < 32 then none else strScan c l (i + 1)

/-- `string_end`: the position after the string whose quote is at `pos`. -/
def stringEnd (c : Bool) (d : Bytes) (pos : Nat) : Option Nat :=
  if d.length ≤ pos then none else (strScan c (d.drop (pos + 1)) 0).map fun i => pos + 1 + i + 1

theorem strScan_lt {c : Bool} : ∀ {l : Bytes} {i k : Nat}, strScan c l i = some k → k < i + l.length
  | [], _, _, h => by simp [strScan] at h
  | b :: l, i, k, h => by
    simp only [strScan] at h
    split at h
    · cases h; simp
    · split at h
      · cases h
      · split at h
        · cases h
        · have := strScan_lt h; simp only [List.length_cons]; omega

/-- How many decimal digits `l` starts with. -/
def digLen : Bytes → Nat
  | [] => 0
  | b :: l => if isDigit b then digLen l + 1 else 0

theorem digLen_le : ∀ l : Bytes, digLen l ≤ l.length
  | [] => Nat.le_refl _
  | b :: l => by
    cases h : isDigit b
    · simp only [digLen, h, Bool.false_eq_true, ↓reduceIte]; exact Nat.zero_le _
    · simp only [digLen, h, ↓reduceIte, List.length_cons]; exact Nat.succ_le_succ (digLen_le l)

/-- `number_end`: the position after the number at `pos`, of 1 to 19
digits with no leading zero. -/
def numberEnd (d : Bytes) (pos : Nat) : Option Nat :=
  if d.length < pos then none
  else if digLen (d.drop pos) = 0 then none
  else if 19 < digLen (d.drop pos) then none
  else if (d.drop pos).head? = some 48 then (if digLen (d.drop pos) = 1 then some (pos + 1) else none)
  else some (pos + digLen (d.drop pos))

theorem numberEnd_nil {d : Bytes} {pos : Nat} (hd : d.drop pos = []) : numberEnd d pos = none := by
  unfold numberEnd
  rw [hd]
  split
  · rfl
  · rfl

theorem numberEnd_cons {d l : Bytes} {pos b : Nat} (hlen : ¬d.length < pos) (hd : d.drop pos = b :: l) :
    numberEnd d pos = if digLen (b :: l) = 0 then none else if 19 < digLen (b :: l) then none
      else if b = 48 then (if digLen (b :: l) = 1 then some (pos + 1) else none)
      else some (pos + digLen (b :: l)) := by
  simp only [numberEnd, hlen, hd, ↓reduceIte, List.head?_cons, Option.some.injEq]

theorem skipWs_le (d : Bytes) (pos : Nat) : skipWs d pos ≤ pos + (d.length - pos) := by
  have := wsLen_le (d.drop pos)
  rw [List.length_drop] at this
  unfold skipWs; omega

theorem stringEnd_le {c : Bool} {d : Bytes} {pos e : Nat} (h : stringEnd c d pos = some e) : e ≤ d.length := by
  unfold stringEnd at h
  split at h
  · cases h
  · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    have := strScan_lt hi
    rw [List.length_drop] at this
    omega

/-- `skip_ws_in`: strict mode skips whitespace, and canonical mode allows
none. -/
def wsIn (c : Bool) (d : Bytes) (pos : Nat) : Nat := if c then pos else skipWs d pos

theorem wsIn_le (c : Bool) (d : Bytes) (pos : Nat) : wsIn c d pos ≤ pos + (d.length - pos) := by
  unfold wsIn; cases c
  · exact skipWs_le d pos
  · exact Nat.le_add_right _ _

/-- `key_end`: with the quote of an object key at `pos`, the position
after the key, its colon, and in strict mode the whitespace around the
colon. -/
def keyEnd (c : Bool) (d : Bytes) (pos : Nat) : Option Nat :=
  if d.length ≤ pos then none
  else if d.getD pos 0 ≠ 34 then none
  else match stringEnd c d pos with
    | none => none
    | some e =>
      if d.length ≤ wsIn c d e then none
      else if d.getD (wsIn c d e) 0 ≠ 58 then none
      else some (wsIn c d (wsIn c d e + 1))

end C3.Json
