import C3BootProofs.Models.JsonLink
import C3BootProofs.Models.JsonLinkSpec

/-!
# The JSON scanners against the spec's parsers

Each scanner of `Proofs/JsonModel.lean` reads the document `d` from a
position, and the spec's parser reads the bytes from there, `d.drop i`. A
scanner returns the position after what it read, `d.length - r.length` for
the spec's leftover bytes `r`.
-/

namespace C3.Json

open C3

set_option linter.unusedSimpArgs false

/-! ## Positions -/

theorem jlp_if_pos {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : p) : (if p then a else b) = a := by
  simp only [h, ↓reduceIte]

theorem jlp_if_neg {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : ¬p) : (if p then a else b) = b := by
  simp only [h, ↓reduceIte]

theorem jlp_drop_cons {d : Bytes} {i : Nat} (h : i < d.length) : d.drop i = d.getD i 0 :: d.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem jlp_drop_cons_inv {d l : Bytes} {i b : Nat} (h : d.drop i = b :: l) :
    i < d.length ∧ d.getD i 0 = b ∧ l = d.drop (i + 1) := by
  have hi : i < d.length := by
    have := congrArg List.length h
    rw [List.length_drop, List.length_cons] at this
    omega
  rw [jlp_drop_cons hi] at h
  injection h with h1 h2
  exact ⟨hi, h1, h2.symm⟩

theorem jlp_drop_nil {d : Bytes} {i : Nat} (h : d.drop i = []) : d.length ≤ i := List.drop_eq_nil_iff.mp h

/-- The bytes a parse leaves are the document from `d.length - r.length`. -/
theorem jlp_rest {d x r : Bytes} {i : Nat} (h : d.drop i = x ++ r) (hx : x ≠ []) :
    r = d.drop (d.length - r.length) ∧ i < d.length - r.length ∧ d.length - r.length ≤ d.length := by
  have hl := congrArg List.length h
  rw [List.length_drop, List.length_append] at hl
  have hx1 : 1 ≤ x.length := by
    cases x with
    | nil => exact absurd rfl hx
    | cons _ _ => simp only [List.length_cons]; omega
  have he : d.length - r.length = i + x.length := by omega
  refine ⟨?_, by omega, by omega⟩
  have := congrArg (List.drop x.length) h
  rw [List.drop_drop, List.drop_left] at this
  rw [he, this]

/-- The position after a parse of `d.drop i` that left `r`. -/
abbrev jlpEnd (d r : Bytes) : Nat := d.length - r.length

theorem jlp_end_drop (d : Bytes) {e : Nat} (h : e ≤ d.length) : jlpEnd d (d.drop e) = e := by
  unfold jlpEnd; rw [List.length_drop]; omega

/-! ## Whitespace -/

theorem jlp_wsLen_dropWhile : ∀ l : Bytes, wsLen (l.dropWhile isWs) = 0
  | [] => rfl
  | b :: l => by
    cases h : isWs b
    · rw [List.dropWhile_cons, h]; exact wsLen_cons_not h
    · rw [List.dropWhile_cons, h]; exact jlp_wsLen_dropWhile l

theorem jlp_ws_drop (c : Bool) (d : Bytes) (i : Nat) : ws c (d.drop i) = d.drop (wsIn c d i) := by
  unfold ws wsIn; cases c
  · show List.dropWhile isWs (d.drop i) = d.drop (i + wsLen (d.drop i))
    rw [← List.drop_drop, drop_wsLen]
  · rfl

theorem jlp_wsIn_ge (c : Bool) (d : Bytes) (i : Nat) : i ≤ wsIn c d i := by
  unfold wsIn skipWs; cases c
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _

theorem jlp_wsIn_le {c : Bool} {d : Bytes} {i : Nat} (h : i ≤ d.length) : wsIn c d i ≤ d.length := by
  have := wsIn_le c d i; omega

theorem jlp_wsIn_idem (c : Bool) (d : Bytes) (i : Nat) : wsIn c d (wsIn c d i) = wsIn c d i := by
  unfold wsIn; cases c
  · show skipWs d (skipWs d i) = skipWs d i
    unfold skipWs
    rw [← List.drop_drop, drop_wsLen, jlp_wsLen_dropWhile]; rfl
  · rfl

theorem jlp_skipWs_eq_wsIn (d : Bytes) (i : Nat) : skipWs d i = wsIn false d i := rfl

/-- In canonical mode the spec's `ws` is the identity, so a byte that a
canonical parse reads next is not whitespace; `skipWs` stops there. -/
theorem jlp_skipWs_not_ws {d : Bytes} {i : Nat} (h : i < d.length) (hb : isWs (d.getD i 0) = false) :
    skipWs d i = i := by
  unfold skipWs; rw [jlp_drop_cons h, wsLen_cons_not hb]; rfl

theorem jlp_skipWs_end {d : Bytes} {i : Nat} (h : d.length ≤ i) : skipWs d i = i := by
  unfold skipWs; rw [List.drop_eq_nil_of_le h]; rfl

/-! ## Strings -/

theorem jlp_strScan (c : Bool) : ∀ (l : Bytes) (k : Nat),
    strScan c l k = (parseString c l).map fun p => k + p.1.length
  | [], k => by rw [jls_ps_nil]; rfl
  | b :: l, k => by
    by_cases h34 : b = 34
    · subst h34; rw [jls_ps_quote]; rfl
    rw [jls_ps_other c b l h34]
    unfold strScan
    have e34 : (b == 34) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h34
    rw [e34]
    by_cases h92 : b = 92
    · subst h92; rfl
    have e92 : (b == 92) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h92
    have n92 : (b != 92) = true := by simp only [bne_iff_ne, ne_eq]; exact h92
    rw [e92, n92]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and]
    cases c
    · by_cases h32 : b < 32
      · have : ¬ b ≥ 32 := by omega
        simp only [Bool.not_false, h32, decide_true, Bool.and_self, ↓reduceIte, Bool.false_or, this,
          decide_false, require, Bool.false_eq_true, Option.bind_none, Option.map_none]
      · have : b ≥ 32 := by omega
        simp only [Bool.not_false, h32, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          Bool.false_or, this, decide_true, require, Option.bind_some]
        rw [jlp_strScan false l (k + 1)]
        cases parseString false l with
        | none => rfl
        | some p => simp only [Option.map_some, Option.bind_some, List.length_cons]; congr 1; omega
    · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.true_or, require,
        Option.bind_some]
      rw [jlp_strScan true l (k + 1)]
      cases parseString true l with
      | none => rfl
      | some p => simp only [Option.map_some, Option.bind_some, List.length_cons]; congr 1; omega

theorem jlp_stringEnd {c : Bool} {d : Bytes} {i : Nat} (hi : i < d.length) :
    stringEnd c d i = (parseString c (d.drop (i + 1))).map fun p => jlpEnd d p.2 := by
  unfold stringEnd
  rw [jlp_if_neg (by omega), jlp_strScan]
  cases h : parseString c (d.drop (i + 1)) with
  | none => rfl
  | some p =>
    obtain ⟨s, r⟩ := p
    have hs := jls_str_suf c h
    have hl := congrArg List.length hs
    simp only [List.length_drop, List.length_append, List.length_cons] at hl
    simp only [Option.map_some, jlpEnd]
    congr 1; omega

theorem jlp_ps_true {c : Bool} : ∀ {l s r : Bytes}, parseString c l = some (s, r) → parseString true l = some (s, r)
  | [], _, _, h => by rw [jls_ps_nil] at h; cases h
  | b :: l, s, r, h => by
    by_cases h34 : b = 34
    · subst h34; rw [jls_ps_quote] at h ⊢; exact h
    rw [jls_ps_other c b l h34] at h
    rw [jls_ps_other true b l h34]
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨s', r'⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hu' := require_eq_some.mp hu
    rw [Bool.and_eq_true] at hu'
    have : (b != 92 && (true || decide (b ≥ 32))) = true := by rw [hu'.1]; rfl
    rw [this]
    show (parseString true l).bind _ = _
    rw [jlp_ps_true h1]; exact h

/-- A canonical string reads in strict mode only when it has no control byte. -/
theorem jlp_ps_false : ∀ {l s r : Bytes}, parseString true l = some (s, r) →
    parseString false l = if s.all (fun b => decide (32 ≤ b)) then some (s, r) else none
  | [], _, _, h => by rw [jls_ps_nil] at h; cases h
  | b :: l, s, r, h => by
    by_cases h34 : b = 34
    · subst h34; rw [jls_ps_quote] at h ⊢; cases h; rfl
    rw [jls_ps_other true b l h34] at h
    rw [jls_ps_other false b l h34]
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨s', r'⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    have hu' := require_eq_some.mp hu
    rw [Bool.and_eq_true] at hu'
    rw [hu'.1, Bool.true_and, Bool.false_or, jlp_ps_false h1, List.all_cons]
    by_cases hb : 32 ≤ b
    · have e1 : decide (b ≥ 32) = true := decide_eq_true hb
      have e2 : decide (32 ≤ b) = true := decide_eq_true hb
      rw [e1]
      cases (List.all s' fun b => decide (32 ≤ b)) <;> rfl
    · have e1 : decide (b ≥ 32) = false := decide_eq_false hb
      have e2 : decide (32 ≤ b) = false := decide_eq_false hb
      rw [e1]; rfl

/-! ## Numbers and literals -/

theorem jlp_digLen : ∀ l : Bytes, digLen l = (l.takeWhile isDigit).length
  | [] => rfl
  | b :: l => by
    cases h : isDigit b
    · simp only [digLen, h, Bool.false_eq_true, ↓reduceIte, List.takeWhile_cons, List.length_nil]
    · simp only [digLen, h, ↓reduceIte, List.takeWhile_cons, List.length_cons, jlp_digLen l]

theorem jlp_numberEnd {d : Bytes} {i : Nat} (hi : i ≤ d.length) :
    numberEnd d i = (parseNumber (d.drop i)).map fun p => jlpEnd d p.2 := by
  rw [jls_num_eq]
  unfold numberEnd
  rw [jlp_if_neg (by omega), jlp_digLen]
  generalize hs : d.drop i = s
  have hsl : s.length = d.length - i := by rw [← hs, List.length_drop]
  have hT : (s.takeWhile isDigit).length ≤ s.length := (List.takeWhile_prefix (l := s) isDigit).length_le
  have hend : jlpEnd d (s.drop (s.takeWhile isDigit).length) = i + (s.takeWhile isDigit).length := by
    unfold jlpEnd; rw [List.length_drop]; omega
  generalize hn : (s.takeWhile isDigit).length = n at hT hend
  by_cases h0 : n = 0
  · subst h0
    simp only [↓reduceIte, Nat.le_zero, Nat.one_ne_zero, decide_false, Bool.false_and, require,
      Bool.false_eq_true, Option.bind_none, Option.map_none]
  rw [jlp_if_neg h0]
  by_cases h19 : 19 < n
  · rw [jlp_if_pos h19]
    have : decide (n ≤ 19) = false := decide_eq_false (by omega)
    simp only [this, Bool.and_false, Bool.false_and, require, Bool.false_eq_true, ↓reduceIte,
      Option.bind_none, Option.map_none]
  rw [jlp_if_neg h19]
  have hhead : (s.takeWhile isDigit).head? = s.head? := by
    cases s with
    | nil => rfl
    | cons b t =>
      cases hb : isDigit b
      · rw [List.takeWhile_cons, hb] at hn
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil] at hn
        exact absurd hn.symm h0
      · rw [List.takeWhile_cons, hb]; rfl
  have e1 : decide (1 ≤ n) = true := decide_eq_true (by omega)
  have e2 : decide (n ≤ 19) = true := decide_eq_true (by omega)
  rw [hhead, e1, e2, Bool.true_and, Bool.true_and]
  by_cases h48 : s.head? = some 48
  · rw [jlp_if_pos h48, h48]
    by_cases h1 : n = 1
    · subst h1
      have e11 : ((1 : Nat) == 1) = true := rfl
      simp only [↓reduceIte, e11, Bool.true_or, require, Option.bind_some, Option.map_some, hend]
    · have : (n == 1) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h1
      simp only [h1, ↓reduceIte, this, bne_self_eq_false, Bool.or_false, require, Bool.false_eq_true,
        Option.bind_none, Option.map_none]
  · rw [jlp_if_neg h48]
    have : (s.head? != some 48) = true := by simp only [bne_iff_ne, ne_eq]; exact h48
    simp only [this, Bool.or_true, require, ↓reduceIte, Option.bind_some, Option.map_some, hend]

theorem jlp_readExpect_eq (w s : Bytes) :
    readExpect w s = if w.length ≤ s.length ∧ s.take w.length = w then some (s.drop w.length) else none := by
  unfold readExpect
  by_cases h : w.length ≤ s.length ∧ s.take w.length = w
  · have hc : (s.take w.length == w && decide (w.length ≤ s.length)) = true := by
      rw [Bool.and_eq_true]; exact ⟨beq_iff_eq.mpr h.2, decide_eq_true h.1⟩
    rw [jlp_if_pos h, hc]; rfl
  · have hc : (s.take w.length == w && decide (w.length ≤ s.length)) = false := by
      cases h1 : (s.take w.length == w) with
      | false => rfl
      | true =>
        have h2 : ¬ w.length ≤ s.length := fun h3 => h ⟨h3, beq_iff_eq.mp h1⟩
        rw [Bool.true_and]; exact decide_eq_false h2
    rw [jlp_if_neg h, hc]; rfl

theorem jlp_litScan (rest : Bytes) (pos : Nat) (w : Bytes) (ws : List Bytes) :
    litScan rest pos (w :: ws) = match readExpect w rest with
      | some _ => some (pos + w.length)
      | none => litScan rest pos ws := by
  conv => lhs; unfold litScan
  rw [jlp_readExpect_eq]
  by_cases h : w.length ≤ rest.length ∧ rest.take w.length = w
  · rw [jlp_if_pos h, jlp_if_pos h]
  · rw [jlp_if_neg h, jlp_if_neg h]

theorem jlp_readExpect_end {d : Bytes} {i : Nat} {w r : Bytes} (hi : i ≤ d.length) (h : readExpect w (d.drop i) = some r) :
    jlpEnd d r = i + w.length := by
  have hs := jls_readExpect_suf h
  have hl := congrArg List.length hs
  simp only [List.length_drop, List.length_append] at hl
  unfold jlpEnd; omega

theorem jlp_literalEnd {d : Bytes} {i : Nat} (hi : i ≤ d.length) :
    literalEnd d i = (parseLiteral (d.drop i)).map fun p => jlpEnd d p.2 := by
  unfold literalEnd parseLiteral litWords
  rw [jlp_if_neg (by omega), jlp_litScan, jlp_litScan, jlp_litScan]
  cases h1 : readExpect (ascii!"true") (d.drop i) with
  | some r => simp only [Option.map_some, jlp_readExpect_end hi h1]
  | none =>
    cases h2 : readExpect (ascii!"false") (d.drop i) with
    | some r => simp only [Option.map_some, jlp_readExpect_end hi h2]
    | none =>
      cases h3 : readExpect (ascii!"null") (d.drop i) with
      | some r => simp only [Option.map_some, jlp_readExpect_end hi h3]
      | none => rfl

/-! ## Keys -/

/-- The spec's reading of `"key":` at the front of `s`: the key, and the
bytes where its value starts. -/
def jlpKey (c : Bool) : Bytes → Option (Bytes × Bytes)
  | [] => none
  | b :: rest => if b = 34 then
      (parseString c rest).bind fun (k, r1) => (readExpect [58] (ws c r1)).map fun r2 => (k, ws c r2)
    else none

theorem jlp_key_nil (c : Bool) : jlpKey c [] = none := rfl

theorem jlp_key_cons (c : Bool) (b : Nat) (rest : Bytes) : jlpKey c (b :: rest) = if b = 34 then
      (parseString c rest).bind fun (k, r1) => (readExpect [58] (ws c r1)).map fun r2 => (k, ws c r2)
    else none := rfl

theorem jlp_readExpect_one (w b : Nat) (t : Bytes) : readExpect [w] (b :: t) = if b = w then some t else none := by
  rw [jlp_readExpect_eq]
  by_cases h : b = w
  · subst h; rw [jlp_if_pos ⟨by simp, rfl⟩, jlp_if_pos rfl]; rfl
  · rw [jlp_if_neg (fun h' => h (by simpa using h'.2)), jlp_if_neg h]

theorem jlp_readExpect_nil (w : Nat) : readExpect [w] [] = none := by
  rw [jlp_readExpect_eq, jlp_if_neg (by simp)]

theorem jlp_keyEnd {c : Bool} {d : Bytes} {p : Nat} (hp : p ≤ d.length) :
    keyEnd c d p = (jlpKey c (d.drop p)).map fun q => jlpEnd d q.2 := by
  unfold keyEnd
  by_cases hL : d.length ≤ p
  · rw [jlp_if_pos hL, List.drop_eq_nil_of_le hL]; rfl
  rw [jlp_if_neg hL, jlp_drop_cons (by omega), jlp_key_cons]
  by_cases hb : d.getD p 0 = 34
  · rw [jlp_if_neg (fun h => h hb), jlp_if_pos hb, jlp_stringEnd (by omega)]
    cases hs : parseString c (d.drop (p + 1)) with
    | none => rfl
    | some q =>
      obtain ⟨k, r1⟩ := q
      have hsuf : d.drop (p + 1) = (k ++ [34]) ++ r1 := by rw [jls_str_suf c hs]; simp
      obtain ⟨hr1, -, he⟩ := jlp_rest hsuf (by simp)
      simp only [Option.map_some, Option.bind_some]
      generalize d.length - r1.length = e at hr1 he ⊢
      rw [hr1, jlp_ws_drop, jlp_end_drop d he]
      have hw := jlp_wsIn_le (c := c) he
      by_cases hw2 : d.length ≤ wsIn c d e
      · rw [jlp_if_pos hw2, List.drop_eq_nil_of_le hw2, jlp_readExpect_nil]; rfl
      rw [jlp_if_neg hw2, jlp_drop_cons (by omega), jlp_readExpect_one]
      by_cases h58 : d.getD (wsIn c d e) 0 = 58
      · rw [jlp_if_neg (fun h => h h58), jlp_if_pos h58]
        simp only [Option.map_some, jlp_ws_drop]
        rw [jlp_end_drop d (jlp_wsIn_le (by omega))]
      · rw [jlp_if_pos h58, jlp_if_neg h58]; rfl
  · rw [jlp_if_pos hb, jlp_if_neg hb]; rfl

theorem jlp_pm_key (c : Bool) (f dep : Nat) (s : Bytes) :
    jlxMembers c (f + 1) dep s = (jlpKey c s).bind fun (k, r) =>
      (jlxValue c f dep r).bind fun (v, r3) => jlsMTail c f dep k v (ws c r3) := by
  cases s with
  | nil => rw [jls_pm_nil, jlp_key_nil]; rfl
  | cons b rest =>
    rw [jlp_key_cons]
    by_cases hb : b = 34
    · subst hb
      rw [jls_pm_eq, jlp_if_pos rfl]
      cases parseString c rest with
      | none => rfl
      | some q =>
        simp only [Option.bind_some]
        cases readExpect [58] (ws c q.2) with
        | none => rfl
        | some r2 => rfl
    · rw [jls_pm_other c f dep b rest hb, jlp_if_neg hb]; rfl

end C3.Json
