import C3BootProofs.Spec.Json

/-!
# Facts about `Spec/Json.lean` for the JSON link

Equations for each case of `parseValue`, `parseMembers`, and `parseElems`,
and two facts about where a parse stops: what is left over is a suffix of
the input (`jls_suffix`), and a parse that stops inside `x ++ r` reads the
same from `x` alone (`jls_trunc`).
-/

namespace C3.Json

open C3

set_option linter.unusedSimpArgs false

/-! ## Equations -/

/-- The members after one `"key": value`, at the bytes after the value. -/
def jlsMTail (c : Bool) (f dep : Nat) (k : Bytes) (v : Json) : Bytes → Option (List (Bytes × Json) × Bytes)
  | 44 :: r => (parseMembers c f dep (ws c r)).bind fun (more, r) => some ((k, v) :: more, r)
  | 125 :: r => some ([(k, v)], r)
  | _ => none

/-- The items after one value, at the bytes after it. -/
def jlsETail (c : Bool) (f dep : Nat) (v : Json) : Bytes → Option (List Json × Bytes)
  | 44 :: r => (parseElems c f dep (ws c r)).bind fun (more, r) => some (v :: more, r)
  | 93 :: r => some ([v], r)
  | _ => none

theorem jls_pv_zero (c : Bool) (dep : Nat) (s : Bytes) : parseValue c 0 dep s = none := by
  unfold parseValue; rfl

theorem jls_pm_zero (c : Bool) (dep : Nat) (s : Bytes) : parseMembers c 0 dep s = none := by
  unfold parseMembers; rfl

theorem jls_pe_zero (c : Bool) (dep : Nat) (s : Bytes) : parseElems c 0 dep s = none := by
  unfold parseElems; rfl

theorem jls_pv_nil (c : Bool) (f dep : Nat) : parseValue c (f + 1) dep [] = none := by
  unfold parseValue; rfl

theorem jls_pm_nil (c : Bool) (f dep : Nat) : parseMembers c (f + 1) dep [] = none := by
  unfold parseMembers; rfl

theorem jls_pv_str (c : Bool) (f dep : Nat) (rest : Bytes) :
    parseValue c (f + 1) dep (34 :: rest) = (parseString c rest).bind fun (s, r) => some (.str s, r) := by
  unfold parseValue; rfl

theorem jls_pv_obj (c : Bool) (f dep : Nat) (rest : Bytes) :
    parseValue c (f + 1) dep (123 :: rest) = (require (decide (dep ≥ 1))).bind fun _ =>
      match ws c rest with
      | 125 :: r => some (.obj [], r)
      | r => (parseMembers c f (dep - 1) r).bind fun (ms, r) =>
          (require (keysOk c (ms.map (·.1)))).bind fun _ => some (.obj ms, r) := by
  unfold parseValue; rfl

theorem jls_pv_arr (c : Bool) (f dep : Nat) (rest : Bytes) :
    parseValue c (f + 1) dep (91 :: rest) = (require (decide (dep ≥ 1))).bind fun _ =>
      match ws c rest with
      | 93 :: r => some (.arr [], r)
      | r => (parseElems c f (dep - 1) r).bind fun (items, r) => some (.arr items, r) := by
  unfold parseValue; rfl

theorem jls_pv_other (c : Bool) (f dep b : Nat) (tl : Bytes) (h1 : b ≠ 123) (h2 : b ≠ 91) (h3 : b ≠ 34) :
    parseValue c (f + 1) dep (b :: tl) = if isDigit b then parseNumber (b :: tl) else parseLiteral (b :: tl) := by
  unfold parseValue
  split
  · rename_i h; injection h with h; exact absurd h h1
  · rename_i h; injection h with h; exact absurd h h2
  · rename_i h; injection h with h; exact absurd h h3
  · rename_i h; injection h with hb ht; subst hb; subst ht; rfl
  · rename_i h; cases h

theorem jls_pm_eq (c : Bool) (f dep : Nat) (rest : Bytes) :
    parseMembers c (f + 1) dep (34 :: rest) = (parseString c rest).bind fun (k, r) =>
      (readExpect [58] (ws c r)).bind fun r => (parseValue c f dep (ws c r)).bind fun (v, r) =>
        jlsMTail c f dep k v (ws c r) := by
  unfold parseMembers; rfl

theorem jls_pm_other (c : Bool) (f dep b : Nat) (tl : Bytes) (h : b ≠ 34) :
    parseMembers c (f + 1) dep (b :: tl) = none := by
  unfold parseMembers
  split
  · rename_i h'; injection h' with h'; exact absurd h' h
  · rfl

theorem jls_pe_eq (c : Bool) (f dep : Nat) (s : Bytes) :
    parseElems c (f + 1) dep s = (parseValue c f dep s).bind fun (v, r) => jlsETail c f dep v (ws c r) := by
  unfold parseElems; rfl

/-! ## Scanners -/

theorem jls_dropWhile_suf (p : Nat → Bool) : ∀ s : Bytes, ∃ x, s = x ++ s.dropWhile p
  | [] => ⟨[], rfl⟩
  | b :: s => by
    cases hb : p b
    · simp only [List.dropWhile_cons, hb, Bool.false_eq_true, ↓reduceIte]; exact ⟨[], rfl⟩
    · simp only [List.dropWhile_cons, hb, ↓reduceIte]
      obtain ⟨x, hx⟩ := jls_dropWhile_suf p s
      exact ⟨b :: x, by rw [List.cons_append, ← hx]⟩

theorem jls_ws_suf (c : Bool) (s : Bytes) : ∃ x, s = x ++ ws c s := by
  unfold ws; cases c
  · exact jls_dropWhile_suf isWs s
  · exact ⟨[], rfl⟩

theorem jls_dropWhile_trunc (p : Nat → Bool) (r : Bytes) :
    ∀ (y z : Bytes), (y ++ r).dropWhile p = z ++ r → y.dropWhile p = z
  | [], z, h => by
    rw [List.nil_append] at h
    obtain ⟨x, hx⟩ := jls_dropWhile_suf p r
    have h1 := congrArg List.length hx
    rw [h, List.length_append, List.length_append] at h1
    have : z.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp this]; rfl
  | b :: y, z, h => by
    rw [List.cons_append, List.dropWhile_cons] at h
    rw [List.dropWhile_cons]
    cases hb : p b
    · rw [hb] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact List.append_cancel_right (by rw [List.cons_append]; exact h)
    · rw [hb] at h
      simp only [↓reduceIte] at h ⊢
      exact jls_dropWhile_trunc p r y z h

theorem jls_ws_trunc (c : Bool) (y r z : Bytes) (h : ws c (y ++ r) = z ++ r) : ws c y = z := by
  unfold ws at h ⊢; cases c
  · exact jls_dropWhile_trunc isWs r y z h
  · exact List.append_cancel_right h

theorem jls_ps_nil (c : Bool) : parseString c [] = none := by
  unfold parseString; rfl

theorem jls_ps_quote (c : Bool) (rest : Bytes) : parseString c (34 :: rest) = some ([], rest) := by
  unfold parseString; rfl

theorem jls_ps_other (c : Bool) (b : Nat) (rest : Bytes) (h : b ≠ 34) :
    parseString c (b :: rest) = (require (b != 92 && (c || decide (b ≥ 32)))).bind fun _ =>
      (parseString c rest).bind fun (s, r) => some (b :: s, r) := by
  conv => lhs; unfold parseString
  split
  · rename_i h'; cases h'
  · rename_i h'; injection h' with hb; exact absurd hb h
  · rename_i h'; injection h' with hb hs; subst hb; subst hs; rfl

theorem jls_str_suf (c : Bool) : ∀ {s st r : Bytes}, parseString c s = some (st, r) → s = st ++ 34 :: r
  | [], _, _, h => by rw [jls_ps_nil] at h; cases h
  | b :: s, st, r, h => by
    by_cases hb : b = 34
    · subst hb; rw [jls_ps_quote] at h; cases h; rfl
    · rw [jls_ps_other c b s hb] at h
      obtain ⟨u, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨st', r'⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      cases h2
      rw [jls_str_suf c h1]; rfl

theorem jls_str_trunc (c : Bool) (r : Bytes) :
    ∀ {y st z : Bytes}, parseString c (y ++ r) = some (st, z ++ r) → parseString c y = some (st, z)
  | [], st, z, h => by
    have h1 := congrArg List.length (jls_str_suf c h)
    simp only [List.nil_append, List.length_append, List.length_cons] at h1
    omega
  | b :: y, st, z, h => by
    rw [List.cons_append] at h
    by_cases hb : b = 34
    · subst hb; rw [jls_ps_quote] at h; rw [jls_ps_quote]
      have h' := Option.some.inj h
      injection h' with h1 h2
      rw [h1, List.append_cancel_right h2]
    · rw [jls_ps_other c b _ hb] at h; rw [jls_ps_other c b _ hb]
      obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨st', r'⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      cases h2
      rw [hu, Option.bind_some, jls_str_trunc c r h1]; rfl

theorem jls_readExpect_suf {w s r : Bytes} (h : readExpect w s = some r) : s = w ++ r := by
  unfold readExpect at h
  split at h
  · rename_i hc
    cases h
    have ht : s.take w.length = w := by
      have := (Bool.and_eq_true _ _).mp hc
      exact beq_iff_eq.mp this.1
    conv => lhs; rw [← List.take_append_drop w.length s]
    rw [ht]
  · cases h

theorem jls_readExpect_self (w z : Bytes) : readExpect w (w ++ z) = some z := by
  have hc : (w.take w.length == w && decide (w.length ≤ (w ++ z).length)) = true := by
    rw [List.take_length, Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr rfl, decide_eq_true (by rw [List.length_append]; exact Nat.le_add_right _ _)⟩
  unfold readExpect
  rw [List.take_left, List.drop_left]
  rw [List.take_length] at hc
  rw [hc]; rfl

theorem jls_readExpect_trunc {w y r z : Bytes} (h : readExpect w (y ++ r) = some (z ++ r)) :
    readExpect w y = some z := by
  have hs := jls_readExpect_suf h
  have hy : y = w ++ z := by
    rw [← List.append_assoc] at hs
    exact List.append_cancel_right hs
  subst hy
  exact jls_readExpect_self w z

theorem jls_readExpect_ext {w y z : Bytes} (r : Bytes) (h : readExpect w y = some z) :
    readExpect w (y ++ r) = some (z ++ r) := by
  have hy := jls_readExpect_suf h
  subst hy
  rw [List.append_assoc]
  exact jls_readExpect_self w (z ++ r)

theorem jls_tw_split (p : Nat → Bool) (r : Bytes) : ∀ y : Bytes,
    ((y ++ r).takeWhile p = y.takeWhile p ∧ (y.takeWhile p).length < y.length) ∨
      (y.takeWhile p = y ∧ (y ++ r).takeWhile p = y ++ r.takeWhile p)
  | [] => .inr ⟨rfl, rfl⟩
  | b :: y => by
    cases hb : p b
    · left
      simp only [List.cons_append, List.takeWhile_cons, hb, Bool.false_eq_true, ↓reduceIte, List.length_nil,
        List.length_cons]
      exact ⟨by trivial, Nat.zero_lt_succ _⟩
    · simp only [List.cons_append, List.takeWhile_cons, hb, ↓reduceIte, List.length_cons]
      rcases jls_tw_split p r y with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [h1]; exact ⟨rfl, Nat.succ_lt_succ h2⟩
      · right; rw [h1, h2]; exact ⟨rfl, rfl⟩

theorem jls_num_eq (s : Bytes) : parseNumber s =
    (require (1 ≤ (s.takeWhile isDigit).length && (s.takeWhile isDigit).length ≤ 19 &&
      ((s.takeWhile isDigit).length == 1 || (s.takeWhile isDigit).head? != some 48))).bind fun _ =>
      some (.num (digitsValue (s.takeWhile isDigit)), s.drop (s.takeWhile isDigit).length) := rfl

theorem jls_num_suf {s r : Bytes} {j : Json} (h : parseNumber s = some (j, r)) : ∃ x, x ≠ [] ∧ s = x ++ r := by
  rw [jls_num_eq] at h
  obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  have h1 := require_eq_some.mp hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  have hl := (List.takeWhile_prefix (l := s) isDigit).length_le
  refine ⟨s.take (s.takeWhile isDigit).length, ?_, (List.take_append_drop _ s).symm⟩
  intro h0
  have := congrArg List.length h0
  rw [List.length_take, List.length_nil] at this
  omega

theorem jls_num_trunc {y r z : Bytes} {j : Json} (h : parseNumber (y ++ r) = some (j, z ++ r)) :
    parseNumber y = some (j, z) := by
  rw [jls_num_eq] at h ⊢
  rcases jls_tw_split isDigit r y with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at h
    rw [List.drop_append_of_le_length (Nat.le_of_lt h2)] at h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hu, Option.bind_some]
    have h' := Option.some.inj h
    injection h' with h3 h4
    rw [h3, List.append_cancel_right h4]
  · rw [h2] at h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    have h' := Option.some.inj h
    injection h' with h3 h4
    rw [List.length_append, ← List.drop_drop, List.drop_left] at h4
    have hl := congrArg List.length h4
    have hT := (List.takeWhile_prefix (l := r) isDigit).length_le
    rw [List.length_drop, List.length_append] at hl
    have hz : z = [] := List.length_eq_zero_iff.mp (by omega)
    have hr : r.takeWhile isDigit = [] := List.length_eq_zero_iff.mp (by omega)
    subst hz
    rw [hr, List.append_nil] at hu h3
    rw [h1, hu, Option.bind_some, List.drop_length, ← h3]

/-- How `parseLiteral` read `s`. -/
theorem jls_lit_inv {s r : Bytes} {j : Json} (h : parseLiteral s = some (j, r)) :
    (readExpect (ascii!"true") s = some r ∧ j = .bool true) ∨
    (readExpect (ascii!"true") s = none ∧ readExpect (ascii!"false") s = some r ∧ j = .bool false) ∨
    (readExpect (ascii!"true") s = none ∧ readExpect (ascii!"false") s = none ∧
      readExpect (ascii!"null") s = some r ∧ j = .null) := by
  unfold parseLiteral at h
  cases h1 : readExpect (ascii!"true") s with
  | some a =>
    rw [h1] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact .inl ⟨rfl, rfl⟩
  | none =>
    cases h2 : readExpect (ascii!"false") s with
    | some b =>
      rw [h1, h2] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact .inr (.inl ⟨rfl, rfl, rfl⟩)
    | none =>
      cases h3 : readExpect (ascii!"null") s with
      | some n =>
        rw [h1, h2, h3] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact .inr (.inr ⟨rfl, rfl, rfl, rfl⟩)
      | none => rw [h1, h2, h3] at h; cases h

theorem jls_lit_suf {s r : Bytes} {j : Json} (h : parseLiteral s = some (j, r)) : ∃ x, x ≠ [] ∧ s = x ++ r := by
  rcases jls_lit_inv h with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, -, h1, -⟩ <;>
    exact ⟨_, List.cons_ne_nil _ _, jls_readExpect_suf h1⟩

theorem jls_readExpect_none_trunc {w y : Bytes} (r : Bytes) (h : readExpect w (y ++ r) = none) :
    readExpect w y = none := by
  cases h1 : readExpect w y
  · rfl
  · rw [jls_readExpect_ext r h1] at h; cases h

theorem jls_lit_trunc {y r z : Bytes} {j : Json} (h : parseLiteral (y ++ r) = some (j, z ++ r)) :
    parseLiteral y = some (j, z) := by
  unfold parseLiteral
  rcases jls_lit_inv h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · rw [jls_readExpect_trunc h1, h2]
  · rw [jls_readExpect_none_trunc r h1, jls_readExpect_trunc h2, h3]
  · rw [jls_readExpect_none_trunc r h1, jls_readExpect_none_trunc r h2, jls_readExpect_trunc h3, h4]

/-! ## Inversion -/

theorem jls_pv_inv {c : Bool} {f dep : Nat} {s r : Bytes} {j : Json} (h : parseValue c (f + 1) dep s = some (j, r)) :
    (∃ rest, s = 123 :: rest ∧ 1 ≤ dep ∧ ((j = .obj [] ∧ ws c rest = 125 :: r) ∨
      ∃ ms, j = .obj ms ∧ (∀ r', ws c rest ≠ 125 :: r') ∧ parseMembers c f (dep - 1) (ws c rest) = some (ms, r) ∧
        keysOk c (ms.map (·.1)) = true)) ∨
    (∃ rest, s = 91 :: rest ∧ 1 ≤ dep ∧ ((j = .arr [] ∧ ws c rest = 93 :: r) ∨
      ∃ items, j = .arr items ∧ (∀ r', ws c rest ≠ 93 :: r') ∧
        parseElems c f (dep - 1) (ws c rest) = some (items, r))) ∨
    (∃ rest st, s = 34 :: rest ∧ j = .str st ∧ parseString c rest = some (st, r)) ∨
    (∃ b tl, s = b :: tl ∧ b ≠ 123 ∧ b ≠ 91 ∧ b ≠ 34 ∧ isDigit b = true ∧ parseNumber s = some (j, r)) ∨
    (∃ b tl, s = b :: tl ∧ b ≠ 123 ∧ b ≠ 91 ∧ b ≠ 34 ∧ isDigit b = false ∧ parseLiteral s = some (j, r)) := by
  match s with
  | [] => rw [jls_pv_nil] at h; cases h
  | b :: tl =>
    by_cases h1 : b = 123
    · subst h1
      rw [jls_pv_obj] at h
      obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
      refine .inl ⟨tl, rfl, of_decide_eq_true (require_eq_some.mp hu), ?_⟩
      split at h
      · rename_i r' hw
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact .inl ⟨rfl, hw⟩
      · rename_i r' hw
        obtain ⟨⟨ms, r''⟩, hm, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨u', hk, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr ⟨ms, rfl, hw, hm, require_eq_some.mp hk⟩
    by_cases h2 : b = 91
    · subst h2
      rw [jls_pv_arr] at h
      obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
      refine .inr (.inl ⟨tl, rfl, of_decide_eq_true (require_eq_some.mp hu), ?_⟩)
      split at h
      · rename_i r' hw
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact .inl ⟨rfl, hw⟩
      · rename_i r' hw
        obtain ⟨⟨it, r''⟩, hm, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr ⟨it, rfl, hw, hm⟩
    by_cases h3 : b = 34
    · subst h3
      rw [jls_pv_str] at h
      obtain ⟨⟨st, r'⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr (.inr (.inl ⟨tl, st, rfl, rfl, hs⟩))
    rw [jls_pv_other c f dep b tl h1 h2 h3] at h
    cases hb : isDigit b
    · rw [hb] at h; exact .inr (.inr (.inr (.inr ⟨b, tl, rfl, h1, h2, h3, hb, h⟩)))
    · rw [hb] at h; exact .inr (.inr (.inr (.inl ⟨b, tl, rfl, h1, h2, h3, hb, h⟩)))

theorem jls_pm_inv {c : Bool} {f dep : Nat} {s r : Bytes} {ms : List (Bytes × Json)}
    (h : parseMembers c (f + 1) dep s = some (ms, r)) :
    ∃ rest k r1 r2 v r3, s = 34 :: rest ∧ parseString c rest = some (k, r1) ∧ readExpect [58] (ws c r1) = some r2 ∧
      parseValue c f dep (ws c r2) = some (v, r3) ∧ jlsMTail c f dep k v (ws c r3) = some (ms, r) := by
  match s with
  | [] => rw [jls_pm_nil] at h; cases h
  | b :: tl =>
    by_cases hb : b = 34
    · subst hb
      rw [jls_pm_eq] at h
      obtain ⟨⟨k, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r2, h2, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨v, r3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨tl, k, r1, r2, v, r3, rfl, h1, h2, h3, h⟩
    · rw [jls_pm_other c f dep b tl hb] at h; cases h

theorem jls_mt_inv {c : Bool} {f dep : Nat} {k : Bytes} {v : Json} {s r : Bytes} {ms : List (Bytes × Json)}
    (h : jlsMTail c f dep k v s = some (ms, r)) :
    (∃ s' more, s = 44 :: s' ∧ parseMembers c f dep (ws c s') = some (more, r) ∧ ms = (k, v) :: more) ∨
      (s = 125 :: r ∧ ms = [(k, v)]) := by
  unfold jlsMTail at h
  split at h
  · rename_i s'
    obtain ⟨⟨more, r'⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨s', more, rfl, h1, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, rfl⟩
  · cases h

theorem jls_pe_inv {c : Bool} {f dep : Nat} {s r : Bytes} {js : List Json}
    (h : parseElems c (f + 1) dep s = some (js, r)) :
    ∃ v r1, parseValue c f dep s = some (v, r1) ∧ jlsETail c f dep v (ws c r1) = some (js, r) := by
  rw [jls_pe_eq] at h
  obtain ⟨⟨v, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨v, r1, h1, h⟩

theorem jls_et_inv {c : Bool} {f dep : Nat} {v : Json} {s r : Bytes} {js : List Json}
    (h : jlsETail c f dep v s = some (js, r)) :
    (∃ s' more, s = 44 :: s' ∧ parseElems c f dep (ws c s') = some (more, r) ∧ js = v :: more) ∨
      (s = 93 :: r ∧ js = [v]) := by
  unfold jlsETail at h
  split at h
  · rename_i s'
    obtain ⟨⟨more, r'⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨s', more, rfl, h1, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr ⟨rfl, rfl⟩
  · cases h

/-! ## Suffixes -/

theorem jls_sx_trans {s m r x y : Bytes} (h1 : s = x ++ m) (h2 : m = y ++ r) : s = (x ++ y) ++ r := by
  subst h1; subst h2; rw [List.append_assoc]

theorem jls_sx_ne {x y : Bytes} (h : x ≠ []) : x ++ y ≠ [] := by
  intro h'; exact h (List.append_eq_nil_iff.mp h').1

/-- What a parse leaves over is a proper suffix of its input. -/
theorem jls_suffix (c : Bool) : ∀ f,
    (∀ {dep s j r}, parseValue c f dep s = some (j, r) → ∃ x, x ≠ [] ∧ s = x ++ r) ∧
    (∀ {dep s ms r}, parseMembers c f dep s = some (ms, r) → ∃ x, x ≠ [] ∧ s = x ++ r) ∧
    (∀ {dep s js r}, parseElems c f dep s = some (js, r) → ∃ x, x ≠ [] ∧ s = x ++ r)
  | 0 => by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [jls_pv_zero] at h; cases h
    · rw [jls_pm_zero] at h; cases h
    · rw [jls_pe_zero] at h; cases h
  | f + 1 => by
    obtain ⟨ihv, ihm, ihe⟩ := jls_suffix c f
    refine ⟨fun {dep s j r} h => ?_, fun {dep s ms r} h => ?_, fun {dep s js r} h => ?_⟩
    · rcases jls_pv_inv h with ⟨rest, rfl, -, ⟨-, hw⟩ | ⟨ms, -, -, hm, -⟩⟩ | ⟨rest, rfl, -, ⟨-, hw⟩ | ⟨it, -, -, he⟩⟩ |
          ⟨rest, st, rfl, -, hs⟩ | ⟨b, tl, rfl, -, -, -, -, hn⟩ | ⟨b, tl, rfl, -, -, -, -, hl⟩
      · obtain ⟨x, hx⟩ := jls_ws_suf c rest
        rw [hw] at hx
        exact ⟨123 :: (x ++ [125]), List.cons_ne_nil _ _, by rw [hx]; simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]⟩
      · obtain ⟨x, hx⟩ := jls_ws_suf c rest
        obtain ⟨y, -, hy⟩ := ihm hm
        exact ⟨123 :: (x ++ y), List.cons_ne_nil _ _, by rw [jls_sx_trans hx hy]; rfl⟩
      · obtain ⟨x, hx⟩ := jls_ws_suf c rest
        rw [hw] at hx
        exact ⟨91 :: (x ++ [93]), List.cons_ne_nil _ _, by rw [hx]; simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]⟩
      · obtain ⟨x, hx⟩ := jls_ws_suf c rest
        obtain ⟨y, -, hy⟩ := ihe he
        exact ⟨91 :: (x ++ y), List.cons_ne_nil _ _, by rw [jls_sx_trans hx hy]; rfl⟩
      · exact ⟨34 :: (st ++ [34]), List.cons_ne_nil _ _, by rw [jls_str_suf c hs]; simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]⟩
      · exact jls_num_suf hn
      · exact jls_lit_suf hl
    · obtain ⟨rest, k, r1, r2, v, r3, rfl, h1, h2, h3, h4⟩ := jls_pm_inv h
      have e1 := jls_str_suf c h1
      obtain ⟨a1, e2⟩ := jls_ws_suf c r1
      have e3 := jls_readExpect_suf h2
      obtain ⟨a2, e4⟩ := jls_ws_suf c r2
      obtain ⟨a3, -, e5⟩ := ihv h3
      obtain ⟨a4, e6⟩ := jls_ws_suf c r3
      have e7 : ∃ a5, ws c r3 = a5 ++ r := by
        rcases jls_mt_inv h4 with ⟨s', more, hs, hm, -⟩ | ⟨hs, -⟩
        · obtain ⟨b1, hb1⟩ := jls_ws_suf c s'
          obtain ⟨b2, -, hb2⟩ := ihm hm
          exact ⟨44 :: (b1 ++ b2), by rw [hs, jls_sx_trans hb1 hb2]; rfl⟩
        · exact ⟨[125], hs⟩
      obtain ⟨a5, e7⟩ := e7
      refine ⟨34 :: (k ++ [34] ++ a1 ++ [58] ++ a2 ++ a3 ++ a4 ++ a5), List.cons_ne_nil _ _, ?_⟩
      rw [e1, e2, e3, e4, e5, e6, e7]
      simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    · obtain ⟨v, r1, h1, h2⟩ := jls_pe_inv h
      obtain ⟨a1, ha1, e1⟩ := ihv h1
      obtain ⟨a2, e2⟩ := jls_ws_suf c r1
      have e3 : ∃ a3, ws c r1 = a3 ++ r := by
        rcases jls_et_inv h2 with ⟨s', more, hs, hm, -⟩ | ⟨hs, -⟩
        · obtain ⟨b1, hb1⟩ := jls_ws_suf c s'
          obtain ⟨b2, -, hb2⟩ := ihe hm
          exact ⟨44 :: (b1 ++ b2), by rw [hs, jls_sx_trans hb1 hb2]; rfl⟩
        · exact ⟨[93], hs⟩
      obtain ⟨a3, e3⟩ := e3
      exact ⟨a1 ++ (a2 ++ a3), jls_sx_ne ha1, by rw [e1, e2, e3, List.append_assoc, List.append_assoc]⟩

theorem jls_pv_suf {c : Bool} {f dep : Nat} {s r : Bytes} {j : Json} (h : parseValue c f dep s = some (j, r)) :
    ∃ x, x ≠ [] ∧ s = x ++ r := (jls_suffix c f).1 h

theorem jls_pm_suf {c : Bool} {f dep : Nat} {s r : Bytes} {ms : List (Bytes × Json)}
    (h : parseMembers c f dep s = some (ms, r)) : ∃ x, x ≠ [] ∧ s = x ++ r := (jls_suffix c f).2.1 h

theorem jls_pe_suf {c : Bool} {f dep : Nat} {s r : Bytes} {js : List Json}
    (h : parseElems c f dep s = some (js, r)) : ∃ x, x ≠ [] ∧ s = x ++ r := (jls_suffix c f).2.2 h

theorem jls_mt_suf {c : Bool} {f dep : Nat} {k : Bytes} {v : Json} {s r : Bytes} {ms : List (Bytes × Json)}
    (h : jlsMTail c f dep k v s = some (ms, r)) : ∃ x, x ≠ [] ∧ s = x ++ r := by
  rcases jls_mt_inv h with ⟨s', more, hs, hm, -⟩ | ⟨hs, -⟩
  · obtain ⟨b1, hb1⟩ := jls_ws_suf c s'
    obtain ⟨b2, -, hb2⟩ := jls_pm_suf hm
    exact ⟨44 :: (b1 ++ b2), List.cons_ne_nil _ _, by rw [hs, jls_sx_trans hb1 hb2]; rfl⟩
  · exact ⟨[125], List.cons_ne_nil _ _, hs⟩

theorem jls_et_suf {c : Bool} {f dep : Nat} {v : Json} {s r : Bytes} {js : List Json}
    (h : jlsETail c f dep v s = some (js, r)) : ∃ x, x ≠ [] ∧ s = x ++ r := by
  rcases jls_et_inv h with ⟨s', more, hs, hm, -⟩ | ⟨hs, -⟩
  · obtain ⟨b1, hb1⟩ := jls_ws_suf c s'
    obtain ⟨b2, -, hb2⟩ := jls_pe_suf hm
    exact ⟨44 :: (b1 ++ b2), List.cons_ne_nil _ _, by rw [hs, jls_sx_trans hb1 hb2]; rfl⟩
  · exact ⟨[93], List.cons_ne_nil _ _, hs⟩

/-! ## Constructors -/

theorem jls_pv_obj_empty_mk {c : Bool} {f dep : Nat} {rest r : Bytes} (hd : 1 ≤ dep) (hw : ws c rest = 125 :: r) :
    parseValue c (f + 1) dep (123 :: rest) = some (.obj [], r) := by
  rw [jls_pv_obj, hw]
  simp only [require, ge_iff_le, hd, decide_true, ↓reduceIte, Option.bind_some]

theorem jls_pv_obj_mk {c : Bool} {f dep : Nat} {rest r : Bytes} {ms : List (Bytes × Json)} (hd : 1 ≤ dep)
    (hw : ∀ r', ws c rest ≠ 125 :: r') (hm : parseMembers c f (dep - 1) (ws c rest) = some (ms, r))
    (hk : keysOk c (ms.map (·.1)) = true) : parseValue c (f + 1) dep (123 :: rest) = some (.obj ms, r) := by
  have hr : require (decide (dep ≥ 1)) = some () := by rw [require_eq_some]; exact decide_eq_true hd
  rw [jls_pv_obj, hr, Option.bind_some]
  revert hw hm; generalize ws c rest = w; intro hw hm
  split
  · rename_i r'; exact absurd rfl (hw r')
  · rw [hm, Option.bind_some]
    show (require (keysOk c (ms.map (·.1)))).bind _ = _
    rw [hk]; rfl

theorem jls_pv_arr_empty_mk {c : Bool} {f dep : Nat} {rest r : Bytes} (hd : 1 ≤ dep) (hw : ws c rest = 93 :: r) :
    parseValue c (f + 1) dep (91 :: rest) = some (.arr [], r) := by
  rw [jls_pv_arr, hw]
  simp only [require, ge_iff_le, hd, decide_true, ↓reduceIte, Option.bind_some]

theorem jls_pv_arr_mk {c : Bool} {f dep : Nat} {rest r : Bytes} {js : List Json} (hd : 1 ≤ dep)
    (hw : ∀ r', ws c rest ≠ 93 :: r') (he : parseElems c f (dep - 1) (ws c rest) = some (js, r)) :
    parseValue c (f + 1) dep (91 :: rest) = some (.arr js, r) := by
  have hr : require (decide (dep ≥ 1)) = some () := by rw [require_eq_some]; exact decide_eq_true hd
  rw [jls_pv_arr, hr, Option.bind_some]
  revert hw he; generalize ws c rest = w; intro hw he
  split
  · rename_i r'; exact absurd rfl (hw r')
  · rw [he]; rfl

theorem jls_pv_str_mk {c : Bool} {f dep : Nat} {rest st r : Bytes} (hs : parseString c rest = some (st, r)) :
    parseValue c (f + 1) dep (34 :: rest) = some (.str st, r) := by
  rw [jls_pv_str, hs]; rfl

theorem jls_pv_num_mk {c : Bool} {f dep b : Nat} {tl r : Bytes} {j : Json} (h1 : b ≠ 123) (h2 : b ≠ 91) (h3 : b ≠ 34)
    (hd : isDigit b = true) (hn : parseNumber (b :: tl) = some (j, r)) : parseValue c (f + 1) dep (b :: tl) = some (j, r) := by
  rw [jls_pv_other c f dep b tl h1 h2 h3, hd]; exact hn

theorem jls_pv_lit_mk {c : Bool} {f dep b : Nat} {tl r : Bytes} {j : Json} (h1 : b ≠ 123) (h2 : b ≠ 91) (h3 : b ≠ 34)
    (hd : isDigit b = false) (hn : parseLiteral (b :: tl) = some (j, r)) : parseValue c (f + 1) dep (b :: tl) = some (j, r) := by
  rw [jls_pv_other c f dep b tl h1 h2 h3, hd]; exact hn

theorem jls_pm_mk {c : Bool} {f dep : Nat} {rest k r1 r2 r3 r : Bytes} {v : Json} {ms : List (Bytes × Json)}
    (h1 : parseString c rest = some (k, r1)) (h2 : readExpect [58] (ws c r1) = some r2)
    (h3 : parseValue c f dep (ws c r2) = some (v, r3)) (h4 : jlsMTail c f dep k v (ws c r3) = some (ms, r)) :
    parseMembers c (f + 1) dep (34 :: rest) = some (ms, r) := by
  rw [jls_pm_eq, h1, Option.bind_some]
  simp only [h2, Option.bind_some, h3]
  exact h4

theorem jls_mt_comma_mk {c : Bool} {f dep : Nat} {k : Bytes} {v : Json} {s' r : Bytes} {more : List (Bytes × Json)}
    (h : parseMembers c f dep (ws c s') = some (more, r)) : jlsMTail c f dep k v (44 :: s') = some ((k, v) :: more, r) := by
  show (parseMembers c f dep (ws c s')).bind _ = _
  rw [h]; rfl

theorem jls_mt_close_mk (c : Bool) (f dep : Nat) (k : Bytes) (v : Json) (r : Bytes) :
    jlsMTail c f dep k v (125 :: r) = some ([(k, v)], r) := by
  unfold jlsMTail; rfl

theorem jls_pe_mk {c : Bool} {f dep : Nat} {s r1 r : Bytes} {v : Json} {js : List Json}
    (h1 : parseValue c f dep s = some (v, r1)) (h2 : jlsETail c f dep v (ws c r1) = some (js, r)) :
    parseElems c (f + 1) dep s = some (js, r) := by
  rw [jls_pe_eq, h1, Option.bind_some]; exact h2

theorem jls_et_comma_mk {c : Bool} {f dep : Nat} {v : Json} {s' r : Bytes} {more : List Json}
    (h : parseElems c f dep (ws c s') = some (more, r)) : jlsETail c f dep v (44 :: s') = some (v :: more, r) := by
  show (parseElems c f dep (ws c s')).bind _ = _
  rw [h]; rfl

theorem jls_et_close_mk (c : Bool) (f dep : Nat) (v : Json) (r : Bytes) :
    jlsETail c f dep v (93 :: r) = some ([v], r) := by
  unfold jlsETail; rfl

/-! ## Truncation -/

theorem jls_len_contra {r y t : Bytes} (h : r = y ++ (t ++ r)) (hy : y ≠ []) : False := by
  have h1 := congrArg List.length h
  simp only [List.length_append] at h1
  have : y.length = 0 := by omega
  exact hy (List.length_eq_zero_iff.mp this)

/-- The input of a parse that leaves `t ++ r` starts with a byte before `r`. -/
theorem jls_head {x r t s : Bytes} (hs : x ++ r = s) (h : ∃ y, y ≠ [] ∧ s = y ++ (t ++ r)) :
    ∃ b x', x = b :: x' := by
  obtain ⟨y, hy, e⟩ := h
  match x with
  | [] => rw [List.nil_append] at hs; subst hs; exact (jls_len_contra e hy).elim
  | b :: x' => exact ⟨b, x', rfl⟩

theorem jls_mid {w q t r : Bytes} (h : w = q ++ (t ++ r)) : w = (q ++ t) ++ r := by
  rw [h, List.append_assoc]

/-- A parse that stops inside `x ++ r` reads the same from `x`. -/
theorem jls_trunc (c : Bool) (r : Bytes) : ∀ f,
    (∀ {dep x t j}, parseValue c f dep (x ++ r) = some (j, t ++ r) → parseValue c f dep x = some (j, t)) ∧
    (∀ {dep x t ms}, parseMembers c f dep (x ++ r) = some (ms, t ++ r) → parseMembers c f dep x = some (ms, t)) ∧
    (∀ {dep x t js}, parseElems c f dep (x ++ r) = some (js, t ++ r) → parseElems c f dep x = some (js, t))
  | 0 => by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [jls_pv_zero] at h; cases h
    · rw [jls_pm_zero] at h; cases h
    · rw [jls_pe_zero] at h; cases h
  | f + 1 => by
    obtain ⟨ihv, ihm, ihe⟩ := jls_trunc c r f
    have mt : ∀ {dep k v y t ms}, jlsMTail c f dep k v (y ++ r) = some (ms, t ++ r) →
        jlsMTail c f dep k v y = some (ms, t) := by
      intro dep k v y t ms h
      obtain ⟨b, y', rfl⟩ := jls_head rfl (jls_mt_suf h)
      rcases jls_mt_inv h with ⟨s', more, hs, hm, rfl⟩ | ⟨hs, rfl⟩
      · rw [List.cons_append] at hs; injection hs with hb hs; subst hb; subst hs
        obtain ⟨q, -, e⟩ := jls_pm_suf hm
        have e' := jls_ws_trunc c y' r _ (jls_mid e)
        rw [jls_mid e] at hm
        exact jls_mt_comma_mk (by rw [e']; exact ihm hm)
      · rw [List.cons_append] at hs; injection hs with hb hs; subst hb
        rw [List.append_cancel_right hs]; exact jls_mt_close_mk c f dep k v t
    have et : ∀ {dep v y t js}, jlsETail c f dep v (y ++ r) = some (js, t ++ r) →
        jlsETail c f dep v y = some (js, t) := by
      intro dep v y t js h
      obtain ⟨b, y', rfl⟩ := jls_head rfl (jls_et_suf h)
      rcases jls_et_inv h with ⟨s', more, hs, hm, rfl⟩ | ⟨hs, rfl⟩
      · rw [List.cons_append] at hs; injection hs with hb hs; subst hb; subst hs
        obtain ⟨q, -, e⟩ := jls_pe_suf hm
        have e' := jls_ws_trunc c y' r _ (jls_mid e)
        rw [jls_mid e] at hm
        exact jls_et_comma_mk (by rw [e']; exact ihe hm)
      · rw [List.cons_append] at hs; injection hs with hb hs; subst hb
        rw [List.append_cancel_right hs]; exact jls_et_close_mk c f dep v t
    refine ⟨fun {dep x t j} h => ?_, fun {dep x t ms} h => ?_, fun {dep x t js} h => ?_⟩
    · obtain ⟨b, x', rfl⟩ := jls_head rfl (jls_pv_suf h)
      rw [List.cons_append] at h
      rcases jls_pv_inv h with ⟨rest, hs, hd, ⟨rfl, hw⟩ | ⟨ms, rfl, hw, hm, hk⟩⟩ |
          ⟨rest, hs, hd, ⟨rfl, hw⟩ | ⟨it, rfl, hw, he⟩⟩ | ⟨rest, st, hs, rfl, hst⟩ |
          ⟨b', tl, hs, h1, h2, h3, hdg, hn⟩ | ⟨b', tl, hs, h1, h2, h3, hdg, hl⟩
      · injection hs with hb hs; subst hb; subst hs
        exact jls_pv_obj_empty_mk hd (jls_ws_trunc c x' r _ (by rw [hw]; rfl))
      · injection hs with hb hs; subst hb; subst hs
        obtain ⟨q, -, e⟩ := jls_pm_suf hm
        have e' := jls_ws_trunc c x' r _ (jls_mid e)
        rw [jls_mid e] at hm
        refine jls_pv_obj_mk hd (fun r' h' => ?_) (by rw [e']; exact ihm hm) hk
        rw [e'] at h'; exact hw (r' ++ r) (by rw [jls_mid e, h']; rfl)
      · injection hs with hb hs; subst hb; subst hs
        exact jls_pv_arr_empty_mk hd (jls_ws_trunc c x' r _ (by rw [hw]; rfl))
      · injection hs with hb hs; subst hb; subst hs
        obtain ⟨q, -, e⟩ := jls_pe_suf he
        have e' := jls_ws_trunc c x' r _ (jls_mid e)
        rw [jls_mid e] at he
        refine jls_pv_arr_mk hd (fun r' h' => ?_) (by rw [e']; exact ihe he)
        rw [e'] at h'; exact hw (r' ++ r) (by rw [jls_mid e, h']; rfl)
      · injection hs with hb hs; subst hb; subst hs
        exact jls_pv_str_mk (jls_str_trunc c r hst)
      · injection hs with hb hs; subst hb; subst hs
        rw [← List.cons_append] at hn
        exact jls_pv_num_mk h1 h2 h3 hdg (jls_num_trunc hn)
      · injection hs with hb hs; subst hb; subst hs
        rw [← List.cons_append] at hl
        exact jls_pv_lit_mk h1 h2 h3 hdg (jls_lit_trunc hl)
    · obtain ⟨b, x', rfl⟩ := jls_head rfl (jls_pm_suf h)
      rw [List.cons_append] at h
      obtain ⟨rest, k, r1, r2, v, r3, hs, h1, h2, h3, h4⟩ := jls_pm_inv h
      injection hs with hb hs; subst hb; subst hs
      obtain ⟨a5, -, e7⟩ := jls_mt_suf h4
      obtain ⟨a4, e6⟩ := jls_ws_suf c r3
      obtain ⟨a3, -, e5⟩ := jls_pv_suf h3
      obtain ⟨a2, e4⟩ := jls_ws_suf c r2
      have e3 := jls_readExpect_suf h2
      obtain ⟨a1, e2⟩ := jls_ws_suf c r1
      obtain ⟨W3, E3⟩ : ∃ W, ws c r3 = W ++ r := ⟨_, jls_mid e7⟩
      obtain ⟨R3', R3⟩ : ∃ R, r3 = R ++ r := ⟨a4 ++ W3, by rw [e6, E3, List.append_assoc]⟩
      obtain ⟨W2, E2⟩ : ∃ W, ws c r2 = W ++ r := ⟨a3 ++ R3', by rw [e5, R3, List.append_assoc]⟩
      obtain ⟨R2', R2⟩ : ∃ R, r2 = R ++ r := ⟨a2 ++ W2, by rw [e4, E2, List.append_assoc]⟩
      obtain ⟨W1, E1⟩ : ∃ W, ws c r1 = W ++ r := ⟨[58] ++ R2', by rw [e3, R2, List.append_assoc]⟩
      obtain ⟨R1', R1⟩ : ∃ R, r1 = R ++ r := ⟨a1 ++ W1, by rw [e2, E1, List.append_assoc]⟩
      have T1 : ws c R1' = W1 := jls_ws_trunc c _ r _ (by rw [← R1]; exact E1)
      have T2 : ws c R2' = W2 := jls_ws_trunc c _ r _ (by rw [← R2]; exact E2)
      have T3 : ws c R3' = W3 := jls_ws_trunc c _ r _ (by rw [← R3]; exact E3)
      refine jls_pm_mk (r2 := R2') (r3 := R3') (v := v) (jls_str_trunc c r (by rw [← R1]; exact h1)) ?_ ?_ ?_
      · rw [T1]; exact jls_readExpect_trunc (by rw [← E1, ← R2]; exact h2)
      · rw [T2]; exact ihv (by rw [← E2, ← R3]; exact h3)
      · rw [T3]; exact mt (by rw [← E3]; exact h4)
    · obtain ⟨v, r1, h1, h2⟩ := jls_pe_inv h
      obtain ⟨a2, -, e2⟩ := jls_et_suf h2
      obtain ⟨a1, e1⟩ := jls_ws_suf c r1
      obtain ⟨W1, E1⟩ : ∃ W, ws c r1 = W ++ r := ⟨_, jls_mid e2⟩
      obtain ⟨R1', R1⟩ : ∃ R, r1 = R ++ r := ⟨a1 ++ W1, by rw [e1, E1, List.append_assoc]⟩
      have T1 : ws c R1' = W1 := jls_ws_trunc c _ r _ (by rw [← R1]; exact E1)
      exact jls_pe_mk (ihv (by rw [← R1]; exact h1)) (by rw [T1]; exact et (by rw [← E1]; exact h2))

end C3.Json
