import C3BootProofs.Models.JsonLinkKeys

/-!
# Steps of `parseLoop` and `closeLoop`

One pass of `parseLoop` reads the value at `pos` the way `parseValue` reads
its first byte, and `closeLoop` on a pushed container reads what follows a
member or an item the way `parseMembers` and `parseElems` do.
-/

namespace C3.Json

open C3

set_option linter.unusedSimpArgs false

/-- `R` is an error. -/
def jlmErr {α : Type} (R : Except Nat α) : Prop := ∃ e, R = .error e

/-- The parse from the key at `p`: `key_end`, then the value pass. -/
def jlmPK (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) (p : Nat) : Except Nat (Nat × Nat) :=
  match keyEnd c d p with
  | none => .error 0x20
  | some v => parseLoop c d start k stk v

theorem jlm_cl_norm (c : Bool) (d : Bytes) (start : Nat) : ∀ (j j' : Nat) (stk : List (Bool × Nat)) (pos : Nat),
    stk.length < j → stk.length < j' → closeLoop c d start j stk pos = closeLoop c d start j' stk pos
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | j + 1, j' + 1, stk, pos, h, h' => by
    rw [closeLoop.eq_2, closeLoop.eq_2]
    cases hl : stk.getLast? with
    | none => rfl
    | some x =>
      obtain ⟨ob, st⟩ := x
      have hne : stk ≠ [] := fun e => by rw [e] at hl; cases hl
      have hlen : stk.dropLast.length + 1 = stk.length := by
        rw [List.length_dropLast]
        have : 0 < stk.length := List.length_pos_iff.mpr hne
        omega
      dsimp only
      rw [jlm_cl_norm c d start j j' stk.dropLast (wsIn c d pos + 1) (by omega) (by omega)]

theorem jlm_cl_push (c : Bool) (d : Bytes) (start : Nat) {stk : List (Bool × Nat)} (ob : Bool) (st p : Nat)
    (hs : stk.length < 16) :
    closeLoop c d start 17 (stk ++ [(ob, st)]) p =
      if d.length ≤ wsIn c d p then .error 0x20
      else if d.getD (wsIn c d p) 0 = 93 then
        if ob then .error 0x20 else closeLoop c d start 17 stk (wsIn c d p + 1)
      else if d.getD (wsIn c d p) 0 = 125 then
        if ob then
          if wsIn c d p + 1 < st then .error 0x20
          else match checkKeys c (slice d st (wsIn c d p + 1 - st)) with
            | .error e => .error e
            | .ok () => closeLoop c d start 17 stk (wsIn c d p + 1)
        else .error 0x20
      else if d.getD (wsIn c d p) 0 = 44 then
        if ob then
          match keyEnd c d (wsIn c d (wsIn c d p + 1)) with
          | none => .error 0x20
          | some v => .ok (.cont (stk ++ [(ob, st)]) v)
        else .ok (.cont (stk ++ [(ob, st)]) (wsIn c d (wsIn c d p + 1)))
      else .error 0x20 := by
  rw [closeLoop.eq_2, List.getLast?_concat, List.dropLast_concat]
  dsimp only
  rw [jlm_cl_norm c d start 16 17 stk _ hs (by omega)]
  rfl

theorem jlm_ac_keys {r : Except Nat Unit} {X : Except Nat PStep} {N : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)} :
    afterClose (match r with | .error e => .error e | .ok () => X) N = keysThen r (afterClose X N) := by
  cases r <;> rfl

theorem jlm_ac_pk {c : Bool} {d : Bytes} {start k : Nat} {stk : List (Bool × Nat)} {p : Nat} :
    afterClose (match keyEnd c d p with | none => .error 0x20 | some v => .ok (.cont stk v)) (parseLoop c d start k) =
      jlmPK c d start k stk p := by
  unfold jlmPK; cases keyEnd c d p <;> rfl

/-- What follows a member, at `ws c (d.drop e)`. -/
theorem jlm_cl_obj (c : Bool) (d : Bytes) (start k : Nat) {stk : List (Bool × Nat)} {st e : Nat} {t : Bytes}
    (hs : stk.length < 16) (ht : ws c (d.drop e) = t) (hst : st ≤ e) :
    (∀ s', t = 44 :: s' → afterClose (closeLoop c d start 17 (stk ++ [(true, st)]) e) (parseLoop c d start k) =
        jlmPK c d start k (stk ++ [(true, st)]) (jlpEnd d (ws c s')) ∧ d.drop (jlpEnd d (ws c s')) = ws c s' ∧
        e < jlpEnd d (ws c s')) ∧
    (∀ r, t = 125 :: r → afterClose (closeLoop c d start 17 (stk ++ [(true, st)]) e) (parseLoop c d start k) =
        keysThen (checkKeys c (slice d st (jlpEnd d r - st))) (afterClose (closeLoop c d start 17 stk (jlpEnd d r))
          (parseLoop c d start k)) ∧ d.drop (jlpEnd d r) = r ∧ e < jlpEnd d r) ∧
    ((∀ s', t ≠ 44 :: s') → (∀ r, t ≠ 125 :: r) →
        jlmErr (afterClose (closeLoop c d start 17 (stk ++ [(true, st)]) e) (parseLoop c d start k))) := by
  rw [jlp_ws_drop] at ht
  have hq := jlp_wsIn_ge c d e
  rw [jlm_cl_push c d start true st e hs]
  refine ⟨fun s' h => ?_, fun r h => ?_, fun h1 h2 => ?_⟩
  · rw [← ht] at h
    obtain ⟨hL, hb, hs'⟩ := jlp_drop_cons_inv h
    have hd' : d.drop (wsIn c d (wsIn c d e + 1)) = ws c s' := by rw [hs', jlp_ws_drop]
    have hle : wsIn c d (wsIn c d e + 1) ≤ d.length := jlp_wsIn_le (by omega)
    have hge := jlp_wsIn_ge c d (wsIn c d e + 1)
    rw [← hd', jlp_end_drop d hle]
    refine ⟨?_, rfl, by omega⟩
    rw [jlp_if_neg (by omega), jlp_if_neg (by rw [hb]; decide), jlp_if_neg (by rw [hb]; decide), jlp_if_pos hb,
      jlp_if_pos rfl]
    exact jlm_ac_pk
  · rw [← ht] at h
    obtain ⟨hL, hb, hr⟩ := jlp_drop_cons_inv h
    have hre : jlpEnd d r = wsIn c d e + 1 := by rw [hr, jlp_end_drop d (by omega)]
    rw [hre]
    refine ⟨?_, by rw [hr], by omega⟩
    rw [jlp_if_neg (by omega), jlp_if_neg (by rw [hb]; decide), jlp_if_pos hb, jlp_if_pos rfl,
      jlp_if_neg (by omega)]
    exact jlm_ac_keys
  · by_cases hL : d.length ≤ wsIn c d e
    · rw [jlp_if_pos hL]; exact ⟨_, rfl⟩
    rw [jlp_if_neg hL]
    have hd := jlp_drop_cons (d := d) (i := wsIn c d e) (by omega)
    rw [ht] at hd
    by_cases h93 : d.getD (wsIn c d e) 0 = 93
    · rw [jlp_if_pos h93, jlp_if_pos rfl]; exact ⟨_, rfl⟩
    rw [jlp_if_neg h93]
    by_cases h125 : d.getD (wsIn c d e) 0 = 125
    · rw [h125] at hd; exact absurd hd (h2 _)
    rw [jlp_if_neg h125]
    by_cases h44 : d.getD (wsIn c d e) 0 = 44
    · rw [h44] at hd; exact absurd hd (h1 _)
    rw [jlp_if_neg h44]; exact ⟨_, rfl⟩

/-- What follows an item, at `ws c (d.drop e)`. -/
theorem jlm_cl_arr (c : Bool) (d : Bytes) (start k : Nat) {stk : List (Bool × Nat)} {st e : Nat} {t : Bytes}
    (hs : stk.length < 16) (ht : ws c (d.drop e) = t) :
    (∀ s', t = 44 :: s' → afterClose (closeLoop c d start 17 (stk ++ [(false, st)]) e) (parseLoop c d start k) =
        parseLoop c d start k (stk ++ [(false, st)]) (jlpEnd d (ws c s')) ∧ d.drop (jlpEnd d (ws c s')) = ws c s' ∧
        e < jlpEnd d (ws c s')) ∧
    (∀ r, t = 93 :: r → afterClose (closeLoop c d start 17 (stk ++ [(false, st)]) e) (parseLoop c d start k) =
        afterClose (closeLoop c d start 17 stk (jlpEnd d r)) (parseLoop c d start k) ∧ d.drop (jlpEnd d r) = r ∧
        e < jlpEnd d r) ∧
    ((∀ s', t ≠ 44 :: s') → (∀ r, t ≠ 93 :: r) →
        jlmErr (afterClose (closeLoop c d start 17 (stk ++ [(false, st)]) e) (parseLoop c d start k))) := by
  rw [jlp_ws_drop] at ht
  have hq := jlp_wsIn_ge c d e
  rw [jlm_cl_push c d start false st e hs]
  refine ⟨fun s' h => ?_, fun r h => ?_, fun h1 h2 => ?_⟩
  · rw [← ht] at h
    obtain ⟨hL, hb, hs'⟩ := jlp_drop_cons_inv h
    have hd' : d.drop (wsIn c d (wsIn c d e + 1)) = ws c s' := by rw [hs', jlp_ws_drop]
    have hle : wsIn c d (wsIn c d e + 1) ≤ d.length := jlp_wsIn_le (by omega)
    have hge := jlp_wsIn_ge c d (wsIn c d e + 1)
    rw [← hd', jlp_end_drop d hle]
    refine ⟨?_, rfl, by omega⟩
    rw [jlp_if_neg (by omega), jlp_if_neg (by rw [hb]; decide), jlp_if_neg (by rw [hb]; decide), jlp_if_pos hb,
      jlp_if_neg Bool.false_ne_true]
    rfl
  · rw [← ht] at h
    obtain ⟨hL, hb, hr⟩ := jlp_drop_cons_inv h
    have hre : jlpEnd d r = wsIn c d e + 1 := by rw [hr, jlp_end_drop d (by omega)]
    rw [hre]
    refine ⟨?_, by rw [hr], by omega⟩
    rw [jlp_if_neg (by omega), jlp_if_pos hb, jlp_if_neg Bool.false_ne_true]
  · by_cases hL : d.length ≤ wsIn c d e
    · rw [jlp_if_pos hL]; exact ⟨_, rfl⟩
    rw [jlp_if_neg hL]
    have hd := jlp_drop_cons (d := d) (i := wsIn c d e) (by omega)
    rw [ht] at hd
    by_cases h93 : d.getD (wsIn c d e) 0 = 93
    · rw [h93] at hd; exact absurd hd (h2 _)
    rw [jlp_if_neg h93]
    by_cases h125 : d.getD (wsIn c d e) 0 = 125
    · rw [jlp_if_pos h125, jlp_if_neg Bool.false_ne_true]; exact ⟨_, rfl⟩
    rw [jlp_if_neg h125]
    by_cases h44 : d.getD (wsIn c d e) 0 = 44
    · rw [h44] at hd; exact absurd hd (h1 _)
    rw [jlp_if_neg h44]; exact ⟨_, rfl⟩

/-! ## One value pass -/

theorem jlm_pl_ge (c : Bool) (d : Bytes) (start : Nat) {pos : Nat} (stk : List (Bool × Nat)) (h : d.length ≤ pos) :
    ∀ k, jlmErr (parseLoop c d start k stk pos)
  | 0 => ⟨_, rfl⟩
  | k + 1 => by rw [parseLoop.eq_2, jlp_if_pos h]; exact ⟨_, rfl⟩

/-- The pass after a scalar that ends at `E`. -/
def jlmScal (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) (E : Option Nat) :
    Except Nat (Nat × Nat) :=
  match E with
  | none => .error 0x20
  | some e => afterClose (closeLoop c d start 17 stk e) (parseLoop c d start k)

theorem jlm_pl_str (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) {pos : Nat} {tl : Bytes}
    (hs : d.drop pos = 34 :: tl) :
    parseLoop c d start (k + 1) stk pos = jlmScal c d start k stk ((parseString c tl).map fun p => jlpEnd d p.2) := by
  obtain ⟨hL, hb, htl⟩ := jlp_drop_cons_inv hs
  rw [parseLoop.eq_2, jlp_if_neg (by omega), jlp_if_pos hb, jlp_stringEnd hL, ← htl]
  rfl

theorem jlm_pl_lit (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) {pos b : Nat} {tl : Bytes}
    (hs : d.drop pos = b :: tl) (hb : b = 102 ∨ b = 110 ∨ b = 116) :
    parseLoop c d start (k + 1) stk pos =
      jlmScal c d start k stk ((parseLiteral (b :: tl)).map fun p => jlpEnd d p.2) := by
  obtain ⟨hL, hb', -⟩ := jlp_drop_cons_inv hs
  rw [parseLoop.eq_2, jlp_if_neg (by omega), hb', jlp_if_neg (by rcases hb with rfl | rfl | rfl <;> decide),
    jlp_if_neg (by rcases hb with rfl | rfl | rfl <;> decide), jlp_if_pos hb, jlp_literalEnd (by omega), hs]
  rfl

theorem jlm_pl_num (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) {pos b : Nat} {tl : Bytes}
    (hs : d.drop pos = b :: tl) (hb : isDigit b = true) :
    parseLoop c d start (k + 1) stk pos =
      jlmScal c d start k stk ((parseNumber (b :: tl)).map fun p => jlpEnd d p.2) := by
  obtain ⟨hL, hb', -⟩ := jlp_drop_cons_inv hs
  have h := jlw_digit hb
  rw [parseLoop.eq_2, jlp_if_neg (by omega), hb', jlp_if_neg (by omega),
    jlp_if_neg (fun h' => by rcases h' with h' | h' <;> omega),
    jlp_if_neg (fun h' => by rcases h' with h' | h' | h' <;> omega), jlp_if_pos hb, jlp_numberEnd (by omega), hs]
  rfl

theorem jlm_pl_bad (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) {pos b : Nat} {tl : Bytes}
    (hs : d.drop pos = b :: tl) (h1 : b ≠ 34) (h2 : b ≠ 91) (h3 : b ≠ 123) (h4 : ¬(b = 102 ∨ b = 110 ∨ b = 116))
    (h5 : isDigit b = false) : jlmErr (parseLoop c d start (k + 1) stk pos) := by
  obtain ⟨hL, hb', -⟩ := jlp_drop_cons_inv hs
  rw [parseLoop.eq_2, jlp_if_neg (by omega), hb', jlp_if_neg h1,
    jlp_if_neg (fun h' => by rcases h' with h' | h' <;> contradiction), jlp_if_neg h4,
    jlp_if_neg (by rw [h5]; exact Bool.false_ne_true)]
  exact ⟨_, rfl⟩

theorem jlm_pl_deep (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) {pos b : Nat} {tl : Bytes}
    (hs : d.drop pos = b :: tl) (hb : b = 91 ∨ b = 123) (hd : 16 ≤ stk.length) :
    jlmErr (parseLoop c d start (k + 1) stk pos) := by
  obtain ⟨hL, hb', -⟩ := jlp_drop_cons_inv hs
  rw [parseLoop.eq_2, jlp_if_neg (by omega), hb', jlp_if_neg (by rcases hb with rfl | rfl <;> decide),
    jlp_if_pos hb, jlp_if_pos hd]
  exact ⟨_, rfl⟩

theorem jlm_pl_obj (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) {pos : Nat} {tl : Bytes}
    (hs : d.drop pos = 123 :: tl) (hd : stk.length < 16) :
    d.drop (wsIn c d (pos + 1)) = ws c tl ∧ pos < wsIn c d (pos + 1) ∧ wsIn c d (pos + 1) ≤ d.length ∧
    (∀ r, ws c tl = 125 :: r → parseLoop c d start (k + 1) stk pos =
      afterClose (closeLoop c d start 17 (stk ++ [(true, pos)]) (wsIn c d (pos + 1))) (parseLoop c d start k)) ∧
    ((∀ r, ws c tl ≠ 125 :: r) → parseLoop c d start (k + 1) stk pos =
      jlmPK c d start k (stk ++ [(true, pos)]) (wsIn c d (pos + 1))) := by
  obtain ⟨hL, hb', htl⟩ := jlp_drop_cons_inv hs
  have hw : d.drop (wsIn c d (pos + 1)) = ws c tl := by rw [htl, jlp_ws_drop]
  have hge := jlp_wsIn_ge c d (pos + 1)
  have hle : wsIn c d (pos + 1) ≤ d.length := jlp_wsIn_le (by omega)
  have base : parseLoop c d start (k + 1) stk pos =
      if wsIn c d (pos + 1) < d.length ∧ d.getD (wsIn c d (pos + 1)) 0 = 125 then
        afterClose (closeLoop c d start 17 (stk ++ [(true, pos)]) (wsIn c d (pos + 1))) (parseLoop c d start k)
      else jlmPK c d start k (stk ++ [(true, pos)]) (wsIn c d (pos + 1)) := by
    rw [parseLoop.eq_2, jlp_if_neg (by omega), hb', jlp_if_neg (by decide), jlp_if_pos (.inr rfl),
      jlp_if_neg (by omega), jlp_if_neg (by decide)]
    rfl
  refine ⟨hw, by omega, hle, fun r h => ?_, fun h => ?_⟩
  · rw [← hw] at h
    obtain ⟨hL', hb2, -⟩ := jlp_drop_cons_inv h
    rw [base, jlp_if_pos ⟨hL', hb2⟩]
  · rw [base, jlp_if_neg]
    intro ⟨hL', hb2⟩
    have := jlp_drop_cons hL'
    rw [hb2, hw] at this
    exact h _ this

theorem jlm_pl_arr (c : Bool) (d : Bytes) (start k : Nat) (stk : List (Bool × Nat)) {pos : Nat} {tl : Bytes}
    (hs : d.drop pos = 91 :: tl) (hd : stk.length < 16) :
    d.drop (wsIn c d (pos + 1)) = ws c tl ∧ pos < wsIn c d (pos + 1) ∧ wsIn c d (pos + 1) ≤ d.length ∧
    (∀ r, ws c tl = 93 :: r → parseLoop c d start (k + 1) stk pos =
      afterClose (closeLoop c d start 17 (stk ++ [(false, pos)]) (wsIn c d (pos + 1))) (parseLoop c d start k)) ∧
    ((∀ r, ws c tl ≠ 93 :: r) → parseLoop c d start (k + 1) stk pos =
      parseLoop c d start k (stk ++ [(false, pos)]) (wsIn c d (pos + 1))) := by
  obtain ⟨hL, hb', htl⟩ := jlp_drop_cons_inv hs
  have hw : d.drop (wsIn c d (pos + 1)) = ws c tl := by rw [htl, jlp_ws_drop]
  have hge := jlp_wsIn_ge c d (pos + 1)
  have hle : wsIn c d (pos + 1) ≤ d.length := jlp_wsIn_le (by omega)
  have base : parseLoop c d start (k + 1) stk pos =
      if wsIn c d (pos + 1) < d.length ∧ d.getD (wsIn c d (pos + 1)) 0 = 93 then
        afterClose (closeLoop c d start 17 (stk ++ [(false, pos)]) (wsIn c d (pos + 1))) (parseLoop c d start k)
      else parseLoop c d start k (stk ++ [(false, pos)]) (wsIn c d (pos + 1)) := by
    rw [parseLoop.eq_2, jlp_if_neg (by omega), hb', jlp_if_neg (by decide), jlp_if_pos (.inl rfl),
      jlp_if_neg (by omega), jlp_if_pos rfl]
  refine ⟨hw, by omega, hle, fun r h => ?_, fun h => ?_⟩
  · rw [← hw] at h
    obtain ⟨hL', hb2, -⟩ := jlp_drop_cons_inv h
    rw [base, jlp_if_pos ⟨hL', hb2⟩]
  · rw [base, jlp_if_neg]
    intro ⟨hL', hb2⟩
    have := jlp_drop_cons hL'
    rw [hb2, hw] at this
    exact h _ this

end C3.Json
