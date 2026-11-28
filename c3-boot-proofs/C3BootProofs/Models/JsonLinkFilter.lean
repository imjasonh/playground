import C3BootProofs.Models.JsonLinkPos

/-!
# The spec is the lax grammar without control bytes in keys

`Spec/Json.lean` reads object keys in strict mode, and the lax grammar of
`JsonLinkLax.lean` reads them in the document's mode. The spec gives
exactly the lax results with no control byte in a key (`jlf_filter`), so a
spec value has none (`jlf_jval`), and each link theorem for the spec
follows from the one for the lax grammar.
-/

namespace C3.Json

open C3

/-! ## The spec's equations -/

def jlfOT (c : Bool) (f dep : Nat) : Bytes → Option (Json × Bytes)
  | 125 :: r => some (.obj [], r)
  | r => (parseMembers c f (dep - 1) r).bind fun (ms, r) =>
      (require (keysOk c (ms.map (·.1)))).bind fun _ => some (.obj ms, r)

def jlfOTx (c : Bool) (f dep : Nat) : Bytes → Option (Json × Bytes)
  | 125 :: r => some (.obj [], r)
  | r => (jlxMembers c f (dep - 1) r).bind fun (ms, r) =>
      (require (keysOk c (ms.map (·.1)))).bind fun _ => some (.obj ms, r)

def jlfAT (c : Bool) (f dep : Nat) : Bytes → Option (Json × Bytes)
  | 93 :: r => some (.arr [], r)
  | r => (parseElems c f (dep - 1) r).bind fun (items, r) => some (.arr items, r)

def jlfATx (c : Bool) (f dep : Nat) : Bytes → Option (Json × Bytes)
  | 93 :: r => some (.arr [], r)
  | r => (jlxElems c f (dep - 1) r).bind fun (items, r) => some (.arr items, r)

def jlfMTail (c : Bool) (f dep : Nat) (k : Bytes) (v : Json) : Bytes → Option (List (Bytes × Json) × Bytes)
  | 44 :: r => (parseMembers c f dep (ws c r)).bind fun (more, r) => some ((k, v) :: more, r)
  | 125 :: r => some ([(k, v)], r)
  | _ => none

def jlfETail (c : Bool) (f dep : Nat) (v : Json) : Bytes → Option (List Json × Bytes)
  | 44 :: r => (parseElems c f dep (ws c r)).bind fun (more, r) => some (v :: more, r)
  | 93 :: r => some ([v], r)
  | _ => none

theorem jlf_pv_obj (c : Bool) (f dep : Nat) (rest : Bytes) :
    parseValue c (f + 1) dep (123 :: rest) = (require (decide (dep ≥ 1))).bind fun _ => jlfOT c f dep (ws c rest) := by
  unfold parseValue; rfl

theorem jlf_pvx_obj (c : Bool) (f dep : Nat) (rest : Bytes) :
    jlxValue c (f + 1) dep (123 :: rest) = (require (decide (dep ≥ 1))).bind fun _ => jlfOTx c f dep (ws c rest) := by
  unfold jlxValue; rfl

theorem jlf_pv_arr (c : Bool) (f dep : Nat) (rest : Bytes) :
    parseValue c (f + 1) dep (91 :: rest) = (require (decide (dep ≥ 1))).bind fun _ => jlfAT c f dep (ws c rest) := by
  unfold parseValue; rfl

theorem jlf_pvx_arr (c : Bool) (f dep : Nat) (rest : Bytes) :
    jlxValue c (f + 1) dep (91 :: rest) = (require (decide (dep ≥ 1))).bind fun _ => jlfATx c f dep (ws c rest) := by
  unfold jlxValue; rfl

theorem jlf_pv_rest (c : Bool) (f dep b : Nat) (tl : Bytes) (h1 : b ≠ 123) (h2 : b ≠ 91) :
    parseValue c (f + 1) dep (b :: tl) = jlxValue c (f + 1) dep (b :: tl) := by
  by_cases h3 : b = 34
  · subst h3; rw [jls_pv_str]; unfold parseValue; rfl
  rw [jls_pv_other c f dep b tl h1 h2 h3]
  unfold parseValue
  split
  · rename_i h; injection h with h; exact absurd h h1
  · rename_i h; injection h with h; exact absurd h h2
  · rename_i h; injection h with h; exact absurd h h3
  · rename_i h; injection h with hb ht; subst hb; subst ht; rfl
  · rename_i h; cases h

theorem jlf_pm_eq (c : Bool) (f dep : Nat) (rest : Bytes) :
    parseMembers c (f + 1) dep (34 :: rest) = (parseString false rest).bind fun (k, r) =>
      (readExpect [58] (ws c r)).bind fun r => (parseValue c f dep (ws c r)).bind fun (v, r) =>
        jlfMTail c f dep k v (ws c r) := by
  unfold parseMembers; rfl

theorem jlf_pm_other (c : Bool) (f dep b : Nat) (tl : Bytes) (h : b ≠ 34) :
    parseMembers c (f + 1) dep (b :: tl) = none := by
  unfold parseMembers
  split
  · rename_i h'; injection h' with h'; exact absurd h' h
  · rfl

theorem jlf_pe_eq (c : Bool) (f dep : Nat) (s : Bytes) :
    parseElems c (f + 1) dep s = (parseValue c f dep s).bind fun (v, r) => jlfETail c f dep v (ws c r) := by
  unfold parseElems; rfl

/-! ## Filters -/

theorem jlf_fl_some {α : Type} (p : α → Bool) (a : α) : (some a).filter p = if p a then some a else none := rfl

theorem jlf_fl_eq {α : Type} {p : α → Bool} {o : Option α} {a : α} :
    o.filter p = some a ↔ o = some a ∧ p a = true := by
  cases o with
  | none => exact ⟨fun h => (nomatch h), fun ⟨h, _⟩ => (nomatch h)⟩
  | some b =>
    rw [jlf_fl_some]
    cases hb : p b
    · refine ⟨fun h => (nomatch h), fun ⟨h, h'⟩ => ?_⟩
      injection h with h; subst h; rw [hb] at h'; cases h'
    · refine ⟨fun h => ?_, fun ⟨h, _⟩ => h⟩
      injection h with h; subst h; exact ⟨rfl, hb⟩

theorem jlf_fl_none {α : Type} {p : α → Bool} {o : Option α} (h : ∀ a, o = some a → p a = false) :
    o.filter p = none := by
  cases o with
  | none => rfl
  | some a => rw [jlf_fl_some, h a rfl]; rfl

theorem jlf_head (s : Bytes) (b : Nat) : (∃ r, s = b :: r) ∨ ∀ r, s ≠ b :: r := by
  cases s with
  | nil => exact .inr fun _ h => nomatch h
  | cons a r =>
    by_cases h : a = b
    · exact .inl ⟨r, by rw [h]⟩
    · exact .inr fun _ e => h (by injection e)

theorem jlf_ps_none {c : Bool} {l : Bytes} (h : parseString c l = none) : parseString false l = none := by
  cases hf : parseString false l with
  | none => rfl
  | some p =>
    have : parseString c l = some p := by
      cases c
      · exact hf
      · exact jlp_ps_true hf
    rw [h] at this; cases this

theorem jlf_ps_some {c : Bool} {l k r : Bytes} (h : parseString c l = some (k, r)) :
    parseString false l = if k.all (fun b => decide (32 ≤ b)) then some (k, r) else none := by
  cases c
  · have h2 := jlp_ps_false (jlp_ps_true h)
    by_cases hc : k.all (fun b => decide (32 ≤ b)) = true
    · rw [jlp_if_pos hc]; exact h
    · rw [jlp_if_neg hc, h] at h2; cases h2
  · exact jlp_ps_false h

theorem jlf_noCtl_obj (ms : List (Bytes × Json)) : noCtlKeys (.obj ms) = noCtlMembers ms := by
  simp only [noCtlKeys]

theorem jlf_noCtl_arr (js : List Json) : noCtlKeys (.arr js) = noCtlElems js := by
  simp only [noCtlKeys]

theorem jlf_noCtl_cons (k : Bytes) (v : Json) (ms : List (Bytes × Json)) :
    noCtlMembers ((k, v) :: ms) = (k.all (fun b => decide (0x20 ≤ b)) && noCtlKeys v && noCtlMembers ms) := by
  simp only [noCtlMembers]

theorem jlf_noCtlE_cons (v : Json) (js : List Json) :
    noCtlElems (v :: js) = (noCtlKeys v && noCtlElems js) := by
  simp only [noCtlElems]

theorem jlf_mt_head {c : Bool} {f dep : Nat} {k : Bytes} {v : Json} {s : Bytes} {p : List (Bytes × Json) × Bytes}
    (h : jlsMTail c f dep k v s = some p) : ∃ more, p.1 = (k, v) :: more := by
  obtain ⟨ms, r⟩ := p
  obtain ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ := jls_mt_inv h
  · exact ⟨_, rfl⟩
  · exact ⟨[], rfl⟩

theorem jlf_et_head {c : Bool} {f dep : Nat} {v : Json} {s : Bytes} {p : List Json × Bytes}
    (h : jlsETail c f dep v s = some p) : ∃ more, p.1 = v :: more := by
  obtain ⟨js, r⟩ := p
  obtain ⟨_, _, _, _, rfl⟩ | ⟨_, rfl⟩ := jls_et_inv h
  · exact ⟨_, rfl⟩
  · exact ⟨[], rfl⟩

theorem jlf_fl_self {α : Type} {p : α → Bool} {o : Option α} (h : ∀ a, o = some a → p a = true) :
    o.filter p = o := by
  cases o with
  | none => rfl
  | some a => rw [jlf_fl_some, h a rfl]; rfl

theorem jlf_noCtl_nil : noCtlMembers [] = true := by simp only [noCtlMembers]

theorem jlf_noCtlE_nil : noCtlElems [] = true := by simp only [noCtlElems]

theorem jlf_scal {c : Bool} {f dep b : Nat} {tl r : Bytes} {j : Json} (h1 : b ≠ 123) (h2 : b ≠ 91)
    (h : jlxValue c (f + 1) dep (b :: tl) = some (j, r)) : noCtlKeys j = true := by
  rcases jls_pv_inv h with ⟨_, hs, _⟩ | ⟨_, hs, _⟩ | ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, _, _, _, hn⟩ |
      ⟨_, _, _, _, _, _, _, hl⟩
  · injection hs with hs; exact absurd hs h1
  · injection hs with hs; exact absurd hs h2
  · simp only [noCtlKeys]
  · rw [jls_num_eq] at hn
    obtain ⟨_, _, hn⟩ := Option.bind_eq_some_iff.mp hn
    injection hn with hn; injection hn with hn; subst hn; simp only [noCtlKeys]
  · rcases jls_lit_inv hl with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> simp only [noCtlKeys]

/-- The fuel induction's claim at one fuel. -/
def jlfClaim (c : Bool) (f : Nat) : Prop :=
  (∀ dep s, parseValue c f dep s = (jlxValue c f dep s).filter (fun p => noCtlKeys p.1)) ∧
  (∀ dep s, parseMembers c f dep s = (jlxMembers c f dep s).filter (fun p => noCtlMembers p.1)) ∧
  (∀ dep s, parseElems c f dep s = (jlxElems c f dep s).filter (fun p => noCtlElems p.1))

theorem jlf_ot {c : Bool} {f dep : Nat}
    (ihm : ∀ dep s, parseMembers c f dep s = (jlxMembers c f dep s).filter (fun p => noCtlMembers p.1))
    (w : Bytes) : jlfOT c f dep w = (jlfOTx c f dep w).filter (fun p => noCtlKeys p.1) := by
  rcases jlf_head w 125 with ⟨r, rfl⟩ | h125
  · show some (Json.obj [], r) = (some (Json.obj [], r)).filter _
    rw [jlf_fl_some, jlf_noCtl_obj, jlf_noCtl_nil]; rfl
  have e1 : jlfOT c f dep w = (parseMembers c f (dep - 1) w).bind fun (ms, r) =>
      (require (keysOk c (ms.map (·.1)))).bind fun _ => some (.obj ms, r) := by
    exact jlfOT.eq_2 _ _ _ _ (fun r e => h125 r e)
  have e2 : jlfOTx c f dep w = (jlxMembers c f (dep - 1) w).bind fun (ms, r) =>
      (require (keysOk c (ms.map (·.1)))).bind fun _ => some (.obj ms, r) := by
    exact jlfOTx.eq_2 _ _ _ _ (fun r e => h125 r e)
  rw [e1, e2, ihm]
  cases jlxMembers c f (dep - 1) w with
  | none => rfl
  | some p =>
    obtain ⟨ms, r⟩ := p
    rw [jlf_fl_some]
    simp only [Option.bind_some]
    cases hn : noCtlMembers ms
    · change none = _
      cases keysOk c (ms.map (·.1))
      · rfl
      · change none = (some (Json.obj ms, r)).filter _
        rw [jlf_fl_some, jlf_noCtl_obj, hn]; rfl
    · change ((require (keysOk c (ms.map (·.1)))).bind fun _ => some (Json.obj ms, r)) = _
      cases keysOk c (ms.map (·.1))
      · rfl
      · change some (Json.obj ms, r) = (some (Json.obj ms, r)).filter _
        rw [jlf_fl_some, jlf_noCtl_obj, hn]; rfl

theorem jlf_at {c : Bool} {f dep : Nat}
    (ihe : ∀ dep s, parseElems c f dep s = (jlxElems c f dep s).filter (fun p => noCtlElems p.1))
    (w : Bytes) : jlfAT c f dep w = (jlfATx c f dep w).filter (fun p => noCtlKeys p.1) := by
  rcases jlf_head w 93 with ⟨r, rfl⟩ | h93
  · show some (Json.arr [], r) = (some (Json.arr [], r)).filter _
    rw [jlf_fl_some, jlf_noCtl_arr, jlf_noCtlE_nil]; rfl
  have e1 : jlfAT c f dep w = (parseElems c f (dep - 1) w).bind fun (items, r) => some (.arr items, r) := by
    exact jlfAT.eq_2 _ _ _ _ (fun r e => h93 r e)
  have e2 : jlfATx c f dep w = (jlxElems c f (dep - 1) w).bind fun (items, r) => some (.arr items, r) := by
    exact jlfATx.eq_2 _ _ _ _ (fun r e => h93 r e)
  rw [e1, e2, ihe]
  cases jlxElems c f (dep - 1) w with
  | none => rfl
  | some p =>
    obtain ⟨js, r⟩ := p
    rw [jlf_fl_some]
    cases hn : noCtlElems js
    all_goals first
      | rfl
      | (change _ = (some (Json.arr js, r)).filter _; rw [jlf_fl_some, jlf_noCtl_arr, hn]; rfl)

theorem jlf_mt {c : Bool} {f dep : Nat} {k : Bytes} {v : Json}
    (ihm : ∀ dep s, parseMembers c f dep s = (jlxMembers c f dep s).filter (fun p => noCtlMembers p.1))
    (hk : k.all (fun b => decide (32 ≤ b)) = true) (hv : noCtlKeys v = true) (w : Bytes) :
    jlfMTail c f dep k v w = (jlsMTail c f dep k v w).filter (fun p => noCtlMembers p.1) := by
  rcases jlf_head w 44 with ⟨r, rfl⟩ | h44
  · show (parseMembers c f dep (ws c r)).bind _ = ((jlxMembers c f dep (ws c r)).bind _).filter _
    rw [ihm]
    cases jlxMembers c f dep (ws c r) with
    | none => rfl
    | some p =>
      obtain ⟨more, r'⟩ := p
      rw [jlf_fl_some]
      cases hn : noCtlMembers more
      all_goals first
        | rfl
        | (change _ = (some ((k, v) :: more, r')).filter _; rw [jlf_fl_some, jlf_noCtl_cons, hk, hv, hn]; rfl)
  rcases jlf_head w 125 with ⟨r, rfl⟩ | h125
  · show some ([(k, v)], r) = (some ([(k, v)], r)).filter _
    rw [jlf_fl_some, jlf_noCtl_cons, hk, hv, jlf_noCtl_nil]; rfl
  rw [jlfMTail.eq_3 _ _ _ _ _ _ (fun r e => h44 r e) (fun r e => h125 r e),
    jlsMTail.eq_3 _ _ _ _ _ _ (fun r e => h44 r e) (fun r e => h125 r e)]
  rfl

theorem jlf_et {c : Bool} {f dep : Nat} {v : Json}
    (ihe : ∀ dep s, parseElems c f dep s = (jlxElems c f dep s).filter (fun p => noCtlElems p.1))
    (hv : noCtlKeys v = true) (w : Bytes) :
    jlfETail c f dep v w = (jlsETail c f dep v w).filter (fun p => noCtlElems p.1) := by
  rcases jlf_head w 44 with ⟨r, rfl⟩ | h44
  · show (parseElems c f dep (ws c r)).bind _ = ((jlxElems c f dep (ws c r)).bind _).filter _
    rw [ihe]
    cases jlxElems c f dep (ws c r) with
    | none => rfl
    | some p =>
      obtain ⟨more, r'⟩ := p
      rw [jlf_fl_some]
      cases hn : noCtlElems more
      all_goals first
        | rfl
        | (change _ = (some (v :: more, r')).filter _; rw [jlf_fl_some, jlf_noCtlE_cons, hv, hn]; rfl)
  rcases jlf_head w 93 with ⟨r, rfl⟩ | h93
  · show some ([v], r) = (some ([v], r)).filter _
    rw [jlf_fl_some, jlf_noCtlE_cons, hv, jlf_noCtlE_nil]; rfl
  rw [jlfETail.eq_3 _ _ _ _ _ (fun r e => h44 r e) (fun r e => h93 r e),
    jlsETail.eq_3 _ _ _ _ _ (fun r e => h44 r e) (fun r e => h93 r e)]
  rfl

theorem jlf_filter (c : Bool) : ∀ f, jlfClaim c f
  | 0 => ⟨fun dep s => by rw [jls_pv_zero]; unfold parseValue; rfl,
      fun dep s => by rw [jls_pm_zero]; unfold parseMembers; rfl,
      fun dep s => by rw [jls_pe_zero]; unfold parseElems; rfl⟩
  | f + 1 => by
    obtain ⟨ihv, ihm, ihe⟩ := jlf_filter c f
    refine ⟨fun dep s => ?_, fun dep s => ?_, fun dep s => ?_⟩
    · cases s with
      | nil => rw [jls_pv_nil]; unfold parseValue; rfl
      | cons b tl =>
        by_cases h1 : b = 123
        · subst h1; rw [jlf_pv_obj, jlf_pvx_obj]
          cases decide (dep ≥ 1)
          · rfl
          · exact jlf_ot ihm (ws c tl)
        by_cases h2 : b = 91
        · subst h2; rw [jlf_pv_arr, jlf_pvx_arr]
          cases decide (dep ≥ 1)
          · rfl
          · exact jlf_at ihe (ws c tl)
        rw [jlf_pv_rest c f dep b tl h1 h2]
        exact (jlf_fl_self fun ⟨j, r⟩ h => jlf_scal h1 h2 h).symm
    · cases s with
      | nil => rw [jls_pm_nil]; unfold parseMembers; rfl
      | cons b tl =>
        by_cases hb : b ≠ 34
        · rw [jlf_pm_other c f dep b tl hb, jls_pm_other c f dep b tl hb]; rfl
        have hb : b = 34 := Decidable.of_not_not hb
        subst hb
        rw [jlf_pm_eq, jls_pm_eq]
        cases hs : parseString c tl with
        | none => rw [jlf_ps_none hs]; rfl
        | some q =>
          obtain ⟨k, r1⟩ := q
          rw [jlf_ps_some hs]
          simp only [Option.bind_some]
          cases hk : k.all (fun b => decide (32 ≤ b))
          · refine (jlf_fl_none fun ⟨ms, r⟩ h => ?_).symm
            obtain ⟨r2, -, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨⟨v, r3⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨more, hm⟩ := jlf_mt_head h
            simp only at hm
            rw [hm, jlf_noCtl_cons, hk]; rfl
          · rw [jlp_if_pos rfl, Option.bind_some]
            cases readExpect [58] (ws c r1) with
            | none => rfl
            | some r2 =>
              simp only [Option.bind_some]
              rw [ihv]
              cases jlxValue c f dep (ws c r2) with
              | none => rfl
              | some q =>
                obtain ⟨v, r3⟩ := q
                rw [jlf_fl_some]
                simp only [Option.bind_some]
                cases hv : noCtlKeys v
                · refine (jlf_fl_none fun ⟨ms, r⟩ h => ?_).symm
                  obtain ⟨more, hm⟩ := jlf_mt_head h
                  simp only at hm
                  rw [hm, jlf_noCtl_cons, hk, hv]; rfl
                · exact jlf_mt ihm hk hv _
    · rw [jlf_pe_eq, jls_pe_eq, ihv]
      cases jlxValue c f dep s with
      | none => rfl
      | some q =>
        obtain ⟨v, r⟩ := q
        rw [jlf_fl_some]
        simp only [Option.bind_some]
        cases hv : noCtlKeys v
        · refine (jlf_fl_none fun ⟨js, r'⟩ h => ?_).symm
          obtain ⟨more, hm⟩ := jlf_et_head h
          simp only at hm
          rw [hm, jlf_noCtlE_cons, hv]; rfl
        · exact jlf_et ihe hv _

/-! ## Transfer -/

theorem jlf_val {c : Bool} {f dep : Nat} {s r : Bytes} {j : Json} :
    parseValue c f dep s = some (j, r) ↔ jlxValue c f dep s = some (j, r) ∧ noCtlKeys j = true := by
  rw [(jlf_filter c f).1, jlf_fl_eq]

/-- A spec value is a lax value with no control byte in a key. -/
theorem jlf_jval {c : Bool} {v : Bytes} {j : Json} : JVal c v j ↔ JValX c v j ∧ noCtlKeys j = true :=
  ⟨fun ⟨f, dep, h⟩ => let h' := jlf_val.mp h; ⟨⟨f, dep, h'.1⟩, h'.2⟩,
    fun ⟨⟨f, dep, h⟩, hn⟩ => ⟨f, dep, jlf_val.mpr ⟨h, hn⟩⟩⟩

theorem jlf_jden {c : Bool} {d : Bytes} {a l : Nat} {j : Json} :
    JDen c d a l j ↔ JDenX c d a l j ∧ noCtlKeys j = true :=
  ⟨fun ⟨hl, h⟩ => let h' := jlf_jval.mp h; ⟨⟨hl, h'.1⟩, h'.2⟩,
    fun ⟨⟨hl, h⟩, hn⟩ => ⟨hl, jlf_jval.mpr ⟨h, hn⟩⟩⟩

theorem jlf_json {c : Bool} {d : Bytes} {j : Json} :
    parseJson c d = some j ↔ jlxJson c d = some j ∧ noCtlKeys j = true := by
  unfold parseJson jlxJson
  rw [(jlf_filter c _).1]
  cases jlxValue c (2 * d.length + 2) 16 (ws c d) with
  | none => exact ⟨fun h => (nomatch h), fun ⟨h, _⟩ => (nomatch h)⟩
  | some q =>
    obtain ⟨v, r⟩ := q
    rw [jlf_fl_some]
    cases hn : noCtlKeys v
    · change none = some j ↔ ((require (ws c r).isEmpty).bind fun _ => some v) = some j ∧ noCtlKeys j = true
      refine ⟨fun h => (nomatch h), fun ⟨h, h'⟩ => ?_⟩
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      cases h; rw [hn] at h'; cases h'
    · change ((require (ws c r).isEmpty).bind fun _ => some v) = some j ↔
        ((require (ws c r).isEmpty).bind fun _ => some v) = some j ∧ noCtlKeys j = true
      refine ⟨fun h => ⟨h, ?_⟩, fun ⟨h, _⟩ => h⟩
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      cases h; exact hn

theorem jlf_mf {c : Bool} {v : Bytes} : ∀ {pos : Nat} {ms : List (Bytes × Json)},
    MembersFromX c v pos ms → noCtlMembers ms = true → MembersFrom c v pos ms
  | _, [], h, _ => h
  | _, (k, j) :: ms, ⟨kp, vp, vl, a, h1, h2, h3, h4⟩, hn => by
    rw [jlf_noCtl_cons, Bool.and_eq_true, Bool.and_eq_true] at hn
    exact ⟨kp, vp, vl, a, h1, h2, jlf_jden.mpr ⟨h3, hn.1.2⟩, jlf_mf h4 hn.2⟩

theorem jlf_ef {c : Bool} {v : Bytes} : ∀ {pos : Nat} {js : List Json},
    ElementsFromX c v pos js → noCtlElems js = true → ElementsFrom c v pos js
  | _, [], h, _ => h
  | _, j :: js, ⟨l, a, h1, h2, h3⟩, hn => by
    rw [jlf_noCtlE_cons, Bool.and_eq_true] at hn
    exact ⟨l, a, h1, jlf_jden.mpr ⟨h2, hn.1⟩, jlf_ef h3 hn.2⟩

theorem jlf_lookup {key : Bytes} {j' : Json} : ∀ {ms : List (Bytes × Json)},
    noCtlMembers ms = true → ms.lookup key = some j' → noCtlKeys j' = true
  | [], _, h => nomatch h
  | (k, j) :: ms, hn, h => by
    rw [jlf_noCtl_cons, Bool.and_eq_true, Bool.and_eq_true] at hn
    unfold List.lookup at h
    cases hk : key == k
    · rw [hk] at h; exact jlf_lookup hn.2 h
    · rw [hk] at h; injection h with h; subst h; exact hn.1.2

theorem jlf_asObj {j : Json} {ms : List (Bytes × Json)} (h : j.asObj = some ms) (hn : noCtlKeys j = true) :
    noCtlMembers ms = true := by
  cases j <;> first | (injection h with h; subst h; rw [← jlf_noCtl_obj]; exact hn) | cases h

end C3.Json
