import C3BootProofs.Models.JsonLinkItems
import C3BootProofs.Models.JsonLinkValue

/-!
# `parse` and `parseJson`

The value step of the fuel induction, the three statements about `parse`
for the lax grammar, and the same statements for the spec.
-/

namespace C3.Json

open C3.RV32

/-- The claim of `jlmV` at one value position. -/
abbrev jlmVAt (c : Bool) (d : Bytes) (start f dep pos : Nat) (stk : List (Bool × Nat)) : Prop :=
  (∀ {j : Json} {r : Bytes}, jlxValue c f dep (d.drop pos) = some (j, r) →
    (noCtlKeys j = true → ∃ n, n ≤ jlpEnd d r - pos ∧
      (∀ k, parseLoop c d start (k + n) stk pos =
        afterClose (closeLoop c d start 17 stk (jlpEnd d r)) (parseLoop c d start k)) ∧
      ∀ k, k < n → jlmErr (parseLoop c d start k stk pos)) ∧
    (noCtlKeys j = false → ∀ k, jlmErr (parseLoop c d start k stk pos))) ∧
  (jlxValue c f dep (d.drop pos) = none → 2 * (d.length - pos) + 2 ≤ f →
    ∀ k, jlmErr (parseLoop c d start k stk pos))

theorem jlm_err0 (c : Bool) (d : Bytes) (start : Nat) (stk : List (Bool × Nat)) (pos : Nat) :
    jlmErr (parseLoop c d start 0 stk pos) := ⟨_, rfl⟩

theorem jlm_all_err {c : Bool} {d : Bytes} {start pos : Nat} {stk : List (Bool × Nat)}
    (h : ∀ k, jlmErr (parseLoop c d start (k + 1) stk pos)) : ∀ k, jlmErr (parseLoop c d start k stk pos) :=
  jlm_split 1 (fun k hk => by rw [show k = 0 by omega]; exact jlm_err0 c d start stk pos) h

theorem jlm_slice {d tl y r : Bytes} {pos b : Nat} (hs : d.drop pos = b :: tl) (ht : tl = y ++ r) :
    slice d pos (jlpEnd d r - pos) = b :: y := by
  have hl := congrArg List.length hs
  rw [ht, List.length_drop, List.length_cons, List.length_append] at hl
  show (d.drop pos).take (jlpEnd d r - pos) = b :: y
  rw [hs, ht, ← List.cons_append, show jlpEnd d r - pos = (b :: y).length by
    rw [List.length_cons]; unfold jlpEnd; omega]
  exact List.take_left' rfl

theorem jlm_head_dec (s : Bytes) (b : Nat) : (∃ r, s = b :: r) ∨ ∀ r, s ≠ b :: r := by
  cases s with
  | nil => exact .inr fun r h => by cases h
  | cons a r =>
    by_cases ha : a = b
    · exact .inl ⟨r, by rw [ha]⟩
    · exact .inr fun r' h => ha (List.cons.inj h).1

theorem jlm_V_scal {c : Bool} {d : Bytes} {start f dep pos : Nat} {stk : List (Bool × Nat)}
    {E : Option (Json × Bytes)} (hpos : pos ≤ d.length) (hpv : jlxValue c f dep (d.drop pos) = E)
    (hPL : ∀ k, parseLoop c d start (k + 1) stk pos = jlmScal c d start k stk (E.map fun p => jlpEnd d p.2))
    (hnc : ∀ j r, E = some (j, r) → noCtlKeys j = true) : jlmVAt c d start f dep pos stk := by
  unfold jlmVAt
  rw [hpv]
  cases E with
  | none =>
    exact ⟨fun h => (by cases h), fun _ _ => jlm_all_err fun k => by rw [hPL]; exact ⟨_, rfl⟩⟩
  | some jr =>
    obtain ⟨j0, r0⟩ := jr
    have hn := hnc _ _ rfl
    obtain ⟨-, hlt, -, -⟩ := jlw_den hpos hpv
    refine ⟨fun h => ?_, fun h => (by cases h)⟩
    cases h
    refine ⟨fun _ => ⟨1, by omega, fun k => by rw [hPL]; rfl, fun k hk => ?_⟩, fun h => ?_⟩
    · rw [show k = 0 by omega]; exact jlm_err0 c d start stk pos
    · rw [hn] at h; cases h

theorem jlm_V_bad {c : Bool} {d : Bytes} {start f dep pos : Nat} {stk : List (Bool × Nat)}
    (hpv : jlxValue c f dep (d.drop pos) = none) (hPL : ∀ k, jlmErr (parseLoop c d start (k + 1) stk pos)) :
    jlmVAt c d start f dep pos stk := by
  unfold jlmVAt
  rw [hpv]
  exact ⟨fun h => (by cases h), fun _ _ => jlm_all_err hPL⟩

theorem jlm_V_obj {c : Bool} {d : Bytes} {start f dep pos : Nat} {stk : List (Bool × Nat)} {tl : Bytes}
    (hM : jlmM c d start f) (hdep : stk.length + dep = 16) (hs : d.drop pos = 123 :: tl) :
    jlmVAt c d start (f + 1) dep pos stk := by
  by_cases hd16 : 16 ≤ stk.length
  · have hdz : ¬1 ≤ dep := by omega
    have hnone : jlxValue c (f + 1) dep (d.drop pos) = none := by
      have hr : require (decide (dep ≥ 1)) = none := by unfold require; rw [decide_eq_false hdz]; rfl
      rw [hs, jls_pv_obj, hr]; rfl
    exact jlm_V_bad hnone fun k => jlm_pl_deep c d start k stk hs (.inr rfl) hd16
  have hd1 : 1 ≤ dep := by omega
  have hs16 : stk.length < 16 := by omega
  obtain ⟨hw, hqgt, hqL, -, -⟩ := jlm_pl_obj c d start 0 stk hs hs16
  have hr1 : require (decide (dep ≥ 1)) = some () := by rw [require_eq_some]; exact decide_eq_true hd1
  obtain ⟨x, hx⟩ := jls_ws_suf c tl
  unfold jlmVAt
  rw [hs]
  rcases jlm_head_dec (ws c tl) 125 with ⟨r, hwr⟩ | hnot
  · rw [jls_pv_obj_empty_mk (f := f) hd1 hwr]
    refine ⟨fun h => ?_, fun h => (by cases h)⟩
    cases h
    have hty : tl = (x ++ [125]) ++ r := by rw [hx, hwr]; simp only [List.append_assoc, List.singleton_append]
    have hwy : ws c (x ++ [125]) = [125] := jls_ws_trunc c _ r _ (by rw [← hty, hwr]; rfl)
    have hck : checkKeys c (slice d pos (jlpEnd d r - pos)) = .ok () := by
      rw [jlm_slice hs hty]
      exact (jlk_check (f := 0) (dep := 0) (ms := []) (.inl ⟨rfl, hwy⟩)).1 (by cases c <;> rfl)
    have hCL := fun k => (jlm_cl_obj c d start k (stk := stk) (st := pos) (e := wsIn c d (pos + 1)) (t := ws c tl)
      hs16 (by rw [jlp_ws_drop, jlp_wsIn_idem, hw]) (by omega)).2.1 r hwr
    have hlt := (hCL 0).2.2
    refine ⟨fun _ => ⟨1, by omega, fun k => ?_, fun k hk => ?_⟩, fun h => (by cases h)⟩
    · rw [(jlm_pl_obj c d start k stk hs hs16).2.2.2.1 r hwr, (hCL k).1, hck]; rfl
    · rw [show k = 0 by omega]; exact jlm_err0 c d start stk pos
  have hPK : ∀ k, parseLoop c d start (k + 1) stk pos =
      jlmPK c d start k (stk ++ [(true, pos)]) (wsIn c d (pos + 1)) :=
    fun k => (jlm_pl_obj c d start k stk hs hs16).2.2.2.2 hnot
  have IH := hM (dep := dep - 1) (p := wsIn c d (pos + 1)) (st := pos) stk hqL (by omega) (by omega)
  rw [hw] at IH
  have hpvE : jlxValue c (f + 1) dep (123 :: tl) = (jlxMembers c f (dep - 1) (ws c tl)).bind
      fun (ms, r) => (require (keysOk c (ms.map (·.1)))).bind fun _ => some (.obj ms, r) := by
    rw [jls_pv_obj, hr1, Option.bind_some]
    revert hnot; generalize ws c tl = w; intro hnot
    split
    · exact absurd rfl (hnot _)
    · rfl
  cases hm : jlxMembers c f (dep - 1) (ws c tl) with
  | none =>
    rw [hpvE, hm]
    exact ⟨fun h => (by cases h), fun _ hf => jlm_all_err fun k => by rw [hPK]; exact IH.2 hm (by omega) k⟩
  | some mr =>
    obtain ⟨ms, r⟩ := mr
    obtain ⟨z, -, hz⟩ := jls_pm_suf hm
    have hty : tl = (x ++ z) ++ r := by rw [hx, hz, List.append_assoc]
    have hwy : ws c (x ++ z) = z := jls_ws_trunc c _ r _ (by rw [← hty, hz])
    have hmz : jlxMembers c f (dep - 1) (ws c (x ++ z)) = some (ms, []) := by
      rw [hwy]; exact (jls_trunc c r f).2.1 (t := []) (by rw [← hz]; exact hm)
    have CK := jlk_check (.inr hmz)
    rw [← jlm_slice hs hty] at CK
    obtain ⟨hIa, hIb⟩ := IH.1 hm
    have hrest : ∀ k, (∃ e, checkKeys c (slice d pos (jlpEnd d r - pos)) = .error e) →
        jlmErr (parseLoop c d start k stk pos) := fun k hck => jlm_all_err (fun k => by
      rw [hPK]
      cases hv : jlmVals ms
      · exact hIb hv k
      · obtain ⟨n', -, hEq', hlo'⟩ := hIa hv
        exact jlm_split n' hlo' (fun k => by
          rw [hEq']; obtain ⟨e, he⟩ := hck; rw [he]; exact ⟨e, rfl⟩) k) k
    cases hko : keysOk c (ms.map (·.1)) with
    | false =>
      have hnone : jlxValue c (f + 1) dep (123 :: tl) = none := by
        rw [hpvE, hm]
        show (require (keysOk c (ms.map (·.1)))).bind _ = none
        rw [hko]; rfl
      rw [hnone]
      exact ⟨fun h => (by cases h), fun _ _ k => hrest k (CK.2 (by rw [hko, Bool.and_false]))⟩
    | true =>
      rw [jls_pv_obj_mk hd1 hnot hm hko]
      refine ⟨fun h => ?_, fun h => (by cases h)⟩
      cases h
      obtain ⟨hltE, -, -⟩ := jlm_pm_end hqL (by rw [hw]; exact hm)
      have hnc : noCtlKeys (.obj ms) = (jlwKeysNC ms && jlmVals ms) := by
        rw [← jlm_noCtlMembers]; simp only [noCtlKeys]
      rw [hnc]
      refine ⟨fun h1 => ?_, fun h1 k => ?_⟩
      · rw [Bool.and_eq_true] at h1
        obtain ⟨n', hn', hEq', hlo'⟩ := hIa h1.2
        have hck : checkKeys c (slice d pos (jlpEnd d r - pos)) = .ok () := CK.1 (by rw [h1.1, hko]; rfl)
        refine ⟨n' + 1, by omega, fun k => ?_, fun k hk => ?_⟩
        · rw [show k + (n' + 1) = (k + n') + 1 by omega, hPK, hEq', hck]; rfl
        · cases k with
          | zero => exact jlm_err0 c d start stk pos
          | succ k => rw [hPK]; exact hlo' k (by omega)
      · cases hv : jlmVals ms
        · exact jlm_all_err (fun k => by rw [hPK]; exact hIb hv k) k
        · have hkn : jlwKeysNC ms = false := by rw [hv, Bool.and_true] at h1; exact h1
          exact hrest k (CK.2 (by rw [hkn, Bool.false_and]))

theorem jlm_V_arr {c : Bool} {d : Bytes} {start f dep pos : Nat} {stk : List (Bool × Nat)} {tl : Bytes}
    (hE : jlmE c d start f) (hdep : stk.length + dep = 16) (hs : d.drop pos = 91 :: tl) :
    jlmVAt c d start (f + 1) dep pos stk := by
  by_cases hd16 : 16 ≤ stk.length
  · have hdz : ¬1 ≤ dep := by omega
    have hnone : jlxValue c (f + 1) dep (d.drop pos) = none := by
      have hr : require (decide (dep ≥ 1)) = none := by unfold require; rw [decide_eq_false hdz]; rfl
      rw [hs, jls_pv_arr, hr]; rfl
    exact jlm_V_bad hnone fun k => jlm_pl_deep c d start k stk hs (.inl rfl) hd16
  have hd1 : 1 ≤ dep := by omega
  have hs16 : stk.length < 16 := by omega
  obtain ⟨hw, hqgt, hqL, -, -⟩ := jlm_pl_arr c d start 0 stk hs hs16
  have hr1 : require (decide (dep ≥ 1)) = some () := by rw [require_eq_some]; exact decide_eq_true hd1
  unfold jlmVAt
  rw [hs]
  rcases jlm_head_dec (ws c tl) 93 with ⟨r, hwr⟩ | hnot
  · rw [jls_pv_arr_empty_mk (f := f) hd1 hwr]
    refine ⟨fun h => ?_, fun h => (by cases h)⟩
    cases h
    have hCL := fun k => (jlm_cl_arr c d start k (stk := stk) (st := pos) (e := wsIn c d (pos + 1)) (t := ws c tl)
      hs16 (by rw [jlp_ws_drop, jlp_wsIn_idem, hw])).2.1 r hwr
    have hlt := (hCL 0).2.2
    refine ⟨fun _ => ⟨1, by omega, fun k => ?_, fun k hk => ?_⟩, fun h => (by cases h)⟩
    · rw [(jlm_pl_arr c d start k stk hs hs16).2.2.2.1 r hwr, (hCL k).1]
    · rw [show k = 0 by omega]; exact jlm_err0 c d start stk pos
  have hPL : ∀ k, parseLoop c d start (k + 1) stk pos =
      parseLoop c d start k (stk ++ [(false, pos)]) (wsIn c d (pos + 1)) :=
    fun k => (jlm_pl_arr c d start k stk hs hs16).2.2.2.2 hnot
  have IH := hE (dep := dep - 1) (p := wsIn c d (pos + 1)) (st := pos) stk hqL (by omega)
  rw [hw] at IH
  cases he : jlxElems c f (dep - 1) (ws c tl) with
  | none =>
    have hnone : jlxValue c (f + 1) dep (91 :: tl) = none := by
      rw [jls_pv_arr, hr1, Option.bind_some]
      revert hnot he; generalize ws c tl = w; intro hnot he
      split
      · exact absurd rfl (hnot _)
      · rw [he]; rfl
    rw [hnone]
    exact ⟨fun h => (by cases h), fun _ hf => jlm_all_err fun k => by rw [hPL]; exact IH.2 he (by omega) k⟩
  | some jr =>
    obtain ⟨js, r⟩ := jr
    rw [jls_pv_arr_mk hd1 hnot he]
    refine ⟨fun h => ?_, fun h => (by cases h)⟩
    cases h
    obtain ⟨hltE, -, -⟩ := jlm_pe_end hqL (by rw [hw]; exact he)
    obtain ⟨hIa, hIb⟩ := IH.1 he
    have hnc : noCtlKeys (.arr js) = noCtlElems js := by simp only [noCtlKeys]
    rw [hnc]
    refine ⟨fun h1 => ?_, fun h1 => jlm_all_err fun k => by rw [hPL]; exact hIb h1 k⟩
    obtain ⟨n', hn', hEq', hlo'⟩ := hIa h1
    refine ⟨n' + 1, by omega, fun k => ?_, fun k hk => ?_⟩
    · rw [show k + (n' + 1) = (k + n') + 1 by omega, hPL, hEq']
    · cases k with
      | zero => exact jlm_err0 c d start stk pos
      | succ k => rw [hPL]; exact hlo' k (by omega)

theorem jlm_V_succ {c : Bool} {d : Bytes} {start f : Nat} (hM : jlmM c d start f) (hE : jlmE c d start f) :
    jlmV c d start (f + 1) := by
  intro dep pos stk hpos hdep
  show jlmVAt c d start (f + 1) dep pos stk
  cases hd : d.drop pos with
  | nil =>
    have hl := congrArg List.length hd
    rw [List.length_drop, List.length_nil] at hl
    exact jlm_V_bad (by rw [hd]; exact jls_pv_nil c f dep) fun k => jlm_pl_ge c d start stk (by omega) (k + 1)
  | cons b tl =>
    by_cases h34 : b = 34
    · subst h34
      refine jlm_V_scal (E := (parseString c tl).bind fun (s, r) => some (.str s, r)) hpos
        (by rw [hd, jls_pv_str]) (fun k => ?_) (fun j r h => ?_)
      · rw [jlm_pl_str c d start k stk hd]; cases parseString c tl <;> rfl
      · obtain ⟨⟨s, r'⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
        cases h; rfl
    by_cases h123 : b = 123
    · subst h123; exact jlm_V_obj hM hdep hd
    by_cases h91 : b = 91
    · subst h91; exact jlm_V_arr hE hdep hd
    by_cases hdg : isDigit b = true
    · refine jlm_V_scal (E := parseNumber (b :: tl)) hpos
        (by rw [hd, jls_pv_other c f dep b tl h123 h91 h34]; exact jlp_if_pos hdg)
        (fun k => jlm_pl_num c d start k stk hd hdg) (fun j r h => ?_)
      obtain ⟨n, rfl⟩ := jlw_num_num h; rfl
    by_cases hl : b = 102 ∨ b = 110 ∨ b = 116
    · refine jlm_V_scal (E := parseLiteral (b :: tl)) hpos
        (by rw [hd, jls_pv_other c f dep b tl h123 h91 h34]; exact jlp_if_neg hdg)
        (fun k => jlm_pl_lit c d start k stk hd hl) (fun j r h => ?_)
      rcases jls_lit_inv h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rfl
    refine jlm_V_bad ?_ fun k => jlm_pl_bad c d start k stk hd h34 h91 h123 hl (Bool.eq_false_iff.mpr hdg)
    rw [hd, jls_pv_other c f dep b tl h123 h91 h34, jlp_if_neg hdg]
    cases hp : parseLiteral (b :: tl) with
    | none => rfl
    | some p =>
      obtain ⟨j, r⟩ := p
      obtain ⟨b', tl', he, hb⟩ := jlsc_lit_head hp
      injection he with h1 _
      rw [← h1] at hb
      exact absurd hb hl

theorem jlm_all (c : Bool) (d : Bytes) (start : Nat) :
    ∀ f, jlmV c d start f ∧ jlmM c d start f ∧ jlmE c d start f
  | 0 => ⟨fun _ _ _ => ⟨fun h => (by rw [jls_pv_zero] at h; cases h), fun _ hf => absurd hf (Nat.not_succ_le_zero _)⟩,
      fun _ _ _ _ => ⟨fun h => (by rw [jls_pm_zero] at h; cases h), fun _ hf => absurd hf (Nat.not_succ_le_zero _)⟩,
      fun _ _ _ => ⟨fun h => (by rw [jls_pe_zero] at h; cases h), fun _ hf => absurd hf (Nat.not_succ_le_zero _)⟩⟩
  | f + 1 =>
    have ⟨hV, hM, hE⟩ := jlm_all c d start f
    ⟨jlm_V_succ hM hE, jlm_M_succ hV hM, jlm_E_succ hV hE⟩

theorem jlm_hs0 (c : Bool) (d : Bytes) : d.drop (wsIn c d 0) = ws c d := by
  rw [← jlp_ws_drop, List.drop_zero]

theorem jlm_V_top (c : Bool) (d : Bytes) :
    jlmVAt c d (wsIn c d 0) (2 * d.length + 2) 16 (wsIn c d 0) [] :=
  (jlm_all c d (wsIn c d 0) (2 * d.length + 2)).1 [] (jlp_wsIn_le (Nat.zero_le _)) rfl

theorem jlm_pj {c : Bool} {d : Bytes} {j : Json} :
    jlxJson c d = some j ↔
      ∃ r, jlxValue c (2 * d.length + 2) 16 (ws c d) = some (j, r) ∧ (ws c r).isEmpty = true := by
  constructor
  · intro h
    unfold jlxJson at h
    obtain ⟨⟨v, r⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, h2, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact ⟨r, h1, require_eq_some.mp h2⟩
  · rintro ⟨r, h1, h2⟩
    unfold jlxJson
    rw [h1]
    show (require (ws c r).isEmpty).bind (fun _ => pure j) = some j
    rw [h2]; rfl

theorem jlm_close_top (c : Bool) (d : Bytes) {s0 e : Nat} (hs : s0 ≤ e) (he : e ≤ d.length) :
    closeLoop c d s0 17 [] e = if wsIn c d e = d.length then .ok (.done s0 e) else .error 0x20 := by
  rw [closeLoop.eq_2]
  show (if wsIn c d e ≠ d.length ∨ e < s0 ∨ d.length < e then _ else _) = _
  by_cases h : wsIn c d e = d.length
  · rw [jlp_if_neg (fun h' => by rcases h' with h' | h' | h'; exact h' h; omega; omega), jlp_if_pos h]
  · rw [jlp_if_pos (.inl h), jlp_if_neg h]

theorem jlm_trail {c : Bool} {d r : Bytes} {e : Nat} (he : e ≤ d.length) (hr : d.drop e = r) :
    wsIn c d e = d.length ↔ (ws c r).isEmpty = true := by
  have h1 : d.drop (wsIn c d e) = ws c r := by rw [← jlp_ws_drop, hr]
  have h2 := jlp_wsIn_le (c := c) he
  constructor
  · intro h; rw [← h1, h, List.drop_length]; rfl
  · intro h
    cases hw : ws c r with
    | nil => rw [hw, List.drop_eq_nil_iff] at h1; omega
    | cons a l => rw [hw] at h; cases h

theorem jlm_model_some {c : Bool} {d r : Bytes} {j : Json}
    (h1 : jlxValue c (2 * d.length + 2) 16 (ws c d) = some (j, r)) (hn : noCtlKeys j = true) :
    parseModel c d = if (ws c r).isEmpty then .ok (wsIn c d 0, jlpEnd d r - wsIn c d 0) else .error 0x20 := by
  have h1' : jlxValue c (2 * d.length + 2) 16 (d.drop (wsIn c d 0)) = some (j, r) := by rw [jlm_hs0]; exact h1
  obtain ⟨n, hn', hEq, -⟩ := ((jlm_V_top c d).1 h1').1 hn
  obtain ⟨-, hlt, hle, hdr⟩ := jlw_den (jlp_wsIn_le (Nat.zero_le _)) h1'
  unfold parseModel
  rw [show d.length + 1 = (d.length + 1 - n) + n by omega, hEq, jlm_close_top c d (by omega) hle]
  by_cases ht : wsIn c d (jlpEnd d r) = d.length
  · rw [jlp_if_pos ht, jlp_if_pos ((jlm_trail hle hdr).mp ht)]; rfl
  · rw [jlp_if_neg ht, jlp_if_neg (fun h => ht ((jlm_trail hle hdr).mpr h))]; rfl

theorem jlm_den_top {c : Bool} {d r : Bytes} {j : Json}
    (h1 : jlxValue c (2 * d.length + 2) 16 (ws c d) = some (j, r)) :
    JDenX c d (wsIn c d 0) (jlpEnd d r - wsIn c d 0) j :=
  (jlw_den (jlp_wsIn_le (Nat.zero_le _)) (by rw [jlm_hs0]; exact h1)).1

theorem jlx_ParseJsonSome : jlxParseJsonSomeStmt := by
  intro c d j h hn
  obtain ⟨r, h1, h2⟩ := jlm_pj.mp h
  exact ⟨_, _, by rw [jlm_model_some h1 hn, jlp_if_pos h2], jlm_den_top h1⟩

theorem jlx_ParseModelOk : jlxParseModelOkStmt := by
  intro c d a l h
  cases h1 : jlxValue c (2 * d.length + 2) 16 (ws c d) with
  | none =>
    obtain ⟨e, he⟩ := (jlm_V_top c d).2 (by rw [jlm_hs0]; exact h1) (by omega) (d.length + 1)
    unfold parseModel at h; rw [he] at h; cases h
  | some jr =>
    obtain ⟨j, r⟩ := jr
    have h1' : jlxValue c (2 * d.length + 2) 16 (d.drop (wsIn c d 0)) = some (j, r) := by rw [jlm_hs0]; exact h1
    cases hn : noCtlKeys j
    · obtain ⟨e, he⟩ := ((jlm_V_top c d).1 h1').2 hn (d.length + 1)
      unfold parseModel at h; rw [he] at h; cases h
    · rw [jlm_model_some h1 hn] at h
      by_cases h2 : (ws c r).isEmpty = true
      · rw [jlp_if_pos h2] at h
        cases h
        exact ⟨j, jlm_pj.mpr ⟨r, h1, h2⟩, jlm_den_top h1, hn⟩
      · rw [jlp_if_neg h2] at h; cases h

theorem jlx_ParseModelError : jlxParseModelErrorStmt := by
  intro c d e h j hj
  cases hn : noCtlKeys j
  · refine ⟨?_, rfl⟩
    cases c
    · obtain ⟨r, h1, -⟩ := jlm_pj.mp hj
      have := jlx_StrictNoCtl _ _ (jlm_den_top h1).2
      rw [hn] at this; cases this
    · rfl
  · obtain ⟨a, l, hm, -⟩ := jlx_ParseJsonSome c d j hj hn
    rw [hm] at h; cases h

/-! ## The spec -/

theorem ParseJsonSome : ParseJsonSomeStmt := fun c doc j hj => by
  obtain ⟨hx, hn⟩ := jlf_json.mp hj
  obtain ⟨a, l, hm, hd⟩ := jlx_ParseJsonSome c doc j hx hn
  exact ⟨a, l, hm, jlf_jden.mpr ⟨hd, hn⟩⟩

theorem ParseModelOk : ParseModelOkStmt := fun c doc a l hm => by
  obtain ⟨j, hx, hd, hn⟩ := jlx_ParseModelOk c doc a l hm
  exact ⟨j, jlf_json.mpr ⟨hx, hn⟩, jlf_jden.mpr ⟨hd, hn⟩⟩

theorem ParseModelError : ParseModelErrorStmt := fun c doc e he => by
  cases hp : parseJson c doc with
  | none => rfl
  | some j =>
    obtain ⟨hx, hn⟩ := jlf_json.mp hp
    have h := (jlx_ParseModelError c doc e he j hx).2
    rw [hn] at h; cases h

end C3.Json
