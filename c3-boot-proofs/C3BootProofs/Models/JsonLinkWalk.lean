import C3BootProofs.Models.JsonLinkScan

/-!
# Walking an object's members and an array's items

On a value that the spec parses, `nextMember` and `nextElement` step through
the members and items that the spec reads, in order (`Members`,
`Elements`). `get` and `field` then find what `List.lookup` finds (`ObjGet`,
`ObjField`).

In canonical mode the spec allows no whitespace, but the compiled code
skips it in both modes. On a canonical value the byte at each skip is never
whitespace, so the skip stays put (`jlw_skip`).
-/

namespace C3.Json

open C3

set_option linter.unusedSimpArgs false

theorem jlw_isWs_false {b : Nat} (h : 14 ≤ b) (h32 : b ≠ 32) : isWs b = false :=
  Bool.eq_false_iff.mpr fun e => by
    unfold isWs at e
    simp only [Bool.or_eq_true, beq_iff_eq] at e
    rcases e with ((e | e) | e) | e <;> omega

theorem jlw_digit {b : Nat} (h : isDigit b = true) : 48 ≤ b ∧ b ≤ 57 := by
  unfold isDigit at h; rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h; exact h

/-- A value starts with a byte that is not whitespace, a comma, or a
closing bracket. -/
theorem jlw_pv_head {c : Bool} {f dep : Nat} {s r : Bytes} {j : Json} (h : parseValue c f dep s = some (j, r)) :
    ∃ b t, s = b :: t ∧ isWs b = false ∧ b ≠ 93 ∧ b ≠ 125 ∧ b ≠ 44 := by
  cases f with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  rcases jls_pv_inv h with ⟨rest, hs, -⟩ | ⟨rest, hs, -⟩ | ⟨rest, st, hs, -⟩ |
      ⟨b, tl, hs, -, -, -, hd, -⟩ | ⟨b, tl, hs, -, -, -, -, hl⟩
  · exact ⟨_, _, hs, rfl, by decide, by decide, by decide⟩
  · exact ⟨_, _, hs, rfl, by decide, by decide, by decide⟩
  · exact ⟨_, _, hs, rfl, by decide, by decide, by decide⟩
  · have := jlw_digit hd
    exact ⟨b, tl, hs, jlw_isWs_false (by omega) (by omega), by omega, by omega, by omega⟩
  · obtain ⟨b', tl', hs', hb⟩ := jlsc_lit_head hl
    rw [hs] at hs'; injection hs' with e; subst e
    rcases hb with rfl | rfl | rfl <;> exact ⟨_, tl, hs, rfl, by decide, by decide, by decide⟩

theorem jlw_pm_head {c : Bool} {f dep : Nat} {s r : Bytes} {ms : List (Bytes × Json)}
    (h : parseMembers c f dep s = some (ms, r)) : ∃ t, s = 34 :: t := by
  cases f with
  | zero => rw [jls_pm_zero] at h; cases h
  | succ f => obtain ⟨rest, -, -, -, -, -, hs, -⟩ := jls_pm_inv h; exact ⟨rest, hs⟩

theorem jlw_pe_head {c : Bool} {f dep : Nat} {s r : Bytes} {js : List Json}
    (h : parseElems c f dep s = some (js, r)) : ∃ b t, s = b :: t ∧ isWs b = false := by
  cases f with
  | zero => rw [jls_pe_zero] at h; cases h
  | succ f =>
    obtain ⟨v, r1, hv, -⟩ := jls_pe_inv h
    obtain ⟨b, t, hs, hb, -⟩ := jlw_pv_head hv
    exact ⟨b, t, hs, hb⟩

/-- Strict-mode whitespace skipping agrees with mode `c` when the next byte
is not whitespace. -/
theorem jlw_ws_false {c : Bool} {s t : Bytes} {b : Nat} (h : ws c s = b :: t) (hb : isWs b = false) :
    ws false s = b :: t := by
  cases c
  · exact h
  · have hs : s = b :: t := h
    subst hs
    show (b :: t).dropWhile isWs = b :: t
    rw [List.dropWhile_cons, hb]; rfl

theorem jlw_skip {c : Bool} {d t : Bytes} {i b : Nat} (h : ws c (d.drop i) = b :: t) (hb : isWs b = false) :
    d.drop (skipWs d i) = b :: t := by
  rw [jlp_skipWs_eq_wsIn, ← jlp_ws_drop]; exact jlw_ws_false h hb

theorem jlw_skip_le {d : Bytes} {i : Nat} (h : i ≤ d.length) : skipWs d i ≤ d.length := by
  rw [jlp_skipWs_eq_wsIn]; exact jlp_wsIn_le h

theorem jlw_itemTail_fst (d : Bytes) (e : Nat) : (itemTail d e).1 = e := by
  unfold itemTail; split <;> rfl

/-- A value parsed at `i` is the slice from `i` to where the parse stops. -/
theorem jlw_den {c : Bool} {d r : Bytes} {i f dep : Nat} {j : Json} (hi : i ≤ d.length)
    (h : parseValue c f dep (d.drop i) = some (j, r)) :
    JDen c d i (jlpEnd d r - i) j ∧ i < jlpEnd d r ∧ jlpEnd d r ≤ d.length ∧ d.drop (jlpEnd d r) = r := by
  obtain ⟨x, hx, hs⟩ := jls_pv_suf h
  obtain ⟨hr, hlt, hle⟩ := jlp_rest hs hx
  have hl := congrArg List.length hs
  rw [List.length_drop, List.length_append] at hl
  have hxl : jlpEnd d r - i = x.length := by unfold jlpEnd; omega
  refine ⟨⟨by omega, ?_⟩, hlt, hle, hr.symm⟩
  refine ⟨f, dep, (jls_trunc c r f).1 (t := []) ?_⟩
  show parseValue c f dep ((d.drop i).take (jlpEnd d r - i) ++ r) = some (j, r)
  rw [hxl, hs, List.take_left' rfl, ← hs]; exact h

theorem jlw_ws_len (c : Bool) (s : Bytes) : (ws c s).length ≤ s.length := by
  obtain ⟨x, hx⟩ := jls_ws_suf c s
  have := congrArg List.length hx
  rw [List.length_append] at this
  omega

/-- No key in `ms` has a byte below `0x20`. -/
def jlwKeysNC (ms : List (Bytes × Json)) : Bool := ms.all fun m => m.1.all fun b => decide (0x20 ≤ b)

/-- One step of `nextMember` over a member that the spec reads at `p`: it
fails exactly when the key has a control byte. -/
theorem jlw_mstep {c : Bool} {d rest k r1 r2 r3 : Bytes} {p f dep : Nat} {v : Json} (hp : p ≤ d.length)
    (hs : d.drop p = 34 :: rest) (hk : parseString c rest = some (k, r1)) (hc : readExpect [58] (ws c r1) = some r2)
    (hv : parseValue c f dep (ws c r2) = some (v, r3)) :
    nextMember d p = (if k.all (fun b => decide (0x20 ≤ b)) = true then some (some (p + 1, k.length,
        jlpEnd d (ws c r2), jlpEnd d r3 - jlpEnd d (ws c r2), (itemTail d (jlpEnd d r3)).2)) else none) ∧
      slice d (p + 1) k.length = k ∧ JDen c d (jlpEnd d (ws c r2)) (jlpEnd d r3 - jlpEnd d (ws c r2)) v ∧
      jlpEnd d r3 ≤ d.length ∧ d.drop (jlpEnd d r3) = r3 ∧ p < jlpEnd d r3 := by
  obtain ⟨hpL, hb, hrest⟩ := jlp_drop_cons_inv hs
  have hst : rest = k ++ 34 :: r1 := jls_str_suf c hk
  have hl1 := congrArg List.length hs
  rw [List.length_drop, hst] at hl1
  simp only [List.length_cons, List.length_append] at hl1
  have hstr : stringEnd true d p = some (jlpEnd d r1) := by
    rw [jlp_stringEnd hpL, ← hrest, jlp_ps_true hk]; rfl
  have he1 : jlpEnd d r1 = p + k.length + 2 := by unfold jlpEnd; omega
  obtain ⟨b2, t2, hv2, hb2, -⟩ := jlw_pv_head hv
  have hc' : ws c r1 = 58 :: r2 := jls_readExpect_suf hc
  have hw1 := jlw_ws_len c r1
  have hw2 := jlw_ws_len c r2
  rw [hc'] at hw1
  simp only [List.length_cons] at hw1
  have S0 : jlscSuf d (34 :: rest) := by rw [← hs]; exact jlsc_suf_drop d hp
  have S1 := (jlsc_suf_cons S0).1
  rw [hst] at S1
  have S2 := (jlsc_suf_cons (jlsc_suf_app S1).1).1
  obtain ⟨-, S3, -, -⟩ := jlsc_wsS (c := c) S2
  rw [hc'] at S3
  obtain ⟨-, S5, -, -⟩ := jlsc_wsS (c := c) (jlsc_suf_cons S3).1
  have hv' : parseValue c f dep (d.drop (jlpEnd d (ws c r2))) = some (v, r3) := by rw [← S5]; exact hv
  have hvL : jlpEnd d (ws c r2) ≤ d.length := Nat.sub_le _ _
  have hpv : p < jlpEnd d (ws c r2) := by unfold jlpEnd; omega
  obtain ⟨hden, hlt, hle, hd3⟩ := jlw_den hvL hv'
  have hri := jlsc_readItem hvL hv'
  have hsl : slice d (p + 1) k.length = k := by
    show (d.drop (p + 1)).take k.length = k
    rw [← hrest, hst, List.take_left' rfl]
  refine ⟨?_, hsl, hden, hle, hd3, by omega⟩
  unfold nextMember
  rw [jlp_if_neg (fun h' => by rw [hb] at h'; exact absurd h'.2 (by decide)), hstr]
  show memberTail d p (jlpEnd d r1) = _
  unfold memberTail
  rw [he1, jlp_if_neg (fun h' => by rcases h' with h' | h' | h' <;> omega),
    show p + k.length + 2 - 1 - (p + 1) = k.length by omega]
  unfold memberKey
  by_cases hk32 : k.all (fun b => decide (0x20 ≤ b)) = true
  · have hkey : jlpKey false (d.drop p) = some (k, ws c r2) := by
      rw [hs, jlp_key_cons, jlp_if_pos rfl, jlp_ps_false (jlp_ps_true hk), jlp_if_pos hk32]
      simp only [Option.bind_some]
      rw [jlw_ws_false hc' rfl, jlp_readExpect_one, jlp_if_pos rfl]
      simp only [Option.map_some]
      rw [jlw_ws_false hv2 hb2, hv2]
    have hkE : keyEnd false d p = some (jlpEnd d (ws c r2)) := by rw [jlp_keyEnd hp, hkey]; rfl
    rw [jlp_if_pos hk32]
    simp only [hkE, hri, Option.map_some, jlw_itemTail_fst]
  · have hkey : jlpKey false (d.drop p) = none := by
      rw [hs, jlp_key_cons, jlp_if_pos rfl, jlp_ps_false (jlp_ps_true hk), jlp_if_neg hk32]; rfl
    have hkE : keyEnd false d p = none := by rw [jlp_keyEnd hp, hkey]; rfl
    rw [jlp_if_neg hk32]
    simp only [hkE]

theorem jlw_keysNC_cons (k : Bytes) (v : Json) (ms : List (Bytes × Json)) :
    jlwKeysNC ((k, v) :: ms) = (k.all (fun b => decide (0x20 ≤ b)) && jlwKeysNC ms) := rfl

/-- `nextMember` walks the members that the spec reads from position `p`. -/
theorem jlw_members (c : Bool) (d : Bytes) : ∀ f {dep p : Nat} {ms : List (Bytes × Json)} {r : Bytes},
    p ≤ d.length → parseMembers c f dep (d.drop p) = some (ms, r) → jlwKeysNC ms = true →
      MembersFrom c d p ms
  | 0, _, _, _, _, _, h, _ => by rw [jls_pm_zero] at h; cases h
  | f + 1, dep, p, ms, r, hp, h, hn => by
    obtain ⟨rest, k, r1, r2, v, r3, hs, hk, hc, hv, ht⟩ := jls_pm_inv h
    obtain ⟨hnm, hsl, hden, hle, hd3, -⟩ := jlw_mstep hp hs hk hc hv
    have hn' : k.all (fun b => decide (0x20 ≤ b)) = true ∧
        ∀ more, ms = (k, v) :: more → jlwKeysNC more = true := by
      rcases jls_mt_inv ht with ⟨_, more, _, _, rfl⟩ | ⟨_, rfl⟩
      · rw [jlw_keysNC_cons, Bool.and_eq_true] at hn
        exact ⟨hn.1, fun m e => by injection e with _ e; subst e; exact hn.2⟩
      · rw [jlw_keysNC_cons, Bool.and_eq_true] at hn
        exact ⟨hn.1, fun m e => by injection e with _ e; subst e; rfl⟩
    rw [jlp_if_pos hn'.1] at hnm
    rcases jls_mt_inv ht with ⟨s', more, hw3, hm, rfl⟩ | ⟨hw3, rfl⟩
    · have hq := jlw_skip (d := d) (i := jlpEnd d r3) (by rw [hd3]; exact hw3) rfl
      obtain ⟨hqL, hqb, hqs⟩ := jlp_drop_cons_inv hq
      have hit : itemTail d (jlpEnd d r3) = (jlpEnd d r3, skipWs d (skipWs d (jlpEnd d r3) + 1)) := by
        unfold itemTail; rw [jlp_if_pos ⟨hqL, hqb⟩]
      obtain ⟨t4, ht4⟩ := jlw_pm_head hm
      have ha := jlw_skip (d := d) (i := skipWs d (jlpEnd d r3) + 1) (by rw [← hqs]; exact ht4) rfl
      have IH := jlw_members c d f (p := skipWs d (skipWs d (jlpEnd d r3) + 1)) (jlw_skip_le (by omega))
        (by rw [ha, ← ht4]; exact hm) (hn'.2 more rfl)
      simp only [MembersFrom]
      exact ⟨_, _, _, _, by rw [hnm, hit], hsl, hden, IH⟩
    · have hq := jlw_skip (d := d) (i := jlpEnd d r3) (by rw [hd3]; exact hw3) rfl
      obtain ⟨hqL, hqb, -⟩ := jlp_drop_cons_inv hq
      have hit : itemTail d (jlpEnd d r3) = (jlpEnd d r3, skipWs d (jlpEnd d r3)) := by
        unfold itemTail; rw [jlp_if_neg (fun h' => by rw [hqb] at h'; exact absurd h'.2 (by decide))]
      have hend : MembersFrom c d (skipWs d (jlpEnd d r3)) [] := by
        simp only [MembersFrom]; unfold nextMember; rw [jlp_if_pos ⟨hqL, hqb⟩]
      simp only [MembersFrom]
      exact ⟨_, _, _, _, by rw [hnm, hit], hsl, hden, hend⟩

theorem jlw_noCtlMembers : ∀ ms : List (Bytes × Json), noCtlMembers ms = true → jlwKeysNC ms = true
  | [], _ => rfl
  | (k, v) :: ms, h => by
    simp only [noCtlMembers, Bool.and_eq_true] at h
    rw [jlw_keysNC_cons, Bool.and_eq_true]
    exact ⟨h.1.1, jlw_noCtlMembers ms h.2⟩

/-- `nextElement` walks the items that the spec reads from position `p`. -/
theorem jlw_elems (c : Bool) (d : Bytes) : ∀ f {dep p : Nat} {js : List Json} {r : Bytes},
    p ≤ d.length → parseElems c f dep (d.drop p) = some (js, r) → ElementsFrom c d p js
  | 0, _, _, _, _, _, h => by rw [jls_pe_zero] at h; cases h
  | f + 1, dep, p, js, r, hp, h => by
    obtain ⟨v, r1, hv, ht⟩ := jls_pe_inv h
    obtain ⟨b, t, hs, -, hb93, -, -⟩ := jlw_pv_head hv
    obtain ⟨hpL, hb, -⟩ := jlp_drop_cons_inv hs
    obtain ⟨hden, hlt, hle, hd1⟩ := jlw_den hp hv
    have hri := jlsc_readItem hp hv
    have hne : nextElement d p = some (some (p, jlpEnd d r1 - p, (itemTail d (jlpEnd d r1)).2)) := by
      unfold nextElement
      rw [jlp_if_neg (fun h' => hb93 (by rw [← hb]; exact h'.2)), hri]
      simp only [Option.map_some, jlw_itemTail_fst]
    rcases jls_et_inv ht with ⟨s', more, hw, hm, rfl⟩ | ⟨hw, rfl⟩
    · have hq := jlw_skip (d := d) (i := jlpEnd d r1) (by rw [hd1]; exact hw) rfl
      obtain ⟨hqL, hqb, hqs⟩ := jlp_drop_cons_inv hq
      have hit : itemTail d (jlpEnd d r1) = (jlpEnd d r1, skipWs d (skipWs d (jlpEnd d r1) + 1)) := by
        unfold itemTail; rw [jlp_if_pos ⟨hqL, hqb⟩]
      obtain ⟨b4, t4, ht4, hb4⟩ := jlw_pe_head hm
      have ha := jlw_skip (d := d) (i := skipWs d (jlpEnd d r1) + 1) (by rw [← hqs]; exact ht4) hb4
      have IH := jlw_elems c d f (p := skipWs d (skipWs d (jlpEnd d r1) + 1)) (jlw_skip_le (by omega)) (by rw [ha, ← ht4]; exact hm)
      simp only [ElementsFrom]
      exact ⟨_, _, by rw [hne, hit], hden, IH⟩
    · have hq := jlw_skip (d := d) (i := jlpEnd d r1) (by rw [hd1]; exact hw) rfl
      obtain ⟨hqL, hqb, -⟩ := jlp_drop_cons_inv hq
      have hit : itemTail d (jlpEnd d r1) = (jlpEnd d r1, skipWs d (jlpEnd d r1)) := by
        unfold itemTail; rw [jlp_if_neg (fun h' => by rw [hqb] at h'; exact absurd h'.2 (by decide))]
      have hend : ElementsFrom c d (skipWs d (jlpEnd d r1)) [] := by
        simp only [ElementsFrom]; unfold nextElement; rw [jlp_if_pos ⟨hqL, hqb⟩]
      simp only [ElementsFrom]
      exact ⟨_, _, by rw [hne, hit], hden, hend⟩

theorem jlw_num_num {s r : Bytes} {j : Json} (h : parseNumber s = some (j, r)) : ∃ n, j = .num n := by
  rw [jls_num_eq] at h
  obtain ⟨u, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h; exact ⟨_, rfl⟩

theorem jlw_pv_obj {c : Bool} {f dep : Nat} {v r : Bytes} {ms : List (Bytes × Json)}
    (h : parseValue c (f + 1) dep v = some (.obj ms, r)) : ∃ rest, v = 123 :: rest ∧
      ((ms = [] ∧ ws c rest = 125 :: r) ∨
        (parseMembers c f (dep - 1) (ws c rest) = some (ms, r) ∧ keysOk c (ms.map (·.1)) = true)) := by
  rcases jls_pv_inv h with ⟨rest, hs, -, ⟨e, hw⟩ | ⟨ms', e, -, hm, hk⟩⟩ | ⟨rest, hs, -, ⟨e, -⟩ | ⟨_, e, -⟩⟩ |
      ⟨rest, st, hs, e, -⟩ | ⟨b, tl, hs, -, -, -, -, hn⟩ | ⟨b, tl, hs, -, -, -, -, hl⟩
  · injection e with e; exact ⟨rest, hs, .inl ⟨e, hw⟩⟩
  · injection e with e; subst e; exact ⟨rest, hs, .inr ⟨hm, hk⟩⟩
  · cases e
  · cases e
  · cases e
  · obtain ⟨n, e⟩ := jlw_num_num hn; cases e
  · rcases jls_lit_inv hl with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, -, e⟩ <;> cases e

theorem jlw_pv_arr {c : Bool} {f dep : Nat} {v r : Bytes} {js : List Json}
    (h : parseValue c (f + 1) dep v = some (.arr js, r)) : ∃ rest, v = 91 :: rest ∧
      ((js = [] ∧ ws c rest = 93 :: r) ∨ parseElems c f (dep - 1) (ws c rest) = some (js, r)) := by
  rcases jls_pv_inv h with ⟨rest, hs, -, ⟨e, -⟩ | ⟨_, e, -⟩⟩ | ⟨rest, hs, -, ⟨e, hw⟩ | ⟨js', e, -, hm⟩⟩ |
      ⟨rest, st, hs, e, -⟩ | ⟨b, tl, hs, -, -, -, -, hn⟩ | ⟨b, tl, hs, -, -, -, -, hl⟩
  · cases e
  · cases e
  · injection e with e; exact ⟨rest, hs, .inl ⟨e, hw⟩⟩
  · injection e with e; subst e; exact ⟨rest, hs, .inr hm⟩
  · cases e
  · obtain ⟨n, e⟩ := jlw_num_num hn; cases e
  · rcases jls_lit_inv hl with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, -, e⟩ <;> cases e

theorem Members : MembersStmt := by
  intro c v ms ⟨fuel, dep, h⟩ hn
  cases fuel with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  obtain ⟨rest, hv, hc⟩ := jlw_pv_obj h
  have h1 : v.drop 1 = rest := by rw [hv]; rfl
  have hL : 1 ≤ v.length := by rw [hv]; exact Nat.succ_le_succ (Nat.zero_le _)
  rcases hc with ⟨rfl, hw⟩ | ⟨hm, -⟩
  · have hq := jlw_skip (d := v) (i := 1) (by rw [h1]; exact hw) rfl
    obtain ⟨hqL, hqb, -⟩ := jlp_drop_cons_inv hq
    simp only [MembersFrom]; unfold nextMember; rw [jlp_if_pos ⟨hqL, hqb⟩]
  · obtain ⟨t, ht⟩ := jlw_pm_head hm
    have hq := jlw_skip (d := v) (i := 1) (by rw [h1]; exact ht) rfl
    exact jlw_members c v f (jlw_skip_le hL) (by rw [hq, ← ht]; exact hm) (jlw_noCtlMembers ms hn)

theorem Elements : ElementsStmt := by
  intro c v js ⟨fuel, dep, h⟩
  cases fuel with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  obtain ⟨rest, hv, hc⟩ := jlw_pv_arr h
  have h1 : v.drop 1 = rest := by rw [hv]; rfl
  have hL : 1 ≤ v.length := by rw [hv]; exact Nat.succ_le_succ (Nat.zero_le _)
  rcases hc with ⟨rfl, hw⟩ | hm
  · have hq := jlw_skip (d := v) (i := 1) (by rw [h1]; exact hw) rfl
    obtain ⟨hqL, hqb, -⟩ := jlp_drop_cons_inv hq
    simp only [ElementsFrom]; unfold nextElement; rw [jlp_if_pos ⟨hqL, hqb⟩]
  · obtain ⟨b, t, ht, hb⟩ := jlw_pe_head hm
    have hq := jlw_skip (d := v) (i := 1) (by rw [h1]; exact ht) hb
    exact jlw_elems c v f (jlw_skip_le hL) (by rw [hq, ← ht]; exact hm)

theorem ObjKeys : ObjKeysStmt := by
  intro c v ms ⟨fuel, dep, h⟩
  cases fuel with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  obtain ⟨rest, -, ⟨rfl, -⟩ | ⟨-, hk⟩⟩ := jlw_pv_obj h
  · cases c <;> rfl
  · exact hk

theorem jlw_iff_tt {p : Prop} (h : p) : p ↔ true = true := ⟨fun _ => rfl, fun _ => h⟩

theorem jlw_iff_ff {p : Prop} (h : ¬p) : p ↔ false = true := ⟨fun x => absurd x h, fun x => Bool.noConfusion x⟩

/-- The first byte of a value names its kind. -/
theorem jlw_tag {c : Bool} {f dep b : Nat} {t r : Bytes} {j : Json}
    (h : parseValue c (f + 1) dep (b :: t) = some (j, r)) :
    (b = 123 ↔ j.asObj.isSome = true) ∧ (b = 91 ↔ j.asArr.isSome = true) ∧
      (b = 34 ↔ j.asStr.isSome = true) ∧ (isDigit b = true ↔ j.asNum.isSome = true) := by
  rcases jls_pv_inv h with ⟨rest, hs, -, ⟨rfl, -⟩ | ⟨ms, rfl, -⟩⟩ | ⟨rest, hs, -, ⟨rfl, -⟩ | ⟨js, rfl, -⟩⟩ |
      ⟨rest, st, hs, rfl, -⟩ | ⟨b', tl, hs, h1, h2, h3, hd, hn⟩ | ⟨b', tl, hs, h1, h2, h3, hd, hl⟩ <;>
    injection hs with e <;> subst e
  · exact ⟨jlw_iff_tt rfl, jlw_iff_ff (by decide), jlw_iff_ff (by decide), jlw_iff_ff (by decide)⟩
  · exact ⟨jlw_iff_tt rfl, jlw_iff_ff (by decide), jlw_iff_ff (by decide), jlw_iff_ff (by decide)⟩
  · exact ⟨jlw_iff_ff (by decide), jlw_iff_tt rfl, jlw_iff_ff (by decide), jlw_iff_ff (by decide)⟩
  · exact ⟨jlw_iff_ff (by decide), jlw_iff_tt rfl, jlw_iff_ff (by decide), jlw_iff_ff (by decide)⟩
  · exact ⟨jlw_iff_ff (by decide), jlw_iff_ff (by decide), jlw_iff_tt rfl, jlw_iff_ff (by decide)⟩
  · obtain ⟨n, rfl⟩ := jlw_num_num hn
    exact ⟨jlw_iff_ff h1, jlw_iff_ff h2, jlw_iff_ff h3, jlw_iff_tt hd⟩
  · have hd' : ¬ isDigit b = true := by rw [hd]; decide
    rcases jls_lit_inv hl with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
      exact ⟨jlw_iff_ff h1, jlw_iff_ff h2, jlw_iff_ff h3, jlw_iff_ff hd'⟩

theorem jlw_nm_none {d : Bytes} {p : Nat} (h : nextMember d p = some none) : p < d.length := by
  unfold nextMember at h
  by_cases hc : p < d.length ∧ d.getD p 0 = 125
  · exact hc.1
  · rw [jlp_if_neg hc] at h
    obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
    unfold memberTail at h
    split at h
    · cases h
    · unfold memberKey at h
      split at h
      · cases h
      · obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.mp h
        cases hx

theorem jlw_mf_len {c : Bool} {d : Bytes} : ∀ {p : Nat} {ms : List (Bytes × Json)},
    MembersFrom c d p ms → p + ms.length < d.length
  | p, [], h => by simp only [MembersFrom] at h; exact jlw_nm_none h
  | p, (k, j) :: ms, h => by
    simp only [MembersFrom] at h
    obtain ⟨kp, vp, vl, a, hn, -, -, hm⟩ := h
    have h1 := (nextMember_lt hn).2.1
    have h2 := jlw_mf_len hm
    simp only [List.length_cons]; omega

/-- `get`'s loop finds what `List.lookup` finds. -/
theorem jlw_getFrom {c : Bool} {d key : Bytes} : ∀ {p : Nat} {ms : List (Bytes × Json)}, MembersFrom c d p ms →
    ∀ k, ms.length < k → match ms.lookup key with
      | none => getFrom d key k p = some none
      | some j' => ∃ vp vl, getFrom d key k p = some (some (vp, vl)) ∧ JDen c d vp vl j'
  | p, [], h, k + 1, _ => by
    simp only [MembersFrom] at h
    show getFrom d key (k + 1) p = some none
    simp only [getFrom, h]
  | p, (k0, j0) :: ms, h, k + 1, hk => by
    simp only [MembersFrom] at h
    obtain ⟨kp, vp, vl, a, hn, hsl, hden, hm⟩ := h
    have hsl' : (d.drop kp).take k0.length = k0 := hsl
    rw [List.lookup_cons]
    by_cases he : k0 = key
    · subst he
      rw [show (k0 == k0) = true from beq_iff_eq.mpr rfl]
      show ∃ vp vl, getFrom d k0 (k + 1) p = some (some (vp, vl)) ∧ JDen c d vp vl j0
      refine ⟨vp, vl, ?_, hden⟩
      simp only [getFrom, hn]
      rw [jlp_if_pos hsl']
    · rw [show (key == k0) = false from Bool.eq_false_iff.mpr fun e => he (beq_iff_eq.mp e).symm]
      have IH := jlw_getFrom (key := key) hm k (by simp only [List.length_cons] at hk; omega)
      have hg : getFrom d key (k + 1) p = getFrom d key k a := by
        simp only [getFrom, hn]; rw [jlp_if_neg (fun e => he (hsl'.symm.trans e))]
      rw [hg]; exact IH
  | _, _, _, 0, hk => absurd hk (Nat.not_lt_zero _)

theorem ObjGet : ObjGetStmt := by
  intro c v j key ⟨fuel, dep, h⟩ hn
  cases fuel with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  obtain ⟨b, t, hv, -⟩ := jlw_pv_head h
  subst hv
  have htag := (jlw_tag h).1
  cases hj : j.asObj with
  | none =>
    show objGet (b :: t) key = .error 0x21
    unfold objGet
    rw [jlp_if_pos (.inr fun e => by
      have := htag.mp e
      rw [hj] at this
      cases this)]
  | some ms =>
    cases j
    case obj ms' =>
      have e : ms' = ms := Option.some.inj hj
      subst e
      have hn' : noCtlMembers ms' = true := by simp only [noCtlKeys] at hn; exact hn
      have hMF := Members c (b :: t) ms' ⟨f + 1, dep, h⟩ hn'
      have hlen := jlw_mf_len hMF
      have G := jlw_getFrom (key := key) hMF ((b :: t).length + 1) (by omega)
      have hobj : objGet (b :: t) key =
          getOut (getFrom (b :: t) key ((b :: t).length + 1) (skipWs (b :: t) 1)) := by
        unfold objGet
        rw [jlp_if_neg (fun e => by
          rcases e with e | e
          · exact absurd e (Nat.succ_ne_zero _)
          · exact e (htag.mpr rfl))]
      show match ms'.lookup key with
        | none => objGet (b :: t) key = .ok none
        | some j' => ∃ vp vl, objGet (b :: t) key = .ok (some (vp, vl)) ∧ JDen c (b :: t) vp vl j'
      rw [hobj]
      revert G
      cases ms'.lookup key with
      | none => intro G; rw [G]; rfl
      | some j' =>
        intro G
        obtain ⟨vp, vl, hg, hd⟩ := G
        exact ⟨vp, vl, by rw [hg]; rfl, hd⟩
    all_goals cases hj

theorem ObjField : ObjFieldStmt := by
  intro c v j key hj hn
  have G := ObjGet c v j key hj hn
  cases j
  case obj ms =>
    show match ms.lookup key with
      | none => objField v key = .error 0x21
      | some j' => ∃ vp vl, objField v key = .ok (vp, vl) ∧ JDen c v vp vl j'
    revert G
    show (match ms.lookup key with
      | none => objGet v key = .ok none
      | some j' => ∃ vp vl, objGet v key = .ok (some (vp, vl)) ∧ JDen c v vp vl j') → _
    cases ms.lookup key with
    | none => intro G; unfold objField; rw [G]
    | some j' =>
      intro G
      obtain ⟨vp, vl, hg, hd⟩ := G
      exact ⟨vp, vl, by unfold objField; rw [hg], hd⟩
  all_goals
    show objField v key = .error 0x21
    unfold objField
    rw [show objGet v key = .error 0x21 from G]

end C3.Json
