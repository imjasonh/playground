import C3BootProofs.Models.JsonLinkWalk

/-!
# Strings, numbers, cursors, and keys

`strRes`, `u64Val`, and `curOpen` on a value agree with `Json.asStr`,
`Json.asNum`, `Json.asObj`, and `Json.asArr` (`StrRes`, `U64Val`,
`CurOpen`). A strict-mode value has no control byte in a key
(`StrictNoCtl`), and increasing keys are distinct
(`KeysIncreasingDistinct`).
-/

namespace C3.Json

open C3
open C3.RV32 (Word strRes curOpen)

set_option linter.unusedSimpArgs false

theorem jlv_asStr {j : Json} {s : Bytes} (h : j.asStr = some s) : j = .str s := by
  cases j <;> try cases h
  rfl

theorem jlv_asNum {j : Json} {n : Nat} (h : j.asNum = some n) : j = .num n := by
  cases j <;> try cases h
  rfl

theorem jlv_pv_str {c : Bool} {f dep : Nat} {v r : Bytes} {st : Bytes}
    (h : parseValue c (f + 1) dep v = some (.str st, r)) :
    ∃ rest, v = 34 :: rest ∧ parseString c rest = some (st, r) := by
  rcases jls_pv_inv h with ⟨rest, hs, -, ⟨e, -⟩ | ⟨_, e, -⟩⟩ | ⟨rest, hs, -, ⟨e, -⟩ | ⟨_, e, -⟩⟩ |
      ⟨rest, st', hs, e, hp⟩ | ⟨b, tl, hs, -, -, -, -, hn⟩ | ⟨b, tl, hs, -, -, -, -, hl⟩
  · cases e
  · cases e
  · cases e
  · cases e
  · injection e with e; subst e; exact ⟨rest, hs, hp⟩
  · obtain ⟨n, e⟩ := jlw_num_num hn; cases e
  · rcases jls_lit_inv hl with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, -, e⟩ <;> cases e

theorem jlv_pv_num {c : Bool} {f dep n : Nat} {v r : Bytes}
    (h : parseValue c (f + 1) dep v = some (.num n, r)) : parseNumber v = some (.num n, r) := by
  rcases jls_pv_inv h with ⟨rest, hs, -, ⟨e, -⟩ | ⟨_, e, -⟩⟩ | ⟨rest, hs, -, ⟨e, -⟩ | ⟨_, e, -⟩⟩ |
      ⟨rest, st', hs, e, hp⟩ | ⟨b, tl, hs, -, -, -, -, hn⟩ | ⟨b, tl, hs, -, -, -, -, hl⟩
  · cases e
  · cases e
  · cases e
  · cases e
  · cases e
  · exact hn
  · rcases jls_lit_inv hl with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, -, e⟩ <;> cases e

theorem StrRes : StrResStmt := by
  intro c v j p ⟨fuel, dep, h⟩
  cases fuel with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  obtain ⟨b, t, hv, -⟩ := jlw_pv_head h
  subst hv
  have htag := (jlw_tag h).2.2.1
  cases hs : j.asStr with
  | none =>
    refine ⟨?_, fun s e => by cases e⟩
    show strRes p (b :: t) = none
    unfold strRes
    by_cases hL : (b :: t).length < 2
    · rw [jlp_if_pos hL]
    · rw [jlp_if_neg hL, jlp_if_pos (show (b :: t).getD 0 0 ≠ 34 from fun e => by
        have := htag.mp e
        rw [hs] at this
        cases this)]
  | some st =>
    obtain rfl := jlv_asStr hs
    obtain ⟨rest, hv, hp⟩ := jlv_pv_str h
    have hst := jls_str_suf c hp
    rw [hst] at hv
    injection hv with e1 e2
    subst e1; subst e2
    have hv' : (34 :: (st ++ [34]) : Bytes) = (34 :: st) ++ [34] := rfl
    refine ⟨?_, fun s e => by cases e; show (st ++ [34]).take st.length = st; rw [List.take_left' rfl]⟩
    show strRes p (34 :: (st ++ [34])) = some (p + 1, st.length)
    unfold strRes
    have hl : (34 :: (st ++ [34])).length = st.length + 2 := by
      simp only [List.length_cons, List.length_append, List.length_nil]
    have hlast : (34 :: (st ++ [34])).getD ((34 :: (st ++ [34])).length - 1) 0 = 34 := by
      rw [hl, hv', List.getD_eq_getElem?_getD,
        show st.length + 2 - 1 = (34 :: st).length from rfl, List.getElem?_concat_length]
      rfl
    rw [jlp_if_neg (by rw [hl]; omega), jlp_if_neg (fun e => e rfl), jlp_if_neg (fun e => e hlast), hl]
    rfl

/-- The value of at most `|l|` digits after `acc` is below
`(acc + 1) * 10 ^ |l|`. -/
theorem jlv_dv_lt : ∀ (l : Bytes) (acc : Nat), l.all isDigit = true →
    l.foldl (fun n d => 10 * n + (d - 48)) acc < (acc + 1) * 10 ^ l.length
  | [], acc, _ => by
    simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one]; omega
  | b :: l, acc, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    have hb := jlw_digit h.1
    rw [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have := jlv_dv_lt l (10 * acc + (b - 48)) h.2
    calc _ < (10 * acc + (b - 48) + 1) * 10 ^ l.length := this
      _ ≤ (acc + 1) * 10 * 10 ^ l.length := Nat.mul_le_mul_right _ (by omega)
      _ = (acc + 1) * (10 ^ l.length * 10) := by rw [Nat.mul_assoc, Nat.mul_comm 10]

theorem jlv_pow : (10 : Nat) ^ 19 < 2 ^ 64 := by decide

theorem U64Val : U64ValStmt := by
  intro c v j ⟨fuel, dep, h⟩
  cases fuel with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  obtain ⟨b, t, hv, -⟩ := jlw_pv_head h
  subst hv
  have htag := (jlw_tag h).2.2.2
  cases hn : j.asNum with
  | none =>
    show u64Val (b :: t) = none
    unfold u64Val
    rw [jlp_if_neg (List.cons_ne_nil _ _)]
    cases hd : isDigit b
    · rw [jlp_if_pos (by rw [List.all_cons, hd]; rfl)]
    · have := htag.mp hd
      rw [hn] at this
      cases this
  | some n =>
    obtain rfl := jlv_asNum hn
    have hp := jlv_pv_num h
    rw [jls_num_eq] at hp
    obtain ⟨u, hu, hp⟩ := Option.bind_eq_some_iff.mp hp
    injection hp with hp
    injection hp with e1 e2
    injection e1 with e1
    have hc := require_eq_some.mp hu
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hc
    generalize hds : (b :: t).takeWhile isDigit = ds at hc e1 e2
    obtain ⟨t', ht'⟩ : ∃ t', ds ++ t' = b :: t := by rw [← hds]; exact List.takeWhile_prefix isDigit
    have : t' = [] := by
      have := congrArg (List.drop ds.length) ht'
      rw [List.drop_left] at this
      rw [this]; exact e2
    subst this
    rw [List.append_nil] at ht'
    have hall : (b :: t).all isDigit = true := by rw [← ht', ← hds]; exact jlsc_takeWhile_all isDigit _
    have hlt : digitsValue (b :: t) < 2 ^ 64 := by
      have h1 := jlv_dv_lt (b :: t) 0 hall
      rw [Nat.zero_add, Nat.one_mul] at h1
      have h2 : (10 : Nat) ^ (b :: t).length ≤ 10 ^ 19 :=
        Nat.pow_le_pow_right (by decide) (by rw [← ht']; exact hc.1.2)
      exact Nat.lt_trans (Nat.lt_of_lt_of_le h1 h2) jlv_pow
    show u64Val (b :: t) = some n
    unfold u64Val
    rw [jlp_if_neg (List.cons_ne_nil _ _), jlp_if_neg (fun e => by rw [hall] at e; cases e), jlp_if_pos hlt,
      ← e1, ← ht']

theorem CurOpen : CurOpenStmt := by
  intro c v j p ⟨fuel, dep, h⟩
  cases fuel with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  obtain ⟨b, t, hv, -⟩ := jlw_pv_head h
  subst hv
  obtain ⟨ho, ha, -, -⟩ := jlw_tag h
  have hc : ∀ o, curOpen o p (b :: t) = if b = o then some (p, (b :: t).length, skipWs (b :: t) 1) else none := by
    intro o
    unfold curOpen
    rw [jlp_if_neg (show ¬ (b :: t).length = 0 from Nat.succ_ne_zero _)]
    by_cases e : b = o
    · rw [jlp_if_neg (fun h' => h' e), jlp_if_pos e]
    · rw [jlp_if_pos (show (b :: t).getD 0 0 ≠ o from e), jlp_if_neg e]
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]
    by_cases e : b = 123
    · rw [jlp_if_pos e]; exact (ho.mp e).symm
    · rw [jlp_if_neg e]
      cases hx : j.asObj.isSome
      · rfl
      · exact absurd (ho.mpr hx) e
  · rw [hc]
    by_cases e : b = 91
    · rw [jlp_if_pos e]; exact (ha.mp e).symm
    · rw [jlp_if_neg e]
      cases hx : j.asArr.isSome
      · rfl
      · exact absurd (ha.mpr hx) e
  · intro x hx
    rw [hc, hc] at hx
    rcases hx with hx | hx <;> split at hx <;> first | (injection hx with e; exact e.symm) | cases hx

theorem jlv_ps_ctl {l s r : Bytes} (h : parseString false l = some (s, r)) :
    s.all (fun b => decide (0x20 ≤ b)) = true := by
  have h2 := jlp_ps_false (jlp_ps_true h)
  by_cases hc : s.all (fun b => decide (32 ≤ b)) = true
  · exact hc
  · rw [jlp_if_neg hc, h] at h2; cases h2

theorem jlv_strict (f : Nat) :
    (∀ {dep s j r}, parseValue false f dep s = some (j, r) → noCtlKeys j = true) ∧
    (∀ {dep s ms r}, parseMembers false f dep s = some (ms, r) → noCtlMembers ms = true) ∧
    (∀ {dep s js r}, parseElems false f dep s = some (js, r) → noCtlElems js = true) := by
  induction f with
  | zero =>
    exact ⟨fun h => (by rw [jls_pv_zero] at h; cases h), fun h => (by rw [jls_pm_zero] at h; cases h),
      fun h => (by rw [jls_pe_zero] at h; cases h)⟩
  | succ f ih =>
    obtain ⟨ihv, ihm, ihe⟩ := ih
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rcases jls_pv_inv h with ⟨_, _, _, ⟨rfl, _⟩ | ⟨ms, rfl, _, hm, _⟩⟩ | ⟨_, _, _, ⟨rfl, _⟩ | ⟨js, rfl, _, he⟩⟩ |
          ⟨_, st, _, rfl, _⟩ | ⟨_, _, _, _, _, _, _, hn⟩ | ⟨_, _, _, _, _, _, _, hl⟩
      · rfl
      · simp only [noCtlKeys]; exact ihm hm
      · rfl
      · simp only [noCtlKeys]; exact ihe he
      · rfl
      · obtain ⟨n, rfl⟩ := jlw_num_num hn; rfl
      · rcases jls_lit_inv hl with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    · obtain ⟨rest, k, r1, r2, v, r3, _, hk, _, hv, ht⟩ := jls_pm_inv h
      rcases jls_mt_inv ht with ⟨s', more, _, hm, rfl⟩ | ⟨_, rfl⟩
      · simp only [noCtlMembers, Bool.and_eq_true]; exact ⟨⟨jlv_ps_ctl hk, ihv hv⟩, ihm hm⟩
      · simp only [noCtlMembers, Bool.and_eq_true]; exact ⟨⟨jlv_ps_ctl hk, ihv hv⟩, trivial⟩
    · obtain ⟨v, r1, hv, ht⟩ := jls_pe_inv h
      rcases jls_et_inv ht with ⟨s', more, _, hm, rfl⟩ | ⟨_, rfl⟩
      · simp only [noCtlElems, Bool.and_eq_true]; exact ⟨ihv hv, ihe hm⟩
      · simp only [noCtlElems, Bool.and_eq_true]; exact ⟨ihv hv, trivial⟩

theorem StrictNoCtl : StrictNoCtlStmt := fun _ _ ⟨f, _, h⟩ => (jlv_strict f).1 h

theorem jlv_lt_irrefl : ∀ a : Bytes, bytesLt a a = false
  | [] => rfl
  | x :: as => by
    show (decide (x < x) || (x == x && bytesLt as as)) = false
    rw [jlv_lt_irrefl as, Bool.and_false, Bool.or_false]
    exact decide_eq_false (Nat.lt_irrefl x)

theorem jlv_lt_trans : ∀ {a b c : Bytes}, bytesLt a b = true → bytesLt b c = true → bytesLt a c = true
  | [], [], _, h, _ => by cases h
  | [], _ :: _, [], _, h => by cases h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, h => by cases h
  | x :: as, y :: bs, z :: cs, h1, h2 => by
    have e1 : (decide (x < y) || (x == y && bytesLt as bs)) = true := h1
    have e2 : (decide (y < z) || (y == z && bytesLt bs cs)) = true := h2
    show (decide (x < z) || (x == z && bytesLt as cs)) = true
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at e1 e2 ⊢
    rcases e1 with e1 | ⟨rfl, e1⟩ <;> rcases e2 with e2 | ⟨rfl, e2⟩
    · exact .inl (Nat.lt_trans e1 e2)
    · exact .inl e1
    · exact .inl e2
    · exact .inr ⟨rfl, jlv_lt_trans e1 e2⟩

theorem jlv_inc_lt : ∀ {a : Bytes} {l : List Bytes}, keysIncreasing (a :: l) = true → ∀ x ∈ l, bytesLt a x = true
  | _, [], _, _, hx => by cases hx
  | a, b :: l, h, x, hx => by
    have h' : (bytesLt a b && keysIncreasing (b :: l)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h'.1
    · exact jlv_lt_trans h'.1 (jlv_inc_lt h'.2 x hx)

theorem jlv_inc_tail {a : Bytes} {l : List Bytes} (h : keysIncreasing (a :: l) = true) : keysIncreasing l = true := by
  cases l with
  | nil => rfl
  | cons b l => exact ((Bool.and_eq_true _ _).mp h).2

theorem jlv_distinct : ∀ ks : List Bytes, keysIncreasing ks = true → distinct ks = true
  | [], _ => rfl
  | a :: l, h => by
    show (!l.contains a && distinct l) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, jlv_distinct l (jlv_inc_tail h)⟩
    cases hc : l.contains a
    · rfl
    · have := jlv_inc_lt h a (List.contains_iff_mem.mp hc)
      rw [jlv_lt_irrefl] at this
      cases this

theorem KeysIncreasingDistinct : KeysIncreasingDistinctStmt := jlv_distinct

end C3.Json
