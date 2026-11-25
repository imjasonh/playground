import C3BootProofs.Models.JsonLinkPos

/-!
# `valueEnd` on values the spec parses

`valueEnd` finds the end of an object or an array by counting brackets and
skipping strings, without parsing what is inside. On a value that the spec
parses, it stops where the spec's parse stops (`jlsc_valueEnd`).

Positions here are the positions of suffixes of the document `d`:
`jlscSuf d s` says `s` is `d` from `jlpEnd d s`.
-/

namespace C3.Json

open C3

set_option linter.unusedSimpArgs false

/-- A byte that `cScan` steps over: not a quote or a bracket. -/
def jlscPlain (b : Nat) : Bool := !(b == 34 || b == 91 || b == 123 || b == 93 || b == 125)

/-- `s` is the document from position `jlpEnd d s`. -/
def jlscSuf (d s : Bytes) : Prop := s = d.drop (jlpEnd d s)

/-- An object or an array. -/
def jlscCont : Json → Bool
  | .obj _ => true
  | .arr _ => true
  | _ => false

theorem jlsc_suf_drop (d : Bytes) {e : Nat} (h : e ≤ d.length) : jlscSuf d (d.drop e) := by
  unfold jlscSuf; rw [jlp_end_drop d h]

theorem jlsc_suf_app {d x s : Bytes} (h : jlscSuf d (x ++ s)) :
    jlscSuf d s ∧ jlpEnd d s = jlpEnd d (x ++ s) + x.length := by
  have hl := congrArg List.length h
  rw [List.length_drop, List.length_append] at hl
  have he : jlpEnd d s = jlpEnd d (x ++ s) + x.length := by
    unfold jlpEnd; rw [List.length_append]; omega
  refine ⟨?_, he⟩
  have := congrArg (List.drop x.length) h
  rw [List.drop_drop, List.drop_left] at this
  unfold jlscSuf; rw [he]; exact this

theorem jlsc_suf_cons {d s : Bytes} {b : Nat} (h : jlscSuf d (b :: s)) :
    jlscSuf d s ∧ jlpEnd d s = jlpEnd d (b :: s) + 1 := jlsc_suf_app (x := [b]) h

theorem jlsc_cons {d s : Bytes} {b : Nat} (h : jlscSuf d (b :: s)) :
    ¬ d.length ≤ jlpEnd d (b :: s) ∧ d.getD (jlpEnd d (b :: s)) 0 = b := by
  obtain ⟨h1, h2, -⟩ := jlp_drop_cons_inv h.symm
  exact ⟨by omega, h2⟩

theorem jlsc_step (d : Bytes) (k δ i : Nat) : cScan d (k + 1) δ i =
    if d.length ≤ i then none
    else if d.getD i 0 = 34 then (stringEnd true d i).bind (cScan d k δ)
    else if d.getD i 0 = 91 ∨ d.getD i 0 = 123 then cScan d k (δ + 1) (i + 1)
    else if d.getD i 0 = 93 ∨ d.getD i 0 = 125 then
      (if δ = 0 then none else if δ = 1 then some (i + 1) else cScan d k (δ - 1) (i + 1))
    else cScan d k δ (i + 1) := rfl

theorem jlsc_plain_ne {b : Nat} (h : jlscPlain b = true) : b ≠ 34 ∧ ¬(b = 91 ∨ b = 123) ∧ ¬(b = 93 ∨ b = 125) := by
  unfold jlscPlain at h
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, fun h => h.elim h2 h3, fun h => h.elim h4 h5⟩

theorem jlsc_plain_step {d s : Bytes} {b : Nat} (k δ : Nat) (h : jlscSuf d (b :: s)) (hb : jlscPlain b = true) :
    cScan d (k + 1) δ (jlpEnd d (b :: s)) = cScan d k δ (jlpEnd d s) := by
  obtain ⟨hL, hg⟩ := jlsc_cons h
  obtain ⟨n1, n2, n3⟩ := jlsc_plain_ne hb
  rw [jlsc_step, jlp_if_neg hL, hg, jlp_if_neg n1, jlp_if_neg n2, jlp_if_neg n3, (jlsc_suf_cons h).2]

theorem jlsc_run {d s : Bytes} (k δ : Nat) : ∀ {x : Bytes}, jlscSuf d (x ++ s) → x.all jlscPlain = true →
    cScan d (k + x.length) δ (jlpEnd d (x ++ s)) = cScan d k δ (jlpEnd d s)
  | [], _, _ => rfl
  | b :: x, h, hx => by
    rw [List.all_cons, Bool.and_eq_true] at hx
    have h' : jlscSuf d (b :: (x ++ s)) := h
    rw [List.length_cons, ← Nat.add_assoc, List.cons_append, jlsc_plain_step _ _ h' hx.1]
    exact jlsc_run k δ (jlsc_suf_cons h').1 hx.2

theorem jlsc_str {c : Bool} {d rest st r : Bytes} (k δ : Nat) (h : jlscSuf d (34 :: rest))
    (hs : parseString c rest = some (st, r)) :
    cScan d (k + 1) δ (jlpEnd d (34 :: rest)) = cScan d k δ (jlpEnd d r) := by
  obtain ⟨hL, hg⟩ := jlsc_cons h
  obtain ⟨h1, h2⟩ := jlsc_suf_cons h
  rw [jlsc_step, jlp_if_neg hL, hg, jlp_if_pos rfl, jlp_stringEnd (by omega), ← h2, ← h1, jlp_ps_true hs]
  rfl

theorem jlsc_open {d r : Bytes} {b : Nat} (k δ : Nat) (h : jlscSuf d (b :: r)) (hb : b = 91 ∨ b = 123) :
    cScan d (k + 1) δ (jlpEnd d (b :: r)) = cScan d k (δ + 1) (jlpEnd d r) := by
  obtain ⟨hL, hg⟩ := jlsc_cons h
  have n1 : b ≠ 34 := by rcases hb with rfl | rfl <;> decide
  rw [jlsc_step, jlp_if_neg hL, hg, jlp_if_neg n1, jlp_if_pos hb, (jlsc_suf_cons h).2]

theorem jlsc_close {d r : Bytes} {b : Nat} (k δ : Nat) (h : jlscSuf d (b :: r)) (hb : b = 93 ∨ b = 125) :
    cScan d (k + 1) (δ + 1) (jlpEnd d (b :: r)) = if δ = 0 then some (jlpEnd d r) else cScan d k δ (jlpEnd d r) := by
  obtain ⟨hL, hg⟩ := jlsc_cons h
  have n1 : b ≠ 34 := by rcases hb with rfl | rfl <;> decide
  have n2 : ¬(b = 91 ∨ b = 123) := by rcases hb with rfl | rfl <;> decide
  rw [jlsc_step, jlp_if_neg hL, hg, jlp_if_neg n1, jlp_if_neg n2, jlp_if_pos hb, (jlsc_suf_cons h).2,
    jlp_if_neg (Nat.succ_ne_zero δ)]
  by_cases h0 : δ = 0
  · subst h0; rfl
  · rw [jlp_if_neg (show δ + 1 ≠ 1 by omega), jlp_if_neg h0]; rfl

/-! ## Plain runs in the spec's tokens -/

theorem jlsc_ws_plain {b : Nat} (h : isWs b = true) : jlscPlain b = true := by
  unfold isWs at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> rfl

theorem jlsc_digit_plain {b : Nat} (h : isDigit b = true) : jlscPlain b = true := by
  unfold isDigit at h
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
  have hne : ∀ {m : Nat}, (m < 48 ∨ 57 < m) → (b == m) = false := fun hm =>
    Bool.eq_false_iff.mpr fun e => by
      have := beq_iff_eq.mp e
      rcases hm with hm | hm <;> omega
  unfold jlscPlain
  rw [hne (.inl (by decide)), hne (.inr (by decide)), hne (.inr (by decide)), hne (.inr (by decide)),
    hne (.inr (by decide))]
  rfl

theorem jlsc_takeWhile_all (p : Nat → Bool) : ∀ l : Bytes, (l.takeWhile p).all p = true
  | [] => rfl
  | b :: l => by
    rw [List.takeWhile_cons]
    cases h : p b
    · rfl
    · simp only [↓reduceIte, List.all_cons, h, Bool.true_and]; exact jlsc_takeWhile_all p l

theorem jlsc_all_mono {p q : Nat → Bool} (h : ∀ b, p b = true → q b = true) :
    ∀ l : Bytes, l.all p = true → l.all q = true
  | [], _ => rfl
  | b :: l, hl => by
    rw [List.all_cons, Bool.and_eq_true] at hl ⊢
    exact ⟨h b hl.1, jlsc_all_mono h l hl.2⟩

theorem jlsc_ws_split (c : Bool) (s : Bytes) : ∃ a, s = a ++ ws c s ∧ a.all jlscPlain = true := by
  unfold ws; cases c
  · exact ⟨s.takeWhile isWs, (List.takeWhile_append_dropWhile).symm,
      jlsc_all_mono (fun _ => jlsc_ws_plain) _ (jlsc_takeWhile_all isWs s)⟩
  · exact ⟨[], rfl, rfl⟩

theorem jlsc_num_split {s r : Bytes} {j : Json} (h : parseNumber s = some (j, r)) :
    ∃ x, s = x ++ r ∧ x.all jlscPlain = true := by
  rw [jls_num_eq] at h
  obtain ⟨u, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  obtain ⟨t, ht⟩ := List.takeWhile_prefix (l := s) isDigit
  have hd : s.drop (s.takeWhile isDigit).length = t := by
    have := congrArg (List.drop (s.takeWhile isDigit).length) ht
    rw [List.drop_left] at this
    exact this.symm
  exact ⟨s.takeWhile isDigit, by rw [hd, ht],
    jlsc_all_mono (fun _ => jlsc_digit_plain) _ (jlsc_takeWhile_all isDigit s)⟩

theorem jlsc_lit_split {s r : Bytes} {j : Json} (h : parseLiteral s = some (j, r)) :
    ∃ x, s = x ++ r ∧ x.all jlscPlain = true := by
  rcases jls_lit_inv h with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, -, h1, -⟩ <;>
    exact ⟨_, jls_readExpect_suf h1, rfl⟩

/-! ## Steps with their positions -/

theorem jlsc_runS {d s' x s : Bytes} (e : s' = x ++ s) (h : jlscSuf d s') (hx : x.all jlscPlain = true) :
    jlscSuf d s ∧ jlpEnd d s = jlpEnd d s' + x.length ∧
      ∀ k δ, cScan d (k + x.length) δ (jlpEnd d s') = cScan d k δ (jlpEnd d s) := by
  subst e
  obtain ⟨h1, h2⟩ := jlsc_suf_app h
  exact ⟨h1, h2, fun k δ => jlsc_run k δ h hx⟩

theorem jlsc_wsS {c : Bool} {d s : Bytes} (h : jlscSuf d s) : ∃ a : Bytes,
    jlscSuf d (ws c s) ∧ jlpEnd d (ws c s) = jlpEnd d s + a.length ∧
      ∀ k δ, cScan d (k + a.length) δ (jlpEnd d s) = cScan d k δ (jlpEnd d (ws c s)) := by
  obtain ⟨a, ha, hp⟩ := jlsc_ws_split c s
  exact ⟨a, jlsc_runS ha h hp⟩

theorem jlsc_strS {c : Bool} {d rest st r : Bytes} (h : jlscSuf d (34 :: rest)) (hs : parseString c rest = some (st, r)) :
    jlscSuf d r ∧ jlpEnd d (34 :: rest) < jlpEnd d r ∧
      ∀ k δ, cScan d (k + 1) δ (jlpEnd d (34 :: rest)) = cScan d k δ (jlpEnd d r) := by
  have e : 34 :: rest = (34 :: st ++ [34]) ++ r := by rw [jls_str_suf c hs]; simp
  obtain ⟨h1, h2⟩ := jlsc_suf_app (e ▸ h)
  rw [← e] at h2
  refine ⟨h1, ?_, fun k δ => jlsc_str k δ h hs⟩
  rw [h2]; simp only [List.length_append, List.length_cons]; omega

theorem jlsc_oneS {d s r : Bytes} {b : Nat} (e : s = b :: r) (h : jlscSuf d s) (hb : jlscPlain b = true) :
    jlscSuf d r ∧ jlpEnd d r = jlpEnd d s + 1 ∧ ∀ k δ, cScan d (k + 1) δ (jlpEnd d s) = cScan d k δ (jlpEnd d r) := by
  have := jlsc_runS (x := [b]) e h (by simp only [List.all_cons, hb, List.all_nil, Bool.and_self])
  exact this

theorem jlsc_chain {d : Bytes} {δ p q n m : Nat} {H : Nat → Option Nat}
    (h1 : ∀ k, cScan d (k + n) δ p = cScan d k δ q) (h2 : ∀ k, cScan d (k + m) δ q = H k) :
    ∀ k, cScan d (k + (m + n)) δ p = H k := fun k => by rw [← Nat.add_assoc, h1, h2]

theorem jlsc_scalar {d : Bytes} {p e n : Nat} {j : Json} (hj : jlscCont j = false)
    (h : ∀ k δ, cScan d (k + n) δ p = cScan d k δ e) :
    (∀ k δ, cScan d (k + n) (δ + 1) p = cScan d k (δ + 1) e) ∧
      (jlscCont j = true → ∀ k, cScan d (k + n) 0 p = some e) :=
  ⟨fun k δ => h k (δ + 1), fun h' => absurd (hj ▸ h') (by decide)⟩

theorem jlsc_container {d : Bytes} {p e n : Nat} {j : Json}
    (h : ∀ k δ, cScan d (k + n) δ p = if δ = 0 then some e else cScan d k δ e) :
    (∀ k δ, cScan d (k + n) (δ + 1) p = cScan d k (δ + 1) e) ∧
      (jlscCont j = true → ∀ k, cScan d (k + n) 0 p = some e) :=
  ⟨fun k δ => by rw [h, jlp_if_neg (Nat.succ_ne_zero δ)], fun _ k => by rw [h, jlp_if_pos rfl]⟩

/-- How `cScan` reads a value, members, or elements that the spec parses
from `s`: the members and the elements through the bracket that closes
them. -/
theorem jlsc_main (c : Bool) (d : Bytes) : ∀ f,
    (∀ {dep s j r}, jlscSuf d s → parseValue c f dep s = some (j, r) →
      ∃ n, jlpEnd d s + n ≤ jlpEnd d r ∧
        (∀ k δ, cScan d (k + n) (δ + 1) (jlpEnd d s) = cScan d k (δ + 1) (jlpEnd d r)) ∧
        (jlscCont j = true → ∀ k, cScan d (k + n) 0 (jlpEnd d s) = some (jlpEnd d r))) ∧
    (∀ {dep s ms r}, jlscSuf d s → parseMembers c f dep s = some (ms, r) →
      ∃ n, jlpEnd d s + n ≤ jlpEnd d r ∧ ∀ k δ,
        cScan d (k + n) (δ + 1) (jlpEnd d s) = if δ = 0 then some (jlpEnd d r) else cScan d k δ (jlpEnd d r)) ∧
    (∀ {dep s js r}, jlscSuf d s → parseElems c f dep s = some (js, r) →
      ∃ n, jlpEnd d s + n ≤ jlpEnd d r ∧ ∀ k δ,
        cScan d (k + n) (δ + 1) (jlpEnd d s) = if δ = 0 then some (jlpEnd d r) else cScan d k δ (jlpEnd d r))
  | 0 => by
    refine ⟨fun _ h => ?_, fun _ h => ?_, fun _ h => ?_⟩
    · rw [jls_pv_zero] at h; cases h
    · rw [jls_pm_zero] at h; cases h
    · rw [jls_pe_zero] at h; cases h
  | f + 1 => by
    obtain ⟨ihv, ihm, ihe⟩ := jlsc_main c d f
    refine ⟨fun {dep s j r} hs h => ?_, fun {dep s ms r} hs h => ?_, fun {dep s js r} hs h => ?_⟩
    · rcases jls_pv_inv h with ⟨rest, rfl, -, ⟨rfl, hw⟩ | ⟨ms, rfl, -, hm, -⟩⟩ |
          ⟨rest, rfl, -, ⟨rfl, hw⟩ | ⟨it, rfl, -, he⟩⟩ | ⟨rest, st, rfl, rfl, hst⟩ |
          ⟨b, tl, rfl, -, -, -, -, hn⟩ | ⟨b, tl, rfl, -, -, -, -, hl⟩
      · obtain ⟨hr, hp⟩ := jlsc_suf_cons hs
        obtain ⟨a, hwa, hpa, hra⟩ := jlsc_wsS (c := c) hr
        rw [hw] at hwa hpa hra
        obtain ⟨hr', hpr⟩ := jlsc_suf_cons hwa
        refine ⟨1 + a.length + 1, by omega, jlsc_container fun k δ => ?_⟩
        rw [show k + (1 + a.length + 1) = (k + 1 + a.length) + 1 by omega, jlsc_open _ _ hs (.inr rfl),
          hra, jlsc_close _ _ hwa (.inr rfl)]
      · obtain ⟨hr, hp⟩ := jlsc_suf_cons hs
        obtain ⟨a, hwa, hpa, hra⟩ := jlsc_wsS (c := c) hr
        obtain ⟨n, hn, hM⟩ := ihm hwa hm
        refine ⟨n + a.length + 1, by omega, jlsc_container fun k δ => ?_⟩
        rw [show k + (n + a.length + 1) = (k + n + a.length) + 1 by omega, jlsc_open _ _ hs (.inr rfl), hra, hM]
      · obtain ⟨hr, hp⟩ := jlsc_suf_cons hs
        obtain ⟨a, hwa, hpa, hra⟩ := jlsc_wsS (c := c) hr
        rw [hw] at hwa hpa hra
        obtain ⟨hr', hpr⟩ := jlsc_suf_cons hwa
        refine ⟨1 + a.length + 1, by omega, jlsc_container fun k δ => ?_⟩
        rw [show k + (1 + a.length + 1) = (k + 1 + a.length) + 1 by omega, jlsc_open _ _ hs (.inl rfl),
          hra, jlsc_close _ _ hwa (.inl rfl)]
      · obtain ⟨hr, hp⟩ := jlsc_suf_cons hs
        obtain ⟨a, hwa, hpa, hra⟩ := jlsc_wsS (c := c) hr
        obtain ⟨n, hn, hE⟩ := ihe hwa he
        refine ⟨n + a.length + 1, by omega, jlsc_container fun k δ => ?_⟩
        rw [show k + (n + a.length + 1) = (k + n + a.length) + 1 by omega, jlsc_open _ _ hs (.inl rfl), hra, hE]
      · obtain ⟨-, hp, hS⟩ := jlsc_strS hs hst
        exact ⟨1, by omega, jlsc_scalar rfl hS⟩
      · obtain ⟨x, hx, hpl⟩ := jlsc_num_split hn
        obtain ⟨-, hp, hS⟩ := jlsc_runS hx hs hpl
        have hj : jlscCont j = false := by
          rw [jls_num_eq] at hn
          obtain ⟨u, -, hn⟩ := Option.bind_eq_some_iff.mp hn
          cases hn; rfl
        exact ⟨x.length, by omega, jlsc_scalar hj hS⟩
      · obtain ⟨x, hx, hpl⟩ := jlsc_lit_split hl
        obtain ⟨-, hp, hS⟩ := jlsc_runS hx hs hpl
        have hj : jlscCont j = false := by
          rcases jls_lit_inv hl with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rfl
        exact ⟨x.length, by omega, jlsc_scalar hj hS⟩
    · obtain ⟨rest, ky, r1, r2, v, r3, rfl, h1, h2, h3, h4⟩ := jls_pm_inv h
      obtain ⟨hr1, hp1, S1⟩ := jlsc_strS hs h1
      obtain ⟨a1, hw1, hpw1, S2⟩ := jlsc_wsS (c := c) hr1
      obtain ⟨hr2, hp2, S3⟩ := jlsc_oneS ((jls_readExpect_suf h2).trans rfl : ws c r1 = 58 :: r2) hw1 rfl
      obtain ⟨a2, hw2, hpw2, S4⟩ := jlsc_wsS (c := c) hr2
      obtain ⟨nv, hnv, S5, -⟩ := ihv hw2 h3
      have hr3 : jlscSuf d r3 := by
        obtain ⟨x, -, hx⟩ := jls_pv_suf h3
        exact (jlsc_suf_app (hx ▸ hw2)).1
      obtain ⟨a3, hw3, hpw3, S6⟩ := jlsc_wsS (c := c) hr3
      rcases jls_mt_inv h4 with ⟨s', more, hs', hm, rfl⟩ | ⟨hs', rfl⟩
      · obtain ⟨hr4, hp4, S7⟩ := jlsc_oneS hs' hw3 rfl
        obtain ⟨a4, hw4, hpw4, S8⟩ := jlsc_wsS (c := c) hr4
        obtain ⟨nm, hnm, S9⟩ := ihm hw4 hm
        refine ⟨nm + a4.length + 1 + a3.length + nv + a2.length + 1 + a1.length + 1, by omega, fun k δ => ?_⟩
        exact jlsc_chain (fun k => S1 k (δ + 1)) (jlsc_chain (fun k => S2 k (δ + 1))
          (jlsc_chain (fun k => S3 k (δ + 1)) (jlsc_chain (fun k => S4 k (δ + 1))
          (jlsc_chain (fun k => S5 k δ) (jlsc_chain (fun k => S6 k (δ + 1))
          (jlsc_chain (fun k => S7 k (δ + 1)) (jlsc_chain (fun k => S8 k (δ + 1)) (fun k => S9 k δ)))))))) k
      · rw [hs'] at hw3 hpw3 S6
        obtain ⟨-, hpr⟩ := jlsc_suf_cons hw3
        refine ⟨1 + a3.length + nv + a2.length + 1 + a1.length + 1, by omega, fun k δ => ?_⟩
        exact jlsc_chain (fun k => S1 k (δ + 1)) (jlsc_chain (fun k => S2 k (δ + 1))
          (jlsc_chain (fun k => S3 k (δ + 1)) (jlsc_chain (fun k => S4 k (δ + 1))
          (jlsc_chain (fun k => S5 k δ) (jlsc_chain (fun k => S6 k (δ + 1))
          (fun k => jlsc_close k δ hw3 (.inr rfl))))))) k
    · obtain ⟨v, r1, h1, h2⟩ := jls_pe_inv h
      obtain ⟨nv, hnv, S1, -⟩ := ihv hs h1
      have hr1 : jlscSuf d r1 := by
        obtain ⟨x, -, hx⟩ := jls_pv_suf h1
        exact (jlsc_suf_app (hx ▸ hs)).1
      obtain ⟨a1, hw1, hpw1, S2⟩ := jlsc_wsS (c := c) hr1
      rcases jls_et_inv h2 with ⟨s', more, hs', hm, rfl⟩ | ⟨hs', rfl⟩
      · obtain ⟨hr4, hp4, S3⟩ := jlsc_oneS hs' hw1 rfl
        obtain ⟨a4, hw4, hpw4, S4⟩ := jlsc_wsS (c := c) hr4
        obtain ⟨ne, hne, S5⟩ := ihe hw4 hm
        refine ⟨ne + a4.length + 1 + a1.length + nv, by omega, fun k δ => ?_⟩
        exact jlsc_chain (fun k => S1 k δ) (jlsc_chain (fun k => S2 k (δ + 1))
          (jlsc_chain (fun k => S3 k (δ + 1)) (jlsc_chain (fun k => S4 k (δ + 1)) (fun k => S5 k δ)))) k
      · rw [hs'] at hw1 hpw1 S2
        obtain ⟨-, hpr⟩ := jlsc_suf_cons hw1
        refine ⟨1 + a1.length + nv, by omega, fun k δ => ?_⟩
        exact jlsc_chain (fun k => S1 k δ) (jlsc_chain (fun k => S2 k (δ + 1))
          (fun k => jlsc_close k δ hw1 (.inl rfl))) k

theorem jlsc_lit_head {s r : Bytes} {j : Json} (h : parseLiteral s = some (j, r)) :
    ∃ b tl, s = b :: tl ∧ (b = 102 ∨ b = 110 ∨ b = 116) := by
  rcases jls_lit_inv h with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, -, h1, -⟩
  · exact ⟨_, _, jls_readExpect_suf h1, .inr (.inr rfl)⟩
  · exact ⟨_, _, jls_readExpect_suf h1, .inl rfl⟩
  · exact ⟨_, _, jls_readExpect_suf h1, .inr (.inl rfl)⟩

/-- `value_end` stops where the spec's parse of the value stops. -/
theorem jlsc_valueEnd {c : Bool} {d r : Bytes} {i f dep : Nat} {j : Json} (hi : i ≤ d.length)
    (h : parseValue c f dep (d.drop i) = some (j, r)) : valueEnd d i = some (jlpEnd d r) := by
  have hs := jlsc_suf_drop d hi
  have hpi := jlp_end_drop d hi
  obtain ⟨n, hn, -, hC⟩ := (jlsc_main c d f).1 hs h
  rw [hpi] at hn hC
  have hrL : jlpEnd d r ≤ d.length := Nat.sub_le _ _
  have cont : ∀ ms its, (j = .obj ms ∨ j = .arr its) → cScan d (d.length + 1) 0 i = some (jlpEnd d r) := by
    intro ms its hj
    have := hC (by rcases hj with rfl | rfl <;> rfl) (d.length + 1 - n)
    rwa [show d.length + 1 - n + n = d.length + 1 by omega] at this
  cases f with
  | zero => rw [jls_pv_zero] at h; cases h
  | succ f =>
  unfold valueEnd
  rcases jls_pv_inv h with ⟨rest, hd, -, ⟨rfl, -⟩ | ⟨ms, rfl, -⟩⟩ | ⟨rest, hd, -, ⟨rfl, -⟩ | ⟨it, rfl, -⟩⟩ |
      ⟨rest, st, hd, rfl, hst⟩ | ⟨b, tl, hd, -, -, -, hdg, hn'⟩ | ⟨b, tl, hd, -, -, -, hdg, hl⟩ <;>
    obtain ⟨hlt, hb, hrest⟩ := jlp_drop_cons_inv hd <;>
    rw [jlp_if_neg (show ¬ d.length ≤ i by omega)]
  · rw [hb, jlp_if_neg (by decide), jlp_if_pos (.inr rfl)]; exact cont [] [] (.inl rfl)
  · rw [hb, jlp_if_neg (by decide), jlp_if_pos (.inr rfl)]; exact cont ms [] (.inl rfl)
  · rw [hb, jlp_if_neg (by decide), jlp_if_pos (.inl rfl)]; exact cont [] [] (.inr rfl)
  · rw [hb, jlp_if_neg (by decide), jlp_if_pos (.inl rfl)]; exact cont [] it (.inr rfl)
  · rw [hb, jlp_if_pos rfl, jlp_stringEnd hlt, ← hrest, jlp_ps_true hst]; rfl
  · have hd' : 48 ≤ b ∧ b ≤ 57 := by
      unfold isDigit at hdg; rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hdg; exact hdg
    rw [hb, jlp_if_neg (by omega), jlp_if_neg (by omega), jlp_if_neg (by omega), hdg, jlp_if_pos rfl,
      jlp_numberEnd hi, hn']
    rfl
  · obtain ⟨b', tl', hd2, hb'⟩ := jlsc_lit_head hl
    rw [hd] at hd2; injection hd2 with e1; subst e1
    rw [hb, jlp_if_neg (by omega), jlp_if_neg (by omega), jlp_if_pos (by omega), jlp_literalEnd hi, hl]
    rfl

theorem jlsc_readItem {c : Bool} {d r : Bytes} {i f dep : Nat} {j : Json} (hi : i ≤ d.length)
    (h : parseValue c f dep (d.drop i) = some (j, r)) : readItem d i = some (itemTail d (jlpEnd d r)) := by
  unfold readItem; rw [jlsc_valueEnd hi h]; rfl

end C3.Json
