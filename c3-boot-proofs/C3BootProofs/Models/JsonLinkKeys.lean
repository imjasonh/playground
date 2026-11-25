import C3BootProofs.Models.JsonLinkWalk

/-!
# `check_keys` against `keysOk`

On an object that the lax grammar reads, `checkKeys` accepts exactly when no key
has a byte below `0x20` and the keys pass `keysOk` (`jlk_check`). A key with
such a byte stops `nextMember`, so `check_keys` rejects the object.
-/

namespace C3.Json

open C3

set_option linter.unusedSimpArgs false

/-- `k` has no byte below `0x20`. -/
abbrev jlkNC (k : Bytes) : Bool := k.all fun b => decide (0x20 ≤ b)

/-- `nextMember` from `pos` reads the keys of `ms`, then fails. -/
def jlkTo (d : Bytes) : Nat → List (Bytes × Json) → Prop
  | pos, [] => nextMember d pos = none
  | pos, (k, _) :: ms => ∃ kp vp vl a, nextMember d pos = some (some (kp, k.length, vp, vl, a)) ∧
      slice d kp k.length = k ∧ jlkTo d a ms

theorem jlk_to_len {d : Bytes} : ∀ {p : Nat} {ms : List (Bytes × Json)}, jlkTo d p ms → p ≤ d.length →
    p + ms.length ≤ d.length
  | p, [], _, hp => hp
  | p, (k, j) :: ms, h, _ => by
    simp only [jlkTo] at h
    obtain ⟨kp, vp, vl, a, hn, -, hm⟩ := h
    have h1 := nextMember_lt hn
    have h2 := jlk_to_len hm h1.2.2.2.1
    simp only [List.length_cons]; omega

theorem jlk_keysNC_tail {k : Bytes} {v : Json} {ms : List (Bytes × Json)} (hk : jlkNC k = true)
    (h : jlwKeysNC ((k, v) :: ms) = false) : jlwKeysNC ms = false := by
  rw [jlw_keysNC_cons, show (k.all fun b => decide (0x20 ≤ b)) = true from hk, Bool.true_and] at h; exact h

/-- `nextMember` walks the members up to the first key with a control byte. -/
theorem jlk_to (c : Bool) (d : Bytes) : ∀ f {dep p : Nat} {ms : List (Bytes × Json)} {r : Bytes},
    p ≤ d.length → jlxMembers c f dep (d.drop p) = some (ms, r) → jlwKeysNC ms = false →
      jlkTo d p (ms.takeWhile fun m => jlkNC m.1)
  | 0, _, _, _, _, _, h, _ => by rw [jls_pm_zero] at h; cases h
  | f + 1, dep, p, ms, r, hp, h, hn => by
    obtain ⟨rest, k, r1, r2, v, r3, hs, hk, hc, hv, ht⟩ := jls_pm_inv h
    obtain ⟨hnm, hsl, -, hle, hd3, -⟩ := jlw_mstep hp hs hk hc hv
    by_cases hk32 : jlkNC k = true
    · rw [jlp_if_pos hk32] at hnm
      rcases jls_mt_inv ht with ⟨s', more, hw3, hm, rfl⟩ | ⟨hw3, rfl⟩
      · have hq := jlw_skip (d := d) (i := jlpEnd d r3) (by rw [hd3]; exact hw3) rfl
        obtain ⟨hqL, hqb, hqs⟩ := jlp_drop_cons_inv hq
        have hit : itemTail d (jlpEnd d r3) = (jlpEnd d r3, skipWs d (skipWs d (jlpEnd d r3) + 1)) := by
          unfold itemTail; rw [jlp_if_pos ⟨hqL, hqb⟩]
        obtain ⟨t4, ht4⟩ := jlw_pm_head hm
        have ha := jlw_skip (d := d) (i := skipWs d (jlpEnd d r3) + 1) (by rw [← hqs]; exact ht4) rfl
        have IH := jlk_to c d f (p := skipWs d (skipWs d (jlpEnd d r3) + 1)) (jlw_skip_le (by omega))
          (by rw [ha, ← ht4]; exact hm) (jlk_keysNC_tail hk32 hn)
        rw [List.takeWhile_cons_of_pos (p := fun m : Bytes × Json => jlkNC m.1) (a := (k, v)) hk32]
        simp only [jlkTo]
        exact ⟨_, _, _, _, by rw [hnm, hit], hsl, IH⟩
      · rw [jlw_keysNC_cons, show (k.all fun b => decide (0x20 ≤ b)) = true from hk32] at hn; cases hn
    · have hk32' : jlkNC k = false := Bool.eq_false_iff.mpr hk32
      rw [jlp_if_neg hk32] at hnm
      have hms : ∃ more, ms = (k, v) :: more := by
        rcases jls_mt_inv ht with ⟨_, more, _, _, rfl⟩ | ⟨_, rfl⟩
        · exact ⟨more, rfl⟩
        · exact ⟨[], rfl⟩
      obtain ⟨more, rfl⟩ := hms
      rw [List.takeWhile_cons_of_neg (p := fun m : Bytes × Json => jlkNC m.1) (a := (k, v)) (by rw [hk32']; decide)]
      exact hnm

theorem jlk_canon_from {c : Bool} {o : Bytes} : ∀ {p : Nat} {ms : List (Bytes × Json)}, MembersFromX c o p ms →
    ∀ k prev, ms.length < k →
      keysCanon o k prev p = if keysIncreasing (prev.toList ++ ms.map (·.1)) then .ok () else .error 0x20
  | p, [], h, k + 1, prev, _ => by
    simp only [MembersFromX] at h
    simp only [keysCanon, h]
    cases prev <;> rfl
  | p, (k0, j0) :: ms, h, k + 1, prev, hk => by
    simp only [MembersFromX] at h
    obtain ⟨kp, vp, vl, a, hn, hsl, -, hm⟩ := h
    have IH := jlk_canon_from hm k (some k0) (by simp only [List.length_cons] at hk; omega)
    simp only [keysCanon, hn]
    rw [hsl]
    cases prev with
    | none => exact IH
    | some pk =>
      show (if bytesLt pk k0 = true then keysCanon o k (some k0) a else .error 0x20) =
        if (bytesLt pk k0 && keysIncreasing ([k0] ++ ms.map (·.1))) = true then .ok () else .error 0x20
      rw [IH]
      cases bytesLt pk k0 <;> rfl

theorem jlk_dec_ne (k1 key : Bytes) : decide (k1 ≠ key) = !(key == k1) := by
  cases h : key == k1
  · have hne : k1 ≠ key := fun e => by rw [e, beq_iff_eq.mpr rfl] at h; cases h
    rw [decide_eq_true hne]; rfl
  · rw [beq_iff_eq.mp h]; exact decide_eq_false fun e => e rfl

theorem jlk_unique {c : Bool} {o : Bytes} (key : Bytes) : ∀ {p : Nat} {ms : List (Bytes × Json)},
    MembersFromX c o p ms → ∀ k u, ms.length < k →
      keysUnique o key k u p = .ok (u && !(ms.map (·.1)).contains key)
  | p, [], h, k + 1, u, _ => by
    simp only [MembersFromX] at h
    simp only [keysUnique, h]
    cases u <;> rfl
  | p, (k1, j1) :: ms, h, k + 1, u, hk => by
    simp only [MembersFromX] at h
    obtain ⟨kp, vp, vl, a, hn, hsl, -, hm⟩ := h
    have IH := jlk_unique key hm k (u && decide (k1 ≠ key)) (by simp only [List.length_cons] at hk; omega)
    simp only [keysUnique, hn]
    rw [hsl, IH, jlk_dec_ne]
    rw [List.map_cons, List.contains_cons]
    cases u <;> cases key == k1 <;> rfl

theorem jlk_strict_from {c : Bool} {o : Bytes} : ∀ {p : Nat} {ms : List (Bytes × Json)}, MembersFromX c o p ms →
    ∀ k, ms.length < k → keysStrict o k p = if distinct (ms.map (·.1)) then .ok () else .error 0x20
  | p, [], h, k + 1, _ => by
    simp only [MembersFromX] at h
    simp only [keysStrict, h]; rfl
  | p, (k0, j0) :: ms, h, k + 1, hk => by
    simp only [MembersFromX] at h
    obtain ⟨kp, vp, vl, a, hn, hsl, -, hm⟩ := h
    have IH := jlk_strict_from hm k (by simp only [List.length_cons] at hk; omega)
    have hL := jlw_mf_len hm
    have hU := jlk_unique k0 hm (o.length + 1) true (by omega)
    simp only [keysStrict, hn]
    rw [hsl, hU]
    show (if (true && !(ms.map (·.1)).contains k0) = true then keysStrict o k a else .error 0x20) =
      if (!(ms.map (·.1)).contains k0 && distinct (ms.map (·.1))) = true then .ok () else .error 0x20
    rw [IH]
    cases (ms.map (·.1)).contains k0 <;> rfl

theorem jlk_canon_to {o : Bytes} : ∀ {p : Nat} {ms : List (Bytes × Json)}, jlkTo o p ms →
    ∀ k prev, ms.length < k → ∃ e, keysCanon o k prev p = .error e
  | p, [], h, k + 1, prev, _ => by
    simp only [jlkTo] at h
    exact ⟨0x20, by simp only [keysCanon, h]⟩
  | p, (k0, j0) :: ms, h, k + 1, prev, hk => by
    simp only [jlkTo] at h
    obtain ⟨kp, vp, vl, a, hn, -, hm⟩ := h
    have IH := jlk_canon_to hm k (some (slice o kp k0.length)) (by simp only [List.length_cons] at hk; omega)
    simp only [keysCanon, hn]
    cases prev with
    | none => exact IH
    | some pk =>
      show ∃ e, (if bytesLt pk (slice o kp k0.length) = true then
        keysCanon o k (some (slice o kp k0.length)) a else .error 0x20) = .error e
      cases bytesLt pk (slice o kp k0.length)
      · exact ⟨0x20, rfl⟩
      · exact IH

theorem jlk_strict_to {o : Bytes} : ∀ {p : Nat} {ms : List (Bytes × Json)}, jlkTo o p ms →
    ∀ k, ms.length < k → ∃ e, keysStrict o k p = .error e
  | p, [], h, k + 1, _ => by
    simp only [jlkTo] at h
    exact ⟨0x20, by simp only [keysStrict, h]⟩
  | p, (k0, j0) :: ms, h, k + 1, hk => by
    simp only [jlkTo] at h
    obtain ⟨kp, vp, vl, a, hn, -, hm⟩ := h
    have IH := jlk_strict_to hm k (by simp only [List.length_cons] at hk; omega)
    simp only [keysStrict, hn]
    cases keysUnique o (slice o kp k0.length) (o.length + 1) true a with
    | error e => exact ⟨e, rfl⟩
    | ok u =>
      show ∃ e, (if u = true then keysStrict o k a else .error 0x20) = .error e
      cases u
      · exact ⟨0x20, rfl⟩
      · exact IH

/-- `checkKeys` on an object that the spec reads, with members `ms`. -/
theorem jlk_check {c : Bool} {rest : Bytes} {f dep : Nat} {ms : List (Bytes × Json)}
    (h : (ms = [] ∧ ws c rest = [125]) ∨ jlxMembers c f dep (ws c rest) = some (ms, [])) :
    ((jlwKeysNC ms && keysOk c (ms.map (·.1))) = true → checkKeys c (123 :: rest) = .ok ()) ∧
      ((jlwKeysNC ms && keysOk c (ms.map (·.1))) = false → ∃ e, checkKeys c (123 :: rest) = .error e) := by
  have hck : checkKeys c (123 :: rest) = if c then keysCanon (123 :: rest) ((123 :: rest).length + 1) none
      (skipWs (123 :: rest) 1) else keysStrict (123 :: rest) ((123 :: rest).length + 1) (skipWs (123 :: rest) 1) := by
    unfold checkKeys
    rw [jlp_if_neg (fun h' => by rcases h' with h' | h'; exact Nat.succ_ne_zero _ h'; exact h' rfl)]
  have h1 : 1 ≤ (123 :: rest).length := Nat.succ_le_succ (Nat.zero_le _)
  rcases h with ⟨rfl, hw⟩ | hm
  · have hq := jlw_skip (d := 123 :: rest) (i := 1) hw rfl
    obtain ⟨hqL, hqb, -⟩ := jlp_drop_cons_inv hq
    have hend : MembersFromX c (123 :: rest) (skipWs (123 :: rest) 1) [] := by
      simp only [MembersFromX]; unfold nextMember; rw [jlp_if_pos ⟨hqL, hqb⟩]
    refine ⟨fun _ => ?_, fun h' => (by cases c <;> cases h')⟩
    rw [hck]
    cases c
    · rw [jlk_strict_from hend _ (by simp only [List.length_nil]; omega)]; rfl
    · rw [jlk_canon_from hend _ none (by simp only [List.length_nil]; omega)]; rfl
  · obtain ⟨t, ht⟩ := jlw_pm_head hm
    have hq := jlw_skip (d := 123 :: rest) (i := 1) ht rfl
    have hm' : jlxMembers c f dep ((123 :: rest).drop (skipWs (123 :: rest) 1)) = some (ms, []) := by
      rw [hq, ← ht]; exact hm
    have hp := jlw_skip_le h1
    cases hnc : jlwKeysNC ms
    · have W := jlk_to c _ f hp hm' hnc
      have hl := jlk_to_len W hp
      have hl' : (ms.takeWhile fun m => jlkNC m.1).length < (123 :: rest).length + 1 := by omega
      refine ⟨fun h' => (by rw [Bool.false_and] at h'; cases h'), fun _ => ?_⟩
      rw [hck]
      cases c
      · exact jlk_strict_to W _ hl'
      · exact jlk_canon_to W _ none hl'
    · have W := jlw_members c _ f hp hm' hnc
      have hl := jlw_mf_len W
      rw [Bool.true_and]
      cases c
      · rw [hck, jlp_if_neg Bool.false_ne_true, jlk_strict_from W _ (by omega)]
        refine ⟨fun h' => ?_, fun h' => ?_⟩
        · rw [jlp_if_pos (show distinct (ms.map (·.1)) = true from h')]
        · exact ⟨0x20, by rw [show distinct (ms.map (·.1)) = false from h']; rfl⟩
      · rw [hck, jlp_if_pos rfl, jlk_canon_from W _ none (by omega)]
        refine ⟨fun h' => ?_, fun h' => ?_⟩
        · rw [jlp_if_pos (show keysIncreasing ((none : Option Bytes).toList ++ ms.map (·.1)) = true from h')]
        · exact ⟨0x20, by
            rw [show keysIncreasing ((none : Option Bytes).toList ++ ms.map (·.1)) = false from h']; rfl⟩

end C3.Json
