import C3BootProofs.Models.JsonLinkLoop

/-!
# `parseLoop` against `parseMembers` and `parseElems`

The claims below say what `parseLoop` does from a value, from an object's
members, and from an array's items, in terms of the spec's parse at the same
position. `jlm_M_succ` and `jlm_E_succ` prove the members and items claims
at one more unit of fuel from the claims at the fuel below.
-/

namespace C3.Json

open C3

set_option linter.unusedSimpArgs false

/-- `noCtlKeys` for each member's value. -/
def jlmVals : List (Bytes × Json) → Bool
  | [] => true
  | (_, j) :: ms => noCtlKeys j && jlmVals ms

theorem jlm_noCtlMembers : ∀ ms : List (Bytes × Json), noCtlMembers ms = (jlwKeysNC ms && jlmVals ms)
  | [] => rfl
  | (k, j) :: ms => by
    simp only [noCtlMembers, jlmVals, jlw_keysNC_cons, jlm_noCtlMembers ms]
    cases k.all (fun b => decide (0x20 ≤ b)) <;> cases noCtlKeys j <;> cases jlwKeysNC ms <;> cases jlmVals ms <;> rfl

/-- What `parseLoop` does from the value at `pos`, given what `parseValue`
does there. -/
def jlmV (c : Bool) (d : Bytes) (start f : Nat) : Prop :=
  ∀ {dep pos : Nat} (stk : List (Bool × Nat)), pos ≤ d.length → stk.length + dep = 16 →
    (∀ {j : Json} {r : Bytes}, parseValue c f dep (d.drop pos) = some (j, r) →
      (noCtlKeys j = true → ∃ n, n ≤ jlpEnd d r - pos ∧
        (∀ k, parseLoop c d start (k + n) stk pos =
          afterClose (closeLoop c d start 17 stk (jlpEnd d r)) (parseLoop c d start k)) ∧
        ∀ k, k < n → jlmErr (parseLoop c d start k stk pos)) ∧
      (noCtlKeys j = false → ∀ k, jlmErr (parseLoop c d start k stk pos))) ∧
    (parseValue c f dep (d.drop pos) = none → 2 * (d.length - pos) + 2 ≤ f →
      ∀ k, jlmErr (parseLoop c d start k stk pos))

/-- What `parseLoop` does from the key at `p` of the object that starts at
`st`, given what `parseMembers` does there. -/
def jlmM (c : Bool) (d : Bytes) (start f : Nat) : Prop :=
  ∀ {dep p st : Nat} (stk : List (Bool × Nat)), p ≤ d.length → stk.length + 1 + dep = 16 → st ≤ p →
    (∀ {ms : List (Bytes × Json)} {r : Bytes}, parseMembers c f dep (d.drop p) = some (ms, r) →
      (jlmVals ms = true → ∃ n, n ≤ jlpEnd d r - p ∧
        (∀ k, jlmPK c d start (k + n) (stk ++ [(true, st)]) p =
          keysThen (checkKeys c (slice d st (jlpEnd d r - st)))
            (afterClose (closeLoop c d start 17 stk (jlpEnd d r)) (parseLoop c d start k))) ∧
        ∀ k, k < n → jlmErr (jlmPK c d start k (stk ++ [(true, st)]) p)) ∧
      (jlmVals ms = false → ∀ k, jlmErr (jlmPK c d start k (stk ++ [(true, st)]) p))) ∧
    (parseMembers c f dep (d.drop p) = none → 2 * (d.length - p) + 2 ≤ f →
      ∀ k, jlmErr (jlmPK c d start k (stk ++ [(true, st)]) p))

/-- What `parseLoop` does from the item at `p` of the array that starts at
`st`, given what `parseElems` does there. -/
def jlmE (c : Bool) (d : Bytes) (start f : Nat) : Prop :=
  ∀ {dep p st : Nat} (stk : List (Bool × Nat)), p ≤ d.length → stk.length + 1 + dep = 16 →
    (∀ {js : List Json} {r : Bytes}, parseElems c f dep (d.drop p) = some (js, r) →
      (noCtlElems js = true → ∃ n, n ≤ jlpEnd d r - p ∧
        (∀ k, parseLoop c d start (k + n) (stk ++ [(false, st)]) p =
          afterClose (closeLoop c d start 17 stk (jlpEnd d r)) (parseLoop c d start k)) ∧
        ∀ k, k < n → jlmErr (parseLoop c d start k (stk ++ [(false, st)]) p)) ∧
      (noCtlElems js = false → ∀ k, jlmErr (parseLoop c d start k (stk ++ [(false, st)]) p))) ∧
    (parseElems c f dep (d.drop p) = none → 2 * (d.length - p) + 3 ≤ f →
      ∀ k, jlmErr (parseLoop c d start k (stk ++ [(false, st)]) p))

theorem jlm_split {P : Nat → Prop} (n : Nat) (h1 : ∀ k, k < n → P k) (h2 : ∀ k, P (k + n)) : ∀ k, P k :=
  fun k => if h : k < n then h1 k h else by
    have := h2 (k - n); rwa [Nat.sub_add_cancel (by omega)] at this

theorem jlm_lo {P : Nat → Prop} (n m : Nat) (h1 : ∀ k, k < n → P k) (h2 : ∀ k, k < m → P (k + n)) :
    ∀ k, k < n + m → P k :=
  fun k hk => if h : k < n then h1 k h else by
    have := h2 (k - n) (by omega); rwa [Nat.sub_add_cancel (by omega)] at this

theorem jlm_suf {d x w : Bytes} {p : Nat} (hp : p ≤ d.length) (h : d.drop p = x ++ w) :
    d.drop (jlpEnd d w) = w ∧ jlpEnd d w = p + x.length := by
  have S := jlsc_suf_drop d hp
  rw [h] at S
  obtain ⟨S1, S2⟩ := jlsc_suf_app S
  rw [← h, jlp_end_drop d hp] at S2
  exact ⟨S1.symm, S2⟩

theorem jlm_key_suf {c : Bool} {s k w : Bytes} (h : jlpKey c s = some (k, w)) : ∃ x, x ≠ [] ∧ s = x ++ w := by
  cases s with
  | nil => rw [jlp_key_nil] at h; cases h
  | cons b rest =>
    rw [jlp_key_cons] at h
    by_cases hb : b = 34
    · rw [jlp_if_pos hb] at h
      obtain ⟨⟨k', r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r2, h2, h⟩ := Option.map_eq_some_iff.mp h
      injection h with _ hw
      subst hw hb
      have hrest := jls_str_suf c h1
      have hc := jls_readExpect_suf h2
      obtain ⟨y1, hy1⟩ := jls_ws_suf c r1
      obtain ⟨y2, hy2⟩ := jls_ws_suf c r2
      refine ⟨34 :: (k' ++ 34 :: (y1 ++ 58 :: y2)), List.cons_ne_nil _ _, ?_⟩
      rw [hrest, hy1, hc]
      generalize ws c r2 = w' at hy2 ⊢
      subst hy2
      simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
    · rw [jlp_if_neg hb] at h; cases h

theorem jlm_pm_end {c : Bool} {d r : Bytes} {p f dep : Nat} {ms : List (Bytes × Json)} (hp : p ≤ d.length)
    (h : parseMembers c f dep (d.drop p) = some (ms, r)) :
    p < jlpEnd d r ∧ jlpEnd d r ≤ d.length ∧ d.drop (jlpEnd d r) = r := by
  obtain ⟨x, hx, hs⟩ := jls_pm_suf h
  obtain ⟨h1, h2⟩ := jlm_suf hp hs
  have := List.length_pos_iff.mpr hx
  exact ⟨by omega, Nat.sub_le _ _, h1⟩

theorem jlm_pe_end {c : Bool} {d r : Bytes} {p f dep : Nat} {js : List Json} (hp : p ≤ d.length)
    (h : parseElems c f dep (d.drop p) = some (js, r)) :
    p < jlpEnd d r ∧ jlpEnd d r ≤ d.length ∧ d.drop (jlpEnd d r) = r := by
  obtain ⟨x, hx, hs⟩ := jls_pe_suf h
  obtain ⟨h1, h2⟩ := jlm_suf hp hs
  have := List.length_pos_iff.mpr hx
  exact ⟨by omega, Nat.sub_le _ _, h1⟩

theorem jlm_M_succ {c : Bool} {d : Bytes} {start f : Nat} (hV : jlmV c d start f) (hM : jlmM c d start f) :
    jlmM c d start (f + 1) := by
  intro dep p st stk hp hdep hst
  have hs16 : stk.length < 16 := by omega
  cases hK : jlpKey c (d.drop p) with
  | none =>
    have hErr : ∀ k, jlmErr (jlmPK c d start k (stk ++ [(true, st)]) p) := fun k =>
      ⟨0x20, by unfold jlmPK; rw [jlp_keyEnd hp, hK]; rfl⟩
    have hnone : parseMembers c (f + 1) dep (d.drop p) = none := by rw [jlp_pm_key, hK]; rfl
    exact ⟨fun h => (by rw [hnone] at h; cases h), fun _ _ => hErr⟩
  | some kw =>
    obtain ⟨key, w⟩ := kw
    obtain ⟨x, hx, hxw⟩ := jlm_key_suf hK
    obtain ⟨hdw, hew⟩ := jlm_suf hp hxw
    have hxl : 0 < x.length := List.length_pos_iff.mpr hx
    have hpL : p < d.length := by
      have := congrArg List.length hxw
      rw [List.length_drop, List.length_append] at this
      omega
    have hwL : jlpEnd d w ≤ d.length := Nat.sub_le _ _
    have hPKv : ∀ k, jlmPK c d start k (stk ++ [(true, st)]) p =
        parseLoop c d start k (stk ++ [(true, st)]) (jlpEnd d w) := fun k => by
      unfold jlmPK; rw [jlp_keyEnd hp, hK]; rfl
    have hpm : parseMembers c (f + 1) dep (d.drop p) =
        (parseValue c f dep w).bind fun (vr : Json × Bytes) => jlsMTail c f dep key vr.1 (ws c vr.2) := by
      rw [jlp_pm_key, hK]; rfl
    have hVw := hV (stk ++ [(true, st)]) (pos := jlpEnd d w) (dep := dep) hwL
      (by rw [List.length_append, List.length_singleton]; omega)
    rw [hdw] at hVw
    cases hv : parseValue c f dep w with
    | none =>
      rw [hpm, hv]
      refine ⟨fun h => (by cases h), fun _ hf k => ?_⟩
      rw [hPKv]; exact hVw.2 hv (by omega) k
    | some vr =>
      obtain ⟨v, r3⟩ := vr
      have hpm' : parseMembers c (f + 1) dep (d.drop p) = jlsMTail c f dep key v (ws c r3) := by
        rw [hpm, hv]; rfl
      obtain ⟨-, hlt3, hle3, hd3⟩ := jlw_den hwL (by rw [hdw]; exact hv)
      have hV1 := hVw.1 hv
      have hCL := fun k => jlm_cl_obj c d start k (stk := stk) (st := st) (e := jlpEnd d r3) (t := ws c r3) hs16
        (by rw [hd3]) (by omega)
      rw [hpm']
      cases hnc : noCtlKeys v with
      | false =>
        have hErr : ∀ k, jlmErr (jlmPK c d start k (stk ++ [(true, st)]) p) := fun k => by
          rw [hPKv]; exact hV1.2 hnc k
        refine ⟨fun hm => ⟨fun hvals => ?_, fun _ => hErr⟩, fun _ _ => hErr⟩
        exfalso
        rcases jls_mt_inv hm with ⟨_, more, _, _, rfl⟩ | ⟨_, rfl⟩
        · simp only [jlmVals, hnc, Bool.false_and] at hvals; cases hvals
        · simp only [jlmVals, hnc, Bool.false_and] at hvals; cases hvals
      | true =>
        obtain ⟨nv, hnv, hEq, hlo⟩ := hV1.1 hnc
        have hPKn : ∀ k, jlmPK c d start (k + nv) (stk ++ [(true, st)]) p =
            afterClose (closeLoop c d start 17 (stk ++ [(true, st)]) (jlpEnd d r3)) (parseLoop c d start k) :=
          fun k => by rw [hPKv, hEq]
        have hPKlo : ∀ k, k < nv → jlmErr (jlmPK c d start k (stk ++ [(true, st)]) p) := fun k hk => by
          rw [hPKv]; exact hlo k hk
        cases ht : ws c r3 with
        | nil =>
          have hmt : jlsMTail c f dep key v [] = none := rfl
          rw [hmt]
          refine ⟨fun h => (by cases h), fun _ _ => jlm_split nv hPKlo fun k => ?_⟩
          rw [hPKn]
          exact (hCL k).2.2 (fun s' h => by rw [ht] at h; cases h) (fun r h => by rw [ht] at h; cases h)
        | cons b s' =>
          by_cases b44 : b = 44
          · subst b44
            have hA := fun k => (hCL k).1 s' ht
            obtain ⟨-, hd2, hlt2⟩ := hA 0
            have hp2L : jlpEnd d (ws c s') ≤ d.length := Nat.sub_le _ _
            have IH := hM stk (p := jlpEnd d (ws c s')) (st := st) (dep := dep) hp2L hdep (by omega)
            rw [hd2] at IH
            have hmt : jlsMTail c f dep key v (44 :: s') =
                (parseMembers c f dep (ws c s')).bind fun (mr : List (Bytes × Json) × Bytes) =>
                  some ((key, v) :: mr.1, mr.2) := rfl
            rw [hmt]
            cases hm2 : parseMembers c f dep (ws c s') with
            | none =>
              refine ⟨fun h => (by cases h), fun _ _ => jlm_split nv hPKlo fun k => ?_⟩
              rw [hPKn, (hA k).1]
              exact IH.2 hm2 (by omega) k
            | some mr =>
              obtain ⟨more, r⟩ := mr
              refine ⟨fun h => ?_, fun h => (by cases h)⟩
              injection h with h; injection h with hms hr; subst hms hr
              dsimp only
              obtain ⟨hIa, hIb⟩ := IH.1 hm2
              have hval : jlmVals ((key, v) :: more) = jlmVals more := by
                simp only [jlmVals, hnc, Bool.true_and]
              rw [hval]
              obtain ⟨hltE, hleE, -⟩ := jlm_pm_end hp2L (by rw [hd2]; exact hm2)
              refine ⟨fun hvals => ?_, fun hvals => ?_⟩
              · obtain ⟨n2, hn2, hEq2, hlo2⟩ := hIa hvals
                refine ⟨nv + n2, by omega, fun k => ?_, jlm_lo nv n2 hPKlo fun k hk => ?_⟩
                · rw [show k + (nv + n2) = (k + n2) + nv by omega, hPKn, (hA (k + n2)).1, hEq2]
                · rw [hPKn, (hA k).1]; exact hlo2 k hk
              · exact jlm_split nv hPKlo fun k => by rw [hPKn, (hA k).1]; exact hIb hvals k
          · by_cases b125 : b = 125
            · subst b125
              have hmt : jlsMTail c f dep key v (125 :: s') = some ([(key, v)], s') := rfl
              rw [hmt]
              refine ⟨fun h => ?_, fun h => (by cases h)⟩
              injection h with h; injection h with hms hr; subst hms hr
              obtain ⟨-, -, hlt2⟩ := (hCL 0).2.1 _ ht
              refine ⟨fun _ => ⟨nv, by omega, fun k => ?_, hPKlo⟩, fun hvals => ?_⟩
              · rw [hPKn, ((hCL k).2.1 _ ht).1]
              · simp only [jlmVals, hnc, Bool.true_and] at hvals; cases hvals
            · have hmt : jlsMTail c f dep key v (b :: s') = none := by
                unfold jlsMTail; split
                · rename_i h; injection h with h; exact absurd h b44
                · rename_i h; injection h with h; exact absurd h b125
                · rfl
              rw [hmt]
              refine ⟨fun h => (by cases h), fun _ _ => jlm_split nv hPKlo fun k => ?_⟩
              rw [hPKn]
              exact (hCL k).2.2 (fun s'' h => b44 (List.cons.inj (ht.symm.trans h)).1)
                (fun r h => b125 (List.cons.inj (ht.symm.trans h)).1)

theorem jlm_E_succ {c : Bool} {d : Bytes} {start f : Nat} (hV : jlmV c d start f) (hE : jlmE c d start f) :
    jlmE c d start (f + 1) := by
  intro dep p st stk hp hdep
  have hs16 : stk.length < 16 := by omega
  have hVp := hV (stk ++ [(false, st)]) (pos := p) (dep := dep) hp
    (by rw [List.length_append, List.length_singleton]; omega)
  rw [jls_pe_eq]
  cases hv : parseValue c f dep (d.drop p) with
  | none =>
    refine ⟨fun h => (by cases h), fun _ hf k => hVp.2 hv (by omega) k⟩
  | some vr =>
    obtain ⟨v, r1⟩ := vr
    show (∀ {js r}, jlsETail c f dep v (ws c r1) = some (js, r) → _) ∧ (jlsETail c f dep v (ws c r1) = none → _)
    obtain ⟨-, hlt1, hle1, hd1⟩ := jlw_den hp hv
    have hV1 := hVp.1 hv
    have hCL := fun k => jlm_cl_arr c d start k (stk := stk) (st := st) (e := jlpEnd d r1) (t := ws c r1) hs16
      (by rw [hd1])
    cases hnc : noCtlKeys v with
    | false =>
      have hErr := hV1.2 hnc
      refine ⟨fun hm => ⟨fun hvals => ?_, fun _ => hErr⟩, fun _ _ => hErr⟩
      exfalso
      rcases jls_et_inv hm with ⟨_, more, _, _, rfl⟩ | ⟨_, rfl⟩
      · simp only [noCtlElems, hnc, Bool.false_and] at hvals; cases hvals
      · simp only [noCtlElems, hnc, Bool.false_and] at hvals; cases hvals
    | true =>
      obtain ⟨nv, hnv, hEq, hlo⟩ := hV1.1 hnc
      cases ht : ws c r1 with
      | nil =>
        have het : jlsETail c f dep v [] = none := rfl
        rw [het]
        refine ⟨fun h => (by cases h), fun _ _ => jlm_split nv hlo fun k => ?_⟩
        rw [hEq]
        exact (hCL k).2.2 (fun s' h => by rw [ht] at h; cases h) (fun r h => by rw [ht] at h; cases h)
      | cons b s' =>
        by_cases b44 : b = 44
        · subst b44
          have hA := fun k => (hCL k).1 s' ht
          obtain ⟨-, hd2, hlt2⟩ := hA 0
          have hp2L : jlpEnd d (ws c s') ≤ d.length := Nat.sub_le _ _
          have IH := hE stk (p := jlpEnd d (ws c s')) (st := st) (dep := dep) hp2L hdep
          rw [hd2] at IH
          have het : jlsETail c f dep v (44 :: s') =
              (parseElems c f dep (ws c s')).bind fun (mr : List Json × Bytes) => some (v :: mr.1, mr.2) := rfl
          rw [het]
          cases hm2 : parseElems c f dep (ws c s') with
          | none =>
            refine ⟨fun h => (by cases h), fun _ _ => jlm_split nv hlo fun k => ?_⟩
            rw [hEq, (hA k).1]
            exact IH.2 hm2 (by omega) k
          | some mr =>
            obtain ⟨more, r⟩ := mr
            refine ⟨fun h => ?_, fun h => (by cases h)⟩
            injection h with h; injection h with hms hr; subst hms hr
            dsimp only
            obtain ⟨hIa, hIb⟩ := IH.1 hm2
            have hval : noCtlElems (v :: more) = noCtlElems more := by
              simp only [noCtlElems, hnc, Bool.true_and]
            rw [hval]
            obtain ⟨hltE, hleE, -⟩ := jlm_pe_end hp2L (by rw [hd2]; exact hm2)
            refine ⟨fun hvals => ?_, fun hvals => ?_⟩
            · obtain ⟨n2, hn2, hEq2, hlo2⟩ := hIa hvals
              refine ⟨nv + n2, by omega, fun k => ?_, jlm_lo nv n2 hlo fun k hk => ?_⟩
              · rw [show k + (nv + n2) = (k + n2) + nv by omega, hEq, (hA (k + n2)).1, hEq2]
              · rw [hEq, (hA k).1]; exact hlo2 k hk
            · exact jlm_split nv hlo fun k => by rw [hEq, (hA k).1]; exact hIb hvals k
        · by_cases b93 : b = 93
          · subst b93
            have het : jlsETail c f dep v (93 :: s') = some ([v], s') := rfl
            rw [het]
            refine ⟨fun h => ?_, fun h => (by cases h)⟩
            injection h with h; injection h with hms hr; subst hms hr
            obtain ⟨-, -, hlt2⟩ := (hCL 0).2.1 _ ht
            refine ⟨fun _ => ⟨nv, by omega, fun k => ?_, hlo⟩, fun hvals => ?_⟩
            · rw [hEq, ((hCL k).2.1 _ ht).1]
            · simp only [noCtlElems, hnc, Bool.true_and] at hvals; cases hvals
          · have het : jlsETail c f dep v (b :: s') = none := by
              unfold jlsETail; split
              · rename_i h; injection h with h; exact absurd h b44
              · rename_i h; injection h with h; exact absurd h b93
              · rfl
            rw [het]
            refine ⟨fun h => (by cases h), fun _ _ => jlm_split nv hlo fun k => ?_⟩
            rw [hEq]
            exact (hCL k).2.2 (fun s'' h => b44 (List.cons.inj (ht.symm.trans h)).1)
              (fun r h => b93 (List.cons.inj (ht.symm.trans h)).1)

end C3.Json
