import C3BootProofs.Models.JsonLinkParse
import C3BootProofs.Models.JsonLinkWalk
import C3BootProofs.Models.JsonLinkValue
import C3BootProofs.Models.JsonLinkCanon
import C3BootProofs.Models.TufLink
import C3BootProofs.Proofs.TufParseRoot

/-!
# `pmModel` and `prModel` against `parseMeta` and `parseTufRoot`

`tufParseMetadata_correct` and `tufParseRoot_correct` give their results as
positions in the document. Here an `.ok` result is the spec's `Meta`, with
the positions naming its `signed` value and its `signatures` value, and an
`.error` result is the spec's `none`.
-/

namespace C3.Json

open C3.RV32 (Word curOpen)

/-- A signature's key ID and hex signature, as `parseMeta` reads them. -/
def sigPair (s : Json) : Option (Bytes × Bytes) := do
  pure (← s.field (ascii!"keyid") >>= Json.asStr, ← s.field (ascii!"sig") >>= Json.asStr)

/-- `parseMeta` after `parseJson`. -/
def metaOf (j : Json) (kind : Bytes) : Option Meta :=
  match j with
  | .obj [(k1, sigs), (k2, signed)] => do
    require (k1 == ascii!"signatures" && k2 == ascii!"signed")
    require ((signed.field (ascii!"_type") >>= Json.asStr) == some kind)
    let pairs ← (← sigs.asArr).mapM sigPair
    require (distinct (pairs.map (·.1)))
    pure ⟨signed, pairs⟩
  | _ => none

theorem tlm_meta {d kind : Bytes} {j : Json} (h : parseJson true d = some j) :
    parseMeta d kind = metaOf j kind := by
  unfold parseMeta; rw [h]; rfl

theorem tlm_meta_none {d kind : Bytes} (h : parseJson true d = none) : parseMeta d kind = none := by
  unfold parseMeta; rw [h]; rfl

/-- A key ID, as `pmLater` reads it. -/
def kidOf (s : Json) : Option Bytes := s.field (ascii!"keyid") >>= Json.asStr

theorem tlm_then {α : Type} (r : Except Nat Unit) (k : Except Nat α) :
    (pmThen r k).toOption = r.toOption.bind (fun _ => k.toOption) := by
  rcases r with e | ⟨⟩ <;> rfl

theorem tlm_open {o : Nat} {p : Word} {t : Bytes} :
    (t.length = 0 ∨ t.getD 0 0 ≠ o) ↔ curOpen o p t = none := by
  unfold curOpen
  by_cases h1 : t.length = 0
  · rw [if_pos h1]; exact ⟨fun _ => rfl, fun _ => Or.inl h1⟩
  rw [if_neg h1]
  by_cases h2 : t.getD 0 0 ≠ o
  · rw [if_pos h2]; exact ⟨fun _ => rfl, fun _ => Or.inr h2⟩
  rw [if_neg h2]
  exact ⟨fun h => (h.elim h1 h2).elim, fun h => nomatch h⟩

theorem tlm_enc_pos (j : Json) : 0 < (encode j).length := by
  cases j with
  | bool b => cases b <;> decide
  | num n => unfold encode decimal; rw [List.length_append]; simp
  | str s => simp [encode]
  | arr _ => simp [encode]
  | obj _ => simp [encode]
  | null => decide

theorem tlm_elems_len : ∀ js : List Json, js.length ≤ (encodeElems js).length
  | [] => Nat.zero_le _
  | [v] => by
    have := tlm_enc_pos v
    simp only [encodeElems, List.length_cons, List.length_nil]; omega
  | v :: w :: rest => by
    have h1 := tlm_elems_len (w :: rest)
    have h2 := tlm_enc_pos v
    simp only [encodeElems, List.length_append, List.length_cons, List.length_nil] at h1 ⊢
    omega

/-- A canonical array has fewer items than bytes. -/
theorem tlm_arr_len {a : Bytes} {js : List Json} (h : JVal true a (.arr js)) : js.length < a.length := by
  rw [CanonEncode a _ h]
  have := tlm_elems_len js
  simp only [encode, List.length_append, List.length_cons, List.length_nil]; omega

theorem tlm_kid {c : Bool} {v : Bytes} {s : Json} (h : JVal c v s) :
    (match objField v (ascii!"keyid") with
      | .error e => Except.error e
      | .ok (kp, kl) => match strBody (slice v kp kl) with
        | none => .error 0x21
        | some k2 => Except.ok k2 : Except Nat Bytes).toOption = kidOf s := by
  have hf := ObjField c v s (ascii!"keyid") h
  unfold kidOf
  rcases hk : s.field (ascii!"keyid") with _ | jk
  · rw [hk] at hf; simp only at hf; rw [hf]; rfl
  rw [hk] at hf; simp only at hf
  obtain ⟨kp, kl, ho, hd⟩ := hf
  rw [ho]; simp only
  rw [tl_strBody hd.2]
  change _ = jk.asStr
  rcases jk.asStr <;> rfl

/-- `pmLater` reads each later item's key ID and finds none equal to `kid`. -/
theorem tlm_later {a kid : Bytes} : ∀ (js : List Json) (pos fuel : Nat), ElementsFrom true a pos js →
    js.length < fuel →
    (pmLater a kid fuel pos).toOption = (js.mapM kidOf).bind (fun ks => require (!ks.contains kid))
  | _, _, 0, _, hf => absurd hf (Nat.not_lt_zero _)
  | [], pos, k + 1, he, _ => by
    unfold ElementsFrom at he
    unfold pmLater; rw [he]; rfl
  | s :: js, pos, k + 1, he, hfu => by
    obtain ⟨l, nx, hne, hd, hel⟩ := he
    unfold pmLater; rw [hne]; simp only
    have hf := ObjField true (slice a pos l) s (ascii!"keyid") hd.2
    rcases hk : s.field (ascii!"keyid") with _ | jk
    · rw [hk] at hf; simp only at hf; rw [hf]
      have hko : kidOf s = none := by unfold kidOf; rw [hk]; rfl
      rw [List.mapM_cons, hko]; rfl
    rw [hk] at hf; simp only at hf
    obtain ⟨kp, kl, ho, hd'⟩ := hf
    rw [ho]; simp only
    rw [tl_strBody hd'.2]
    rcases hs : jk.asStr with _ | k2
    · have hko : kidOf s = none := by unfold kidOf; rw [hk]; exact hs
      rw [List.mapM_cons, hko]; rfl
    have hko : kidOf s = some k2 := by unfold kidOf; rw [hk]; exact hs
    rw [List.mapM_cons, hko]
    change (if k2 = kid then Except.error 33 else pmLater a kid k nx).toOption = _
    by_cases heq : k2 = kid
    · rw [if_pos heq]
      rcases js.mapM kidOf with _ | ks
      · rfl
      show none = require (!(k2 :: ks).contains kid)
      subst heq; simp [require]
    rw [if_neg heq, tlm_later js nx k hel (by simp only [List.length_cons] at hfu; omega)]
    rcases js.mapM kidOf with _ | ks
    · rfl
    show require (!ks.contains kid) = require (!(k2 :: ks).contains kid)
    simp [Ne.symm heq]

theorem tlm_pair_kid {s : Json} {k g : Bytes} (h : sigPair s = some (k, g)) : kidOf s = some k := by
  unfold sigPair at h; unfold kidOf
  rcases hk : (s.field (ascii!"keyid") >>= Json.asStr) with _ | k'
  · rw [hk] at h; cases h
  rw [hk] at h
  rcases hg : (s.field (ascii!"sig") >>= Json.asStr) with _ | g'
  · rw [hg] at h; cases h
  rw [hg] at h; cases h; rfl

theorem tlm_kids : ∀ (js : List Json) (ps : List (Bytes × Bytes)), js.mapM sigPair = some ps →
    js.mapM kidOf = some (ps.map Prod.fst)
  | [], ps, h => by rw [List.mapM_nil] at h; cases h; rfl
  | s :: js, ps, h => by
    rw [List.mapM_cons] at h
    rcases hp : sigPair s with _ | ⟨k, g⟩
    · rw [hp] at h; cases h
    rw [hp] at h
    rcases hq : js.mapM sigPair with _ | qs
    · rw [hq] at h; cases h
    rw [hq] at h; cases h
    rw [List.mapM_cons, tlm_pair_kid hp, tlm_kids js qs hq]; rfl

theorem tlm_pair_none {s : Json} (h : kidOf s = none) : sigPair s = none := by
  show (kidOf s).bind _ = none
  rw [h]; rfl

/-- `pmSigs` reads each item's key ID and signature, and no key ID repeats. -/
theorem tlm_sigs {a : Bytes} : ∀ (js : List Json) (pos fuel : Nat), ElementsFrom true a pos js →
    js.length < fuel → js.length ≤ a.length →
    (pmSigs a fuel pos).toOption = (js.mapM sigPair).bind (fun ps => require (distinct (ps.map (·.1))))
  | _, _, 0, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | [], pos, k + 1, he, _, _ => by
    unfold ElementsFrom at he
    unfold pmSigs; rw [he]; rfl
  | s :: js, pos, k + 1, he, hfu, hA => by
    simp only [List.length_cons] at hfu hA
    obtain ⟨l, nx, hne, hd, hel⟩ := he
    unfold pmSigs; rw [hne]; simp only
    have hf := ObjField true (slice a pos l) s (ascii!"keyid") hd.2
    rcases hk : s.field (ascii!"keyid") with _ | jk
    · rw [hk] at hf; simp only at hf; rw [hf]
      have hko : kidOf s = none := by unfold kidOf; rw [hk]; rfl
      rw [List.mapM_cons, tlm_pair_none hko]; rfl
    rw [hk] at hf; simp only at hf
    obtain ⟨kp, kl, ho, hd'⟩ := hf
    rw [ho]; simp only
    rw [tl_strBody hd'.2]
    rcases hs : jk.asStr with _ | kid
    · have hko : kidOf s = none := by unfold kidOf; rw [hk]; exact hs
      rw [List.mapM_cons, tlm_pair_none hko]; rfl
    simp only
    have hg := ObjField true (slice a pos l) s (ascii!"sig") hd.2
    have hko : kidOf s = some kid := by unfold kidOf; rw [hk]; exact hs
    rcases hk2 : s.field (ascii!"sig") with _ | jg
    · rw [hk2] at hg; simp only at hg; rw [hg]
      have hp : sigPair s = none := by
        show (kidOf s).bind _ = none
        rw [hko]; show (s.field (ascii!"sig") >>= Json.asStr).bind _ = none; rw [hk2]; rfl
      rw [List.mapM_cons, hp]; rfl
    rw [hk2] at hg; simp only at hg
    obtain ⟨gp, gl, hgo, hgd⟩ := hg
    rw [hgo]; simp only
    rw [tl_strBody hgd.2]
    rcases hs2 : jg.asStr with _ | g
    · have hp : sigPair s = none := by
        show (kidOf s).bind _ = none
        rw [hko]; show (s.field (ascii!"sig") >>= Json.asStr).bind _ = none; rw [hk2]
        show jg.asStr.bind _ = none; rw [hs2]; rfl
      rw [List.mapM_cons, hp]; rfl
    have hp : sigPair s = some (kid, g) := by
      show (kidOf s).bind _ = _
      rw [hko]; show (s.field (ascii!"sig") >>= Json.asStr).bind _ = _; rw [hk2]
      show jg.asStr.bind _ = _; rw [hs2]; rfl
    simp only
    rw [tlm_then, tlm_later js nx (a.length + 1) hel (by omega), tlm_sigs js nx k hel (by omega) (by omega),
      List.mapM_cons, hp]
    rcases hq : js.mapM sigPair with _ | ps
    · generalize ((js.mapM kidOf).bind fun ks => require (!ks.contains kid)) = X
      cases X <;> rfl
    rw [tlm_kids js ps hq]
    show (require (!(ps.map Prod.fst).contains kid)).bind (fun _ => require (distinct (ps.map Prod.fst))) =
      require (distinct (kid :: ps.map Prod.fst))
    simp only [distinct]
    cases (ps.map Prod.fst).contains kid <;> cases distinct (ps.map Prod.fst) <;> rfl

theorem tlm_asArr {j : Json} {js : List Json} (h : j.asArr = some js) : j = .arr js := by
  cases j <;> cases h <;> rfl

theorem tlm_asObj {j : Json} {ms : List (Bytes × Json)} (h : j.asObj = some ms) : j = .obj ms := by
  cases j <;> cases h <;> rfl

/-- The checks on the `signatures` value. -/
theorem tlm_arr {a : Bytes} {sj : Json} (h : JVal true a sj) :
    (pmArr a).toOption = (sj.asArr >>= List.mapM sigPair).bind (fun ps => require (distinct (ps.map (·.1)))) := by
  have ho := (CurOpen true a sj 0 h).2.1
  unfold pmArr
  by_cases hc : a.length = 0 ∨ a.getD 0 0 ≠ 91
  · rw [if_pos hc]
    rw [tlm_open.mp hc] at ho
    rcases hA : sj.asArr with _ | js
    · rfl
    rw [hA] at ho; cases ho
  rw [if_neg hc]
  rcases hA : sj.asArr with _ | js
  · rcases hcu : curOpen 91 0 a with _ | _
    · exact absurd (tlm_open.mpr hcu) hc
    rw [hcu, hA] at ho; cases ho
  have hj := tlm_asArr hA
  subst hj
  have hl := tlm_arr_len h
  exact tlm_sigs js _ _ (Elements true a js h) (by omega) (by omega)

/-- The checks on `signed`, the value `v`, and on `signatures`, the value `a`. -/
theorem tlm_ty {v a kind : Bytes} {sg sj : Json} (hv : JVal true v sg) (ha : JVal true a sj) :
    (pmTy v a kind).toOption = (require ((sg.field (ascii!"_type") >>= Json.asStr) == some kind)).bind
      (fun _ => (sj.asArr >>= List.mapM sigPair).bind (fun ps => require (distinct (ps.map (·.1))))) := by
  unfold pmTy
  have hf := ObjField true v sg (ascii!"_type") hv
  rcases hk : sg.field (ascii!"_type") with _ | jt
  · rw [hk] at hf; simp only at hf; rw [hf]; rfl
  rw [hk] at hf; simp only at hf
  obtain ⟨yp, yl, ho, hd⟩ := hf
  rw [ho]; simp only
  rw [tl_strBody hd.2]
  show _ = (require (jt.asStr == some kind)).bind _
  rcases jt.asStr with _ | ty
  · rfl
  change (if ty = kind then pmArr a else .error 0x21).toOption = _
  by_cases heq : ty = kind
  · rw [if_pos heq, tlm_arr ha, heq, show (some kind == some kind) = true from (beq_iff_eq.mpr rfl : (kind == kind) = true)]
    rfl
  · rw [if_neg heq]
    have : (some ty == some kind) = false := by
      rcases h : (some ty == some kind) with _ | _
      · rfl
      have h' : (ty == kind) = true := h
      exact absurd (beq_iff_eq.mp h') heq
    rw [this]; rfl

theorem tlm_meta2 (j1 j2 : Json) (kind : Bytes) :
    metaOf (.obj [(ascii!"signatures", j1), (ascii!"signed", j2)]) kind =
      (require ((j2.field (ascii!"_type") >>= Json.asStr) == some kind)).bind (fun _ =>
        (j1.asArr >>= List.mapM sigPair).bind (fun ps =>
          (require (distinct (ps.map (·.1)))).bind (fun _ => some ⟨j2, ps⟩))) := by
  delta metaOf; dsimp only
  rw [show (ascii!"signatures" == ascii!"signatures") = true from beq_iff_eq.mpr rfl,
    show (ascii!"signed" == ascii!"signed") = true from beq_iff_eq.mpr rfl]
  rcases j1.asArr with _ | l <;> rfl

/-- The top-level object's checks, against `metaOf`. -/
theorem tlm_obj {t kind : Bytes} {j : Json} (h : JVal true t j) :
    match pmObj t kind with
    | .error _ => metaOf j kind = none
    | .ok (a, b, c, e) => ∃ md sj, metaOf j kind = some md ∧ JDen true t a b md.signed ∧
        JDen true t c e sj ∧ (sj.asArr >>= List.mapM sigPair) = some md.sigs := by
  have ho := (CurOpen true t j 0 h).1
  unfold pmObj
  by_cases hc : t.length = 0 ∨ t.getD 0 0 ≠ 123
  · rw [if_pos hc]
    rw [tlm_open.mp hc] at ho
    rcases hA : j.asObj with _ | ms
    · cases j <;> first | rfl | cases hA
    rw [hA] at ho; cases ho
  rw [if_neg hc]
  rcases hA : j.asObj with _ | ms
  · rcases hcu : curOpen 123 0 t with _ | _
    · exact absurd (tlm_open.mpr hcu) hc
    rw [hcu, hA] at ho; cases ho
  have hj := tlm_asObj hA
  subst hj
  have hm := Members true t ms h
  unfold pmMembers
  rcases ms with _ | ⟨⟨k1, j1⟩, _ | ⟨⟨k2, j2⟩, rest⟩⟩
  · unfold MembersFrom at hm; rw [hm]; rfl
  · obtain ⟨kp1, vp1, vl1, a1, hn1, -, -, hm1⟩ := hm
    unfold MembersFrom at hm1
    rw [hn1]; simp only; unfold pmTwo; rw [hm1]; rfl
  obtain ⟨kp1, vp1, vl1, a1, hn1, hs1, hd1, hm1⟩ := hm
  obtain ⟨kp2, vp2, vl2, a2, hn2, hs2, hd2, hm2⟩ := hm1
  rw [hn1]; simp only; unfold pmTwo; rw [hn2]; simp only; rw [hs1, hs2]
  by_cases hkk : k1 = ascii!"signatures" ∧ k2 = ascii!"signed"
  rotate_left
  · rw [if_neg hkk]
    show metaOf _ kind = none
    rcases rest with _ | _
    · show (require (k1 == ascii!"signatures" && k2 == ascii!"signed")).bind _ = none
      rcases hb : (k1 == ascii!"signatures" && k2 == ascii!"signed") with _ | _
      · rfl
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hb
      exact absurd hb hkk
    · rfl
  rw [if_pos hkk]
  obtain ⟨rfl, rfl⟩ := hkk
  unfold pmRest
  rcases rest with _ | ⟨⟨k3, j3⟩, rest⟩
  rotate_left
  · obtain ⟨kp3, vp3, vl3, a3, hn3, -⟩ := hm2
    rw [hn3]; rfl
  unfold MembersFrom at hm2
  rw [hm2]; simp only
  have hty := tlm_ty (kind := kind) hd2.2 hd1.2
  rw [tlm_meta2]
  revert hty
  generalize pmTy (slice t vp2 vl2) (slice t vp1 vl1) kind = r
  generalize ((j2.field (ascii!"_type") >>= Json.asStr) == some kind) = T
  generalize hP : (j1.asArr >>= List.mapM sigPair) = P
  intro hty
  rcases r with e | ⟨⟩
  · show (require T).bind _ = none
    cases T
    · rfl
    rcases P with _ | ps
    · rfl
    show (require (distinct (ps.map (·.1)))).bind _ = none
    change _ = require (distinct (ps.map (·.1))) at hty
    rcases hd : distinct (ps.map (·.1)) with _ | _
    · rw [hd]; rfl
    rw [hd] at hty; cases hty
  · cases T
    · cases hty
    rcases P with _ | ps
    · cases hty
    change _ = require (distinct (ps.map (·.1))) at hty
    rcases hd : distinct (ps.map (·.1)) with _ | _
    · rw [hd] at hty; cases hty
    refine ⟨⟨j2, ps⟩, j1, ?_, hd2, hd1, hP⟩
    show (require (distinct (ps.map (·.1)))).bind _ = _
    rw [hd]; rfl

theorem tlm_drop_take {α : Type} : ∀ (m n : Nat) (l : List α), (l.take n).drop m = (l.drop m).take (n - m)
  | 0, _, _ => rfl
  | m + 1, 0, l => by rw [Nat.zero_sub]; rfl
  | _ + 1, _ + 1, [] => by show ([] : List α) = List.take _ []; rw [List.take_nil]
  | m + 1, n + 1, _ :: xs => by
    rw [Nat.add_sub_add_right]; exact tlm_drop_take m n xs

theorem tlm_slice {d : Bytes} {tp tl a b : Nat} (h : a + b ≤ tl) :
    slice (slice d tp tl) a b = slice d (tp + a) b := by
  unfold slice
  rw [tlm_drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]

theorem tlm_den {d : Bytes} {tp tl a b : Nat} {j : Json} (ht : tp + tl ≤ d.length)
    (h : JDen true (slice d tp tl) a b j) : JDen true d (tp + a) b j := by
  obtain ⟨h1, h2⟩ := h
  have hl : (slice d tp tl).length ≤ tl := by unfold slice; simp only [List.length_take]; omega
  refine ⟨by omega, ?_⟩
  rw [← tlm_slice (d := d) (tp := tp) (tl := tl) (by omega)]; exact h2

/-- `tuf::parse_metadata` is `parseMeta`: an `.ok` result names the spec's
`signed` value and its `signatures` value, whose key IDs and signatures are
the spec's, and an `.error` result is the spec's `none`. -/
theorem pmModel_spec (d kind : Bytes) :
    match pmModel d kind with
    | .error _ => parseMeta d kind = none
    | .ok (gp, gl, sp, sl) => ∃ md sj, parseMeta d kind = some md ∧ JDen true d gp gl md.signed ∧
        JDen true d sp sl sj ∧ (sj.asArr >>= List.mapM sigPair) = some md.sigs := by
  unfold pmModel
  rcases hp : parseModel true d with e | ⟨tp, tl⟩
  · exact tlm_meta_none (ParseModelError true d e hp)
  obtain ⟨j, hj, hd⟩ := ParseModelOk true d tp tl hp
  simp only
  rw [tlm_meta hj]
  have ho := tlm_obj (kind := kind) hd.2
  revert ho
  rcases pmObj (slice d tp tl) kind with e | ⟨a, b, c, e⟩
  · exact id
  intro ⟨md, sj, h1, h2, h3, h4⟩
  exact ⟨md, sj, h1, tlm_den hd.1 h2, tlm_den hd.1 h3, h4⟩

theorem tlm_root {d : Bytes} {md : Meta} (hm : parseMeta d (ascii!"root") = some md) :
    parseTufRoot d = (md.signed.field (ascii!"version") >>= Json.asNum).bind
      (fun v => (require (v ≥ 1)).bind fun _ => some ⟨md, v⟩) := by
  unfold parseTufRoot; rw [hm]; rfl

/-- `tuf::parse_root` is `parseTufRoot`: an `.ok` result is the spec's root,
with the positions of its `signed` and `signatures` values and its version,
and an `.error` result is the spec's `none`. -/
theorem prModel_spec (d : Bytes) :
    match prModel d with
    | .error _ => parseTufRoot d = none
    | .ok (gp, gl, sp, sl, v) => ∃ r sj, parseTufRoot d = some r ∧ r.version = v ∧
        JDen true d gp gl r.md.signed ∧ JDen true d sp sl sj ∧ (sj.asArr >>= List.mapM sigPair) = some r.md.sigs := by
  have hpm := pmModel_spec d (ascii!"root")
  unfold prModel
  revert hpm
  rcases pmModel d (ascii!"root") with e | ⟨gp, gl, sp, sl⟩
  · intro h; unfold parseTufRoot; rw [h]; rfl
  intro ⟨md, sj, hm, hs, hg, hp⟩
  simp only
  rw [tlm_root hm]
  have hf := ObjField true (slice d gp gl) md.signed (ascii!"version") hs.2
  rcases hk : md.signed.field (ascii!"version") with _ | jv
  · rw [hk] at hf; simp only at hf; rw [hf]; rfl
  rw [hk] at hf; simp only at hf
  obtain ⟨vp, vl, ho, hd⟩ := hf
  rw [ho]; simp only
  rw [U64Val true _ jv hd.2]
  rw [show (some jv >>= Json.asNum) = jv.asNum from rfl]
  rcases jv.asNum with _ | v
  · rfl
  change match (if v = 0 then Except.error 0x21 else Except.ok (gp, gl, sp, sl, v)) with
    | .error _ => (require (v ≥ 1)).bind (fun _ => some (TufRoot.mk md v)) = none
    | .ok (gp, gl, sp, sl, v') => ∃ (r : TufRoot) (sj : Json),
        (require (v ≥ 1)).bind (fun _ => some (TufRoot.mk md v)) = some r ∧
        r.version = v' ∧ JDen true d gp gl r.md.signed ∧ JDen true d sp sl sj ∧
        (sj.asArr >>= List.mapM sigPair) = some r.md.sigs
  by_cases h0 : v = 0
  · rw [if_pos h0, h0]; rfl
  rw [if_neg h0]
  have h1 : decide (v ≥ 1) = true := decide_eq_true (by omega)
  refine ⟨⟨md, v⟩, sj, ?_, rfl, hs, hg, hp⟩
  show (require (decide (v ≥ 1))).bind _ = _
  rw [h1]; rfl

end C3.Json
