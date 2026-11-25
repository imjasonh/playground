import C3BootProofs.Models.TufLinkKeys
import C3BootProofs.Proofs.TufRoleKeysMetModel

/-!
# `RoleKeys::met` against `Spec/Tuf.lean`

`metLookup_spec` shows that the compiled search through the signatures
array finds `List.lookup` of the signatures that `parseMeta` reads.
`metOf_of_sound` shows that `MetSound`, the result of `Ok(true)`, gives
`metOf`, the spec's count of the keys that signed.
-/

namespace C3.Json

open C3.RV32 (Word)

theorem tlmt_pair {s : Json} {k g : Bytes} (h : sigPair s = some (k, g)) :
    (s.field (ascii!"keyid") >>= Json.asStr) = some k ∧ (s.field (ascii!"sig") >>= Json.asStr) = some g := by
  unfold sigPair at h
  rcases hk : (s.field (ascii!"keyid") >>= Json.asStr) with _ | k'
  · rw [hk] at h; cases h
  rw [hk] at h
  rcases hg : (s.field (ascii!"sig") >>= Json.asStr) with _ | g'
  · rw [hg] at h; cases h
  rw [hg] at h; cases h; exact ⟨rfl, rfl⟩

theorem tlmt_beq {a b : Bytes} : (a == b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [decide_eq_true rfl]; exact beq_iff_eq.mpr rfl
  · rw [decide_eq_false h]; exact tlk_bfalse h

/-- The search over the items `js` from `pos` finds the first signature
for `id`. -/
theorem tlmt_sig {a id : Bytes} : ∀ (js : List Json) (ps : List (Bytes × Bytes)) (pos fuel : Nat),
    ElementsFrom true a pos js → js.length < fuel → js.mapM sigPair = some ps →
    metSig a id fuel pos = some (ps.lookup id)
  | _, _, _, 0, _, hf, _ => absurd hf (Nat.not_lt_zero _)
  | [], ps, pos, k + 1, he, _, hm => by
    rw [List.mapM_nil] at hm; cases hm
    unfold ElementsFrom at he
    unfold metSig; rw [he]; rfl
  | s :: js, ps, pos, k + 1, he, hfu, hm => by
    rw [List.mapM_cons] at hm
    rcases hp : sigPair s with _ | ⟨kid, g⟩
    · rw [hp] at hm; cases hm
    rw [hp] at hm
    rcases hq : js.mapM sigPair with _ | qs
    · rw [hq] at hm; cases hm
    rw [hq] at hm; cases hm
    obtain ⟨hk1, hg1⟩ := tlmt_pair hp
    obtain ⟨l, nx, hne, hd, hel⟩ := he
    unfold metSig; rw [hne]; simp only
    have hf := ObjField true (slice a pos l) s (ascii!"keyid") hd.2
    rcases hk : s.field (ascii!"keyid") with _ | jk
    · rw [hk] at hk1; cases hk1
    rw [hk] at hf hk1; simp only at hf
    obtain ⟨kp, kl, ho, hd'⟩ := hf
    rw [ho]; simp only
    rw [tl_strBody hd'.2, show jk.asStr = some kid from hk1]
    simp only
    rw [List.lookup_cons]
    by_cases heq : kid = id
    · rw [if_pos heq]
      subst heq
      rw [show (kid == kid) = true from beq_iff_eq.mpr rfl]
      have hg := ObjField true (slice a pos l) s (ascii!"sig") hd.2
      rcases hk2 : s.field (ascii!"sig") with _ | jg
      · rw [hk2] at hg1; cases hg1
      rw [hk2] at hg hg1; simp only at hg
      obtain ⟨gp, gl, hgo, hgd⟩ := hg
      rw [hgo]; simp only
      rw [tl_strBody hgd.2, show jg.asStr = some g from hg1]; rfl
    · rw [if_neg heq, show (id == kid) = false from tlk_bfalse (Ne.symm heq)]
      simp only
      exact tlmt_sig js qs nx k hel (by simp only [List.length_cons] at hfu; omega) hq

/-- The compiled search finds the first signature for `id` among the pairs
that `parseMeta` reads from the signatures array `a`. -/
theorem metLookup_spec {a : Bytes} {sj : Json} {ps : List (Bytes × Bytes)} (h : JVal true a sj)
    (hp : (sj.asArr >>= List.mapM sigPair) = some ps) (id : Bytes) : metLookup a id = some (ps.lookup id) := by
  rcases hA : sj.asArr with _ | js
  · rw [hA] at hp; cases hp
  rw [hA] at hp
  have hj := tlm_asArr hA
  subst hj
  have ho := (CurOpen true a (.arr js) 0 h).2.1
  unfold metLookup
  by_cases hc : a.length = 0 ∨ a.getD 0 0 ≠ 91
  · rw [tlm_open.mp hc] at ho; cases ho
  rw [if_neg hc]
  exact tlmt_sig js ps _ _ (Elements true a js h) (by have := tlm_arr_len h; omega) hp

theorem sigOkT_keyTag (k : TufKey) (msg sig : Bytes) : sigOkT (keyTag k) msg sig = sigValid k msg sig := by
  cases k <;> rfl

theorem keyTag_inj {k k' : TufKey} (h : keyTag k = keyTag k') : k = k' := by
  cases k <;> cases k' <;> simp only [keyTag, Prod.mk.injEq] at h <;>
    first | exact absurd h.1 (by decide) | rw [h.2]

/-- The list `l` without its first `a`. -/
def tlmtRm {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | b :: l => if b = a then l else b :: tlmtRm a l

theorem tlmtRm_len {α : Type} [DecidableEq α] (a : α) : ∀ {l : List α}, a ∈ l → (tlmtRm a l).length + 1 = l.length
  | [], h => nomatch h
  | b :: l, h => by
    unfold tlmtRm
    by_cases hb : b = a
    · rw [if_pos hb]; rfl
    rw [if_neg hb]
    rcases List.mem_cons.mp h with h | h
    · exact absurd h.symm hb
    simp only [List.length_cons]
    rw [tlmtRm_len a h]

theorem tlmtRm_mem {α : Type} [DecidableEq α] {a x : α} (hx : x ≠ a) : ∀ {l : List α}, x ∈ l → x ∈ tlmtRm a l
  | [], h => nomatch h
  | b :: l, h => by
    unfold tlmtRm
    by_cases hb : b = a
    · rw [if_pos hb]
      rcases List.mem_cons.mp h with h | h
      · exact absurd (h.trans hb) hx
      exact h
    rw [if_neg hb]
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact List.mem_cons_self
    exact List.mem_cons_of_mem _ (tlmtRm_mem hx h)

theorem tlmt_len_le {α : Type} [DecidableEq α] : ∀ {l L : List α}, l.Nodup → (∀ x ∈ l, x ∈ L) → l.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, L, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ L := hs a List.mem_cons_self
    have ht : ∀ x ∈ t, x ∈ tlmtRm a L := fun x hx =>
      tlmtRm_mem (fun e => hn.1 (by rw [← e]; exact hx)) (hs x (List.mem_cons_of_mem _ hx))
    have := tlmt_len_le hn.2 ht
    have := tlmtRm_len a ha
    simp only [List.length_cons]; omega

theorem tlmt_nodup_map {α β : Type} {f : α → β} (hf : ∀ x y, f x = f y → x = y) :
    ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun ha => h.1 (List.mem_map_of_mem ha), tlmt_nodup_map hf h.2⟩

theorem tlmt_tag_mem {id : Bytes} {k : Nat × Bytes} :
    ∀ {es : List (Bytes × Option TufKey)}, (id, some k) ∈ es.map rkTag → ∃ key, keyTag key = k ∧ (id, some key) ∈ es
  | [], h => nomatch h
  | e :: es, h => by
    rw [List.map_cons] at h
    rcases List.mem_cons.mp h with h | h
    · rcases e with ⟨i, _ | key⟩
      · cases h
      simp only [rkTag, Option.map_some, Prod.mk.injEq, Option.some.injEq] at h
      exact ⟨key, h.2.symm, by rw [h.1]; exact List.mem_cons_self⟩
    obtain ⟨key, h1, h2⟩ := tlmt_tag_mem h
    exact ⟨key, h1, List.mem_cons_of_mem _ h2⟩

/-- The key of the entry `e` when its signature in `md` checks over
`msg`, as `metOf` filters. -/
def tlmtGood (md : Meta) (msg : Bytes) (e : Bytes × Option TufKey) : Option TufKey := do
  let key ← e.2
  let sig ← md.sigs.lookup e.1
  if sigValid key msg sig then some key else none

theorem tlmt_metOf (md : Meta) (t : Nat) (es : List (Bytes × Option TufKey)) :
    metOf md t es = decide ((es.filterMap (tlmtGood md (encode md.signed))).eraseDups.length ≥ t) := rfl

/-- A key in `es` with a signature in `md` that checks over `msg` is in the
list that `metOf` counts. -/
theorem tlmt_good {md : Meta} {msg : Bytes} {id sig : Bytes} {key : TufKey} {es : List (Bytes × Option TufKey)}
    (h : (id, some key) ∈ es) (hl : md.sigs.lookup id = some sig) (hv : sigValid key msg sig = true) :
    key ∈ es.filterMap (tlmtGood md msg) := by
  refine List.mem_filterMap.mpr ⟨(id, some key), h, ?_⟩
  simp only [tlmtGood, Option.bind_eq_bind, Option.bind_some, hl, hv, ↓reduceIte]

/-- `MetSound` on the tagged entries of `es` gives `metOf`, when the search
through `a` finds the signatures of `md` and `msg` is the encoding of its
`signed` value. -/
theorem metOf_of_sound {md : Meta} {a : Bytes} {t : Nat} {es : List (Bytes × Option TufKey)}
    (hl : ∀ id, metLookup a id = some (md.sigs.lookup id)) (h : MetSound a (encode md.signed) t (es.map rkTag)) :
    metOf md t es = true := by
  obtain ⟨ks, hn, ht, hk⟩ := h
  have hsub : ∀ k ∈ ks, k ∈ (es.filterMap (tlmtGood md (encode md.signed))).eraseDups.map keyTag := by
    intro k hkm
    obtain ⟨id, sig, hm, hlk, hv⟩ := hk k hkm
    obtain ⟨key, hkt, hm'⟩ := tlmt_tag_mem hm
    rw [hl id] at hlk
    have hlk := Option.some.inj hlk
    rw [← hkt, sigOkT_keyTag] at hv
    rw [← hkt]; exact List.mem_map_of_mem (List.mem_eraseDups.mpr (tlmt_good hm' hlk hv))
  have hle := tlmt_len_le hn hsub
  rw [List.length_map] at hle
  rw [tlmt_metOf]
  exact decide_eq_true (by omega)

end C3.Json
