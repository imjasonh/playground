import C3BootProofs.Models.JsonLink
import C3BootProofs.Models.JsonLinkSpec

/-!
# A slice holds one value

`parseValue` gives the same value and rest at every fuel and depth that
accept, so `JVal` names at most one value.
-/

namespace C3.Json

/-- `parseValue`, `parseMembers`, and `parseElems` agree on every fuel and
depth that accept. -/
def jluDet (c : Bool) (f : Nat) : Prop :=
  ∀ f',
    (∀ {dep dep' : Nat} {s r r' : Bytes} {j j' : Json}, parseValue c f dep s = some (j, r) →
      parseValue c f' dep' s = some (j', r') → j = j' ∧ r = r') ∧
    (∀ {dep dep' : Nat} {s r r' : Bytes} {ms ms' : List (Bytes × Json)}, parseMembers c f dep s = some (ms, r) →
      parseMembers c f' dep' s = some (ms', r') → ms = ms' ∧ r = r') ∧
    (∀ {dep dep' : Nat} {s r r' : Bytes} {js js' : List Json}, parseElems c f dep s = some (js, r) →
      parseElems c f' dep' s = some (js', r') → js = js' ∧ r = r')

theorem jlu_value {c : Bool} {f f' dep dep' : Nat} {s r r' : Bytes} {j j' : Json} (ih : jluDet c f)
    (h1 : parseValue c (f + 1) dep s = some (j, r)) (h2 : parseValue c (f' + 1) dep' s = some (j', r')) :
    j = j' ∧ r = r' := by
  rcases jls_pv_inv h1 with ⟨rest, rfl, -, h1'⟩ | ⟨rest, rfl, -, h1'⟩ | ⟨rest, st, rfl, rfl, h1'⟩ |
      ⟨b, tl, rfl, hb1, hb2, hb3, hd, h1'⟩ | ⟨b, tl, rfl, hb1, hb2, hb3, hd, h1'⟩ <;>
    rcases jls_pv_inv h2 with ⟨rest', hs, -, h2'⟩ | ⟨rest', hs, -, h2'⟩ | ⟨rest', st', hs, rfl, h2'⟩ |
      ⟨b', tl', hs, hb1', hb2', hb3', hd', h2'⟩ | ⟨b', tl', hs, hb1', hb2', hb3', hd', h2'⟩ <;>
    injection hs with hb ht
  all_goals first
    | exact absurd hb (by decide)
    | exact absurd hb.symm (by decide)
    | exact absurd hb.symm hb1'
    | exact absurd hb.symm hb2'
    | exact absurd hb.symm hb3'
    | exact absurd hb hb1
    | exact absurd hb hb2
    | exact absurd hb hb3
    | skip
  all_goals subst ht
  · rcases h1' with ⟨rfl, hw⟩ | ⟨ms, rfl, hn, hm, -⟩ <;> rcases h2' with ⟨rfl, hw'⟩ | ⟨ms', rfl, hn', hm', -⟩
    · rw [hw] at hw'; injection hw' with _ hr; exact ⟨rfl, hr⟩
    · exact absurd hw (hn' r)
    · exact absurd hw' (hn r')
    · obtain ⟨rfl, rfl⟩ := ((ih f').2.1 hm hm'); exact ⟨rfl, rfl⟩
  · rcases h1' with ⟨rfl, hw⟩ | ⟨js, rfl, hn, hm⟩ <;> rcases h2' with ⟨rfl, hw'⟩ | ⟨js', rfl, hn', hm'⟩
    · rw [hw] at hw'; injection hw' with _ hr; exact ⟨rfl, hr⟩
    · exact absurd hw (hn' r)
    · exact absurd hw' (hn r')
    · obtain ⟨rfl, rfl⟩ := ((ih f').2.2 hm hm'); exact ⟨rfl, rfl⟩
  · rw [h1'] at h2'; cases h2'; exact ⟨rfl, rfl⟩
  · subst hb; rw [h1'] at h2'; cases h2'; exact ⟨rfl, rfl⟩
  · subst hb; rw [hd] at hd'; cases hd'
  · subst hb; rw [hd] at hd'; cases hd'
  · subst hb; rw [h1'] at h2'; cases h2'; exact ⟨rfl, rfl⟩

theorem jlu_members {c : Bool} {f f' dep dep' : Nat} {s r r' : Bytes} {ms ms' : List (Bytes × Json)}
    (ih : jluDet c f) (h1 : parseMembers c (f + 1) dep s = some (ms, r))
    (h2 : parseMembers c (f' + 1) dep' s = some (ms', r')) : ms = ms' ∧ r = r' := by
  obtain ⟨rest, k, r1, r2, v, r3, rfl, hk, hc, hv, ht⟩ := jls_pm_inv h1
  obtain ⟨rest', k', r1', r2', v', r3', hs, hk', hc', hv', ht'⟩ := jls_pm_inv h2
  injection hs with _ hs; subst hs
  rw [hk] at hk'; cases hk'
  rw [hc] at hc'; cases hc'
  obtain ⟨rfl, rfl⟩ := (ih f').1 hv hv'
  rcases jls_mt_inv ht with ⟨s', more, hs1, hm, rfl⟩ | ⟨hs1, rfl⟩ <;>
    rcases jls_mt_inv ht' with ⟨s'', more', hs2, hm', rfl⟩ | ⟨hs2, rfl⟩ <;> rw [hs1] at hs2 <;>
    injection hs2 with hb hs2
  · subst hs2; obtain ⟨rfl, rfl⟩ := (ih f').2.1 hm hm'; exact ⟨rfl, rfl⟩
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · exact ⟨rfl, hs2⟩

theorem jlu_elems {c : Bool} {f f' dep dep' : Nat} {s r r' : Bytes} {js js' : List Json}
    (ih : jluDet c f) (h1 : parseElems c (f + 1) dep s = some (js, r))
    (h2 : parseElems c (f' + 1) dep' s = some (js', r')) : js = js' ∧ r = r' := by
  obtain ⟨v, r1, hv, ht⟩ := jls_pe_inv h1
  obtain ⟨v', r1', hv', ht'⟩ := jls_pe_inv h2
  obtain ⟨rfl, rfl⟩ := (ih f').1 hv hv'
  rcases jls_et_inv ht with ⟨s', more, hs1, hm, rfl⟩ | ⟨hs1, rfl⟩ <;>
    rcases jls_et_inv ht' with ⟨s'', more', hs2, hm', rfl⟩ | ⟨hs2, rfl⟩ <;> rw [hs1] at hs2 <;>
    injection hs2 with hb hs2
  · subst hs2; obtain ⟨rfl, rfl⟩ := (ih f').2.2 hm hm'; exact ⟨rfl, rfl⟩
  · exact absurd hb (by decide)
  · exact absurd hb (by decide)
  · exact ⟨rfl, hs2⟩

theorem jlu_det (c : Bool) : ∀ f, jluDet c f
  | 0 => fun _ => ⟨fun h => (by rw [jls_pv_zero] at h; cases h), fun h => (by rw [jls_pm_zero] at h; cases h),
      fun h => (by rw [jls_pe_zero] at h; cases h)⟩
  | f + 1 => fun f' => by
    cases f' with
    | zero =>
      exact ⟨fun _ h => (by rw [jls_pv_zero] at h; cases h), fun _ h => (by rw [jls_pm_zero] at h; cases h),
        fun _ h => (by rw [jls_pe_zero] at h; cases h)⟩
    | succ f' =>
      have ih := jlu_det c f
      exact ⟨fun h1 h2 => jlu_value ih h1 h2, fun h1 h2 => jlu_members ih h1 h2, fun h1 h2 => jlu_elems ih h1 h2⟩

theorem JValUnique : JValUniqueStmt := fun c _ _ _ ⟨f, _, h⟩ ⟨f', _, h'⟩ => ((jlu_det c f f').1 h h').1

end C3.Json
