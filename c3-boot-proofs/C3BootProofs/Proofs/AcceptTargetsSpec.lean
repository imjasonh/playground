import C3BootProofs.Models.TufLinkMeta
import C3BootProofs.Proofs.AcceptTargetsErr

/-!
# `verifyTuf` after the roots

`verifyTuf` folds over the roots, then checks `targets.json` and
`trusted_root.json` against the last root. `act_verifyTuf` splits it there:
`actRoot` is the fold, and `actFinish` is the rest.

`act_finish` gives `actFinish`'s result from the results of the compiled
functions' models on `targets.json`: `parse_metadata`, `expires`, and the
lookups of `signed.targets["trusted_root.json"]`, its `length`, and its
`hashes.sha256`.
-/

namespace C3.Json

/-- One step of `verifyTuf`'s fold over the roots. -/
def actStep (prev : TufRoot) (doc : Bytes) : Option TufRoot := do
  let next ← parseTufRoot doc
  require (next.version == prev.version + 1)
  require (← thresholdMet next.md prev.md.signed (ascii!"root"))
  require (← thresholdMet next.md next.md.signed (ascii!"root"))
  pure next

/-- The root that `verifyTuf` checks `targets.json` against: the pinned root,
then each root that the slot carries. -/
def actRoot (pinned : Bytes) (parts : TufParts) : Option TufRoot := do
  let first ← parseTufRoot pinned
  parts.roots.foldlM (init := first) actStep

/-- `verifyTuf` after the roots, for the last root `root`. -/
def actFinish (root : TufRoot) (parts : TufParts) : Option (Nat × Nat) := do
  let rootExpires ← expires root.md
  let targets ← parseMeta parts.targets (ascii!"targets")
  require (← thresholdMet targets root.md.signed (ascii!"targets"))
  let targetsExpires ← expires targets
  let entry ← targets.signed.field (ascii!"targets") >>= Json.field (ascii!"trusted_root.json")
  let length ← entry.field (ascii!"length") >>= Json.asNum
  let digest ← entry.field (ascii!"hashes") >>= Json.field (ascii!"sha256") >>= Json.asStr
  require (length == parts.trustedRoot.length && digest == hexBytes (sha256 parts.trustedRoot))
  pure (root.version, min rootExpires targetsExpires)

theorem act_verifyTuf (pinned : Bytes) (parts : TufParts) :
    verifyTuf pinned parts = (actRoot pinned parts).bind fun root => actFinish root parts := by
  unfold verifyTuf actRoot actFinish actStep
  cases parseTufRoot pinned <;> rfl

theorem act_field_asObj (j : Json) (key : Bytes) : j.field key = j.asObj.bind (·.lookup key) := by
  cases j <;> rfl

/-- `objField` on a value succeeds only on an object with the key. -/
theorem act_objField {c : Bool} {v : Bytes} {j : Json} {key : Bytes} {p l : Nat} (hj : JVal c v j)
    (h : objField v key = .ok (p, l)) : ∃ j', j.field key = some j' ∧ JVal c (slice v p l) j' := by
  have hf := ObjField c v j key hj
  revert hf
  rcases j.field key with _ | j'
  · intro hf; rw [hf] at h; cases h
  · intro ⟨vp, vl, hf, hd⟩
    rw [hf] at h; cases h
    exact ⟨j', rfl, hd.2⟩

/-- `objGet` on a value finds a member only on an object with the key. -/
theorem act_objGet {c : Bool} {v : Bytes} {j : Json} {key : Bytes} {p l : Nat} (hj : JVal c v j)
    (h : objGet v key = .ok (some (p, l))) : ∃ j', j.field key = some j' ∧ JVal c (slice v p l) j' := by
  have hf := ObjGet c v j key hj
  rw [act_field_asObj]
  revert hf
  rcases j.asObj with _ | ms
  · intro hf; rw [hf] at h; cases h
  · simp only [Option.bind_some]
    rcases ms.lookup key with _ | j'
    · intro hf; rw [hf] at h; cases h
    · intro ⟨vp, vl, hf, hd⟩
      rw [hf] at h; cases h
      exact ⟨j', rfl, hd.2⟩

/-- **`actFinish` from the models.** With `targets.json`'s `signed` value at
`S`, the entry at `E`, and the results of the lookups as the compiled code
gets them, `actFinish` accepts. -/
theorem act_finish {root : TufRoot} {parts : TufParts} {re te gp gl sp sl p1 l1 p2 l2 p3 l3 p4 l4 p5 l5 v : Nat}
    {body : Bytes} (hre : expires root.md = some re)
    (hpm : pmModel parts.targets (ascii!"targets") = .ok (gp, gl, sp, sl))
    (hmet : ∀ md, parseMeta parts.targets (ascii!"targets") = some md →
      thresholdMet md root.md.signed (ascii!"targets") = some true)
    (hte : expiresModel (slice parts.targets gp gl) = .ok te)
    (h1 : objField (slice parts.targets gp gl) (ascii!"targets") = .ok (p1, l1))
    (h2 : objGet (slice (slice parts.targets gp gl) p1 l1) (ascii!"trusted_root.json") = .ok (some (p2, l2)))
    (h3 : objField (slice (slice (slice parts.targets gp gl) p1 l1) p2 l2) (ascii!"length") = .ok (p3, l3))
    (h4 : u64Val (slice (slice (slice (slice parts.targets gp gl) p1 l1) p2 l2) p3 l3) = some v)
    (h5 : objField (slice (slice (slice parts.targets gp gl) p1 l1) p2 l2) (ascii!"hashes") = .ok (p4, l4))
    (h6 : objField (slice (slice (slice (slice parts.targets gp gl) p1 l1) p2 l2) p4 l4) (ascii!"sha256") =
      .ok (p5, l5))
    (h7 : strBody (slice (slice (slice (slice (slice parts.targets gp gl) p1 l1) p2 l2) p4 l4) p5 l5) = some body)
    (hv : v = parts.trustedRoot.length) (hb : body = hexBytes (sha256 parts.trustedRoot)) :
    actFinish root parts = some (root.version, min re te) := by
  have hs := pmModel_spec parts.targets (ascii!"targets")
  rw [hpm] at hs
  obtain ⟨md, sj, hmd, ⟨_, hS⟩, _, _⟩ := hs
  have hex : expires md = some te := by rw [← expiresModel_spec hS, hte]; rfl
  obtain ⟨j1, hj1, hv1⟩ := act_objField hS h1
  obtain ⟨j2, hj2, hv2⟩ := act_objGet hv1 h2
  obtain ⟨j3, hj3, hv3⟩ := act_objField hv2 h3
  obtain ⟨j4, hj4, hv4⟩ := act_objField hv2 h5
  obtain ⟨j5, hj5, hv5⟩ := act_objField hv4 h6
  have hn : j3.asNum = some v := by rw [← U64Val _ _ _ hv3, h4]
  have hstr : j5.asStr = some body := by rw [← tl_strBody hv5, h7]
  unfold actFinish
  simp only [hre, hmd, hmet md hmd, hex, hj1, hj2, hj3, hj4, hj5, hn, hstr, hv, hb, Option.bind_eq_bind,
    Option.bind_some, require, beq_self_eq_true, Bool.and_self, ite_true]
  rfl

end C3.Json
