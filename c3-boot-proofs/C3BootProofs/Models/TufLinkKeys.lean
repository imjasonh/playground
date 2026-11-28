import C3BootProofs.Models.TufLinkMeta
import C3BootProofs.Proofs.TufRoleKeys

/-!
# `rkModel` against `Spec/Tuf.lean`

`RoleKeys::read` is the part of `tuf::threshold_met` that reads a role's
threshold, its key IDs, and the keys that `keys` names for them.
`roleKeys` is that part of `thresholdMet`, and `rkModel_spec` relates the
position model to it. `thresholdMet_roleKeys` shows that `thresholdMet` is
`roleKeys` followed by `metOf`. A model key is a tag and bytes, which `keyTag` gives
for a `TufKey`.
-/

namespace C3.Json

open C3.RV32 (Word curOpen)

/-- The tag and bytes that `RoleKeys` stores for a key. -/
def keyTag : TufKey → Nat × Bytes
  | .p256 p => (0, p)
  | .p384 p => (1, p)
  | .ed25519 k => (2, k)

theorem tlk_bind {α β : Type} {x : Option α} {f : α → Option β} {g : β} {P : β → Prop}
    (h : x.bind f = some g) (hf : ∀ a, f a = some g → P g) : P g := by
  cases x with
  | none => cases h
  | some a => exact hf a h

theorem tlk_group {c0 c1 c2 c3 pad : Nat} {g : Bytes} (h : b64Group c0 c1 c2 c3 pad = some g) :
    g.length = 3 - pad := by
  unfold b64Group at h
  simp only [Option.bind_eq_bind] at h
  refine tlk_bind (P := fun g => g.length = 3 - pad) h fun _ h =>
    tlk_bind (P := fun g => g.length = 3 - pad) h fun _ h => ?_
  have fin : ∀ (bits : Nat) (u : Option Unit), (u.bind fun _ => pure (List.take (3 - pad)
      [bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256])) = some g → g.length = 3 - pad := by
    intro bits u hu
    refine tlk_bind (P := fun g => g.length = 3 - pad) hu fun _ hu => ?_
    rw [Option.pure_def] at hu
    have hu := Option.some.inj hu
    subst hu
    rw [List.length_take]; simp only [List.length_cons, List.length_nil]; omega
  split at h <;> refine tlk_bind (P := fun g => g.length = 3 - pad) h fun _ h => ?_ <;> split at h <;>
    refine tlk_bind (P := fun g => g.length = 3 - pad) h fun _ h => ?_ <;> exact fin _ _ h

/-- Base64 text is at most four characters for each three bytes, rounded up. -/
theorem tlk_b64_len : ∀ {x bs : Bytes}, base64Decode x = some bs → 3 * x.length ≤ 4 * (bs.length + 2)
  | [], bs, h => by
    rw [base64Decode.eq_1] at h
    cases h; decide
  | [c0, c1, c2, c3], bs, h => by
    rw [base64Decode.eq_2] at h
    have := tlk_group h
    have hp : (if c2 = b64Pad ∧ c3 = b64Pad then 2 else if c3 = b64Pad then 1 else 0) ≤ 2 := by
      split
      · exact Nat.le_refl _
      split <;> decide
    simp only [List.length_cons, List.length_nil]; omega
  | c0 :: c1 :: c2 :: c3 :: hd :: tl, bs, h => by
    rw [base64Decode.eq_3] at h
    cases hg : b64Group c0 c1 c2 c3 0 with
    | none => rw [hg] at h; cases h
    | some g =>
      cases hr : base64Decode (hd :: tl) with
      | none => rw [hg, hr] at h; cases h
      | some r =>
        rw [hg, hr] at h
        cases h
        have h1 := tlk_group hg
        have h2 := tlk_b64_len hr
        simp only [List.length_cons, List.length_append] at h1 h2 ⊢; omega
  | [a], _, h => by
    rw [base64Decode.eq_4 [a] (by intro e; cases e) (by intro _ _ _ _ e; cases e) (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h
  | [a, b], _, h => by
    rw [base64Decode.eq_4 [a, b] (by intro e; cases e) (by intro _ _ _ _ e; cases e) (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h
  | [a, b, c], _, h => by
    rw [base64Decode.eq_4 [a, b, c] (by intro e; cases e) (by intro _ _ _ _ e; cases e)
      (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h

theorem tlk_hex_len : ∀ {s k : Bytes}, parseHex s = some k → s.length = 2 * k.length
  | [], k, h => by unfold parseHex at h; cases h; rfl
  | [_], _, h => by unfold parseHex at h; cases h
  | a :: b :: rest, k, h => by
    unfold parseHex at h
    simp only [Option.bind_eq_bind] at h
    revert h
    rcases hexDigit a with _ | hi
    · intro h; cases h
    rcases hexDigit b with _ | lo
    · intro h; cases h
    rcases hr : parseHex rest with _ | r
    · intro h; cases h
    intro h; cases h
    have := tlk_hex_len hr
    simp only [List.length_cons]; omega

theorem tlk_bfalse {a b : Bytes} (h : a ≠ b) : (a == b) = false := by
  rcases hb : (a == b) with _ | _
  · rfl
  exact absurd (beq_iff_eq.mp hb) h

theorem tlk_nfalse {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  rcases hb : (a == b) with _ | _
  · rfl
  exact absurd (beq_iff_eq.mp hb) h

theorem tlk_spki_len {pfx der p : Bytes} {kl : Nat} (h : spkiPoint pfx kl der = some p) :
    der.take pfx.length = pfx ∧ der.length = pfx.length + kl ∧ p = der.drop pfx.length := by
  unfold spkiPoint readExpect at h
  by_cases c : (der.take pfx.length == pfx && decide (pfx.length ≤ der.length)) = true
  · rw [if_pos c] at h
    change (require ((der.drop pfx.length).length == kl)).bind (fun _ => some (der.drop pfx.length)) = some p at h
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c
    rcases hr : ((der.drop pfx.length).length == kl) with _ | _
    · rw [hr] at h; cases h
    rw [hr] at h; cases h
    have := beq_iff_eq.mp hr
    rw [List.length_drop] at this
    exact ⟨c.1, by omega, rfl⟩
  · rw [if_neg c] at h; cases h

/-- An ECDSA key: the model's limits on the PEM text and the key hold for
every key the spec accepts. -/
theorem tlk_spki {t : Nat} {mk : Bytes → TufKey} (hmk : ∀ p, keyTag (mk p) = (t, p)) {pfx : Bytes} {kl : Nat}
    (hb : pfx.length + kl ≤ 128) (hb2 : 4 * (pfx.length + kl + 2) ≤ 576) (pub : Bytes) :
    rkSpki t pfx kl pub = (mk <$> (pemSpki pub >>= spkiPoint pfx kl)).map keyTag := by
  unfold rkSpki
  rcases hm : pemSpkiModel pub with _ | der
  · rcases hs : pemSpki pub with _ | der'
    · rfl
    show none = Option.map keyTag (Option.map mk (spkiPoint pfx kl der'))
    rcases hp : spkiPoint pfx kl der' with _ | p
    · rfl
    exfalso
    obtain ⟨-, hl, -⟩ := tlk_spki_len hp
    have hs' := hs
    rw [tl_pem_lines] at hs'
    by_cases H : pub.take 27 = ascii!"-----BEGIN PUBLIC KEY-----\n" ∧ 52 ≤ pub.length ∧
        pub.drop (pub.length - 25) = ascii!"-----END PUBLIC KEY-----\n"
    · rw [if_pos H] at hs'
      have h3 := tlk_b64_len hs'
      have := (pemSpkiModel_spec pub der').mpr ⟨hs, by omega, by omega⟩
      rw [hm] at this; cases this
    · rw [if_neg H] at hs'; cases hs'
  have hs := ((pemSpkiModel_spec pub der).mp hm).1
  rw [hs]
  show (if der.take pfx.length = pfx ∧ der.length = pfx.length + kl then some (t, der.drop pfx.length)
    else none) = Option.map keyTag (Option.map mk (spkiPoint pfx kl der))
  by_cases C : der.take pfx.length = pfx ∧ der.length = pfx.length + kl
  · rw [if_pos C]
    have hp : spkiPoint pfx kl der = some (der.drop pfx.length) := by
      unfold spkiPoint readExpect
      rw [if_pos (by rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact ⟨C.1, by omega⟩)]
      change (require ((der.drop pfx.length).length == kl)).bind (fun _ => some (der.drop pfx.length)) = _
      rw [show ((der.drop pfx.length).length == kl) = true from beq_iff_eq.mpr (by rw [List.length_drop]; omega)]
      rfl
    rw [hp]; show _ = some (keyTag (mk _)); rw [hmk]
  · rw [if_neg C]
    rcases hp : spkiPoint pfx kl der with _ | p
    · rfl
    obtain ⟨h1, h2, -⟩ := tlk_spki_len hp
    exact absurd ⟨h1, h2⟩ C

/-- An Ed25519 key: 32 bytes come from 64 hex digits, within the model's
limit of 256. -/
theorem tlk_hexk (pub : Bytes) :
    rkHex pub = (do
      let k ← parseHex pub
      require (k.length == 32)
      pure (TufKey.ed25519 k)).map keyTag := by
  unfold rkHex
  by_cases hl : pub.length ≤ 256
  · rw [if_pos hl]
    rcases parseHex pub with _ | k
    · rfl
    show (if k.length = 32 then some (2, k) else none) = ((require (k.length == 32)).bind _).map keyTag
    by_cases h32 : k.length = 32
    · rw [if_pos h32, show (k.length == 32) = true from beq_iff_eq.mpr h32]; rfl
    · rw [if_neg h32, tlk_nfalse h32]; rfl
  · rw [if_neg hl]
    rcases hp : parseHex pub with _ | k
    · rfl
    have := tlk_hex_len hp
    show none = ((require (k.length == 32)).bind _).map keyTag
    rw [tlk_nfalse (by omega : k.length ≠ 32)]; rfl

/-- A string member, read with `Value::field` and `Value::str`. -/
theorem tlk_fsb {α : Type} {c : Bool} {v : Bytes} {j : Json} {key : Bytes} (h : JVal c v j)
    (k : Bytes → Option α) :
    (match objField v key with
      | .error _ => none
      | .ok (p, l) => match strBody (slice v p l) with
        | none => none
        | some s => k s) = (j.field key >>= Json.asStr).bind k := by
  have hf := ObjField c v j key h
  rcases hk : j.field key with _ | jk
  · rw [hk] at hf; simp only at hf; rw [hf]; rfl
  rw [hk] at hf; simp only at hf
  obtain ⟨kp, kl, ho, hd⟩ := hf
  rw [ho]; simp only
  rw [tl_strBody hd.2]
  show _ = (jk.asStr).bind k
  rcases jk.asStr <;> rfl

theorem tlk_c2 (kt sc a b : Bytes) :
    (((kt == a) || (kt == b)) && (sc == b)) = true ↔ (sc = b ∧ (kt = a ∨ kt = b)) := by
  rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq]
  exact ⟨fun ⟨x, y⟩ => ⟨y, x⟩, fun ⟨x, y⟩ => ⟨y, x⟩⟩

theorem tlk_c1 (kt sc a : Bytes) : ((kt == a) && (sc == a)) = true ↔ (kt = a ∧ sc = a) := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

/-- `decode_key` is `decodeKey`, with the key as its tag and bytes. -/
theorem tlk_decode {v : Bytes} {j : Json} (h : JVal true v j) : rkDecode v = (decodeKey j).map keyTag := by
  unfold rkDecode decodeKey
  simp only [Option.bind_eq_bind]
  have hf := ObjField true v j (ascii!"keytype") h
  rcases hk : j.field (ascii!"keytype") with _ | jt
  · rw [hk] at hf; simp only at hf; rw [hf]; rfl
  rw [hk] at hf; simp only at hf
  obtain ⟨tp, tl, ho, hd⟩ := hf
  rw [ho]; simp only
  rw [tl_strBody hd.2, Option.bind_some]
  rcases jt.asStr with _ | kt
  · rfl
  simp only [Option.bind_some]
  have hf := ObjField true v j (ascii!"scheme") h
  rcases hk : j.field (ascii!"scheme") with _ | js
  · rw [hk] at hf; simp only at hf; rw [hf]; rfl
  rw [hk] at hf; simp only at hf
  obtain ⟨sp, sl, ho, hd⟩ := hf
  rw [ho]; simp only
  rw [tl_strBody hd.2, Option.bind_some]
  rcases js.asStr with _ | sc
  · rfl
  simp only [Option.bind_some]
  have hf := ObjField true v j (ascii!"keyval") h
  rcases hk : j.field (ascii!"keyval") with _ | jk
  · rw [hk] at hf; simp only at hf; rw [hf]; rfl
  rw [hk] at hf; simp only at hf
  obtain ⟨vp, vl, ho, hd⟩ := hf
  rw [ho]; simp only [Option.bind_some]
  have hf := ObjField true (slice v vp vl) jk (ascii!"public") hd.2
  rcases hk : jk.field (ascii!"public") with _ | jp
  · rw [hk] at hf; simp only at hf; rw [hf]; rfl
  rw [hk] at hf; simp only at hf
  obtain ⟨pp, pl, ho, hd'⟩ := hf
  rw [ho]; simp only
  rw [tl_strBody hd'.2, Option.bind_some]
  rcases jp.asStr with _ | pub
  · rfl
  simp only [Option.bind_some]
  unfold rkKey
  by_cases c1 : sc = ascii!"ecdsa-sha2-nistp256" ∧ (kt = ascii!"ecdsa" ∨ kt = ascii!"ecdsa-sha2-nistp256")
  · rw [if_pos c1, if_pos ((tlk_c2 kt sc _ _).mpr c1)]
    exact tlk_spki (fun _ => rfl) (by decide) (by decide) pub
  rw [if_neg c1, if_neg (fun hb => c1 ((tlk_c2 kt sc _ _).mp hb))]
  by_cases c2 : sc = ascii!"ecdsa-sha2-nistp384" ∧ (kt = ascii!"ecdsa" ∨ kt = ascii!"ecdsa-sha2-nistp384")
  · rw [if_pos c2, if_pos ((tlk_c2 kt sc _ _).mpr c2)]
    exact tlk_spki (fun _ => rfl) (by decide) (by decide) pub
  rw [if_neg c2, if_neg (fun hb => c2 ((tlk_c2 kt sc _ _).mp hb))]
  by_cases c3 : kt = ascii!"ed25519" ∧ sc = ascii!"ed25519"
  · rw [if_pos c3, if_pos ((tlk_c1 kt sc _).mpr c3)]
    exact tlk_hexk pub
  rw [if_neg c3, if_neg (fun hb => c3 ((tlk_c1 kt sc _).mp hb))]
  rfl

/-- The entry for the key ID `id` with the `keys` members `ms`. -/
def keyEntry (ms : List (Bytes × Json)) (id : Bytes) : RkEntry := (id, (ms.lookup id >>= decodeKey).map keyTag)

theorem tlk_get {kv : Bytes} {ms : List (Bytes × Json)} (hkv : JVal true kv (.obj ms)) (id : Bytes) :
    ∃ v, objGet kv id = .ok v ∧ (v.bind fun x => rkDecode (slice kv x.1 x.2)) = (keyEntry ms id).2 := by
  have hg := ObjGet true kv (.obj ms) id hkv
  dsimp only [Json.asObj] at hg
  unfold keyEntry
  rcases hl : ms.lookup id with _ | j'
  · rw [hl] at hg; exact ⟨none, hg, rfl⟩
  rw [hl] at hg
  obtain ⟨vp, vl, ho, hd⟩ := hg
  exact ⟨some (vp, vl), ho, tlk_decode hd.2⟩

/-- The loop over the key IDs reads each one as a string, takes at most `k`
of at most 64 bytes, and looks each up in `keys`. -/
theorem tlk_loop {a kv : Bytes} {ms : List (Bytes × Json)} (hkv : JVal true kv (.obj ms)) :
    ∀ (js : List Json) (k pos : Nat), ElementsFrom true a pos js →
    (rkLoop a kv k pos).toOption = (js.mapM Json.asStr).bind (fun ids =>
      (require (decide (ids.length ≤ k) && ids.all (fun x => decide (x.length ≤ 64)))).bind
        (fun _ => some (ids.map (keyEntry ms))))
  | [], k, pos, he => by
    unfold ElementsFrom at he
    unfold rkLoop; rw [he, List.mapM_nil]
    show some [] = (require (decide (([] : List Bytes).length ≤ k) && true)).bind
      (fun _ => some ([] : List RkEntry))
    rfl
  | s :: js, k, pos, he => by
    obtain ⟨l, nx, hne, hd, hel⟩ := he
    unfold rkLoop; rw [hne]; simp only
    rw [tl_strBody hd.2, List.mapM_cons]
    rcases s.asStr with _ | id
    · rfl
    simp only [Option.bind_eq_bind, Option.bind_some]
    have ih := tlk_loop (a := a) hkv js
    rcases k with _ | k
    · show none = _
      rcases js.mapM Json.asStr with _ | ids
      · rfl
      show none = (require (decide ((id :: ids).length ≤ 0) &&
        (id :: ids).all (fun x => decide (x.length ≤ 64)))).bind
          (fun _ => some ((id :: ids).map (keyEntry ms)))
      rw [decide_eq_false (by simp only [List.length_cons]; omega)]; rfl
    show (if 64 < id.length then Except.error 0x21 else _).toOption = _
    by_cases hl : 64 < id.length
    · rw [if_pos hl]
      rcases js.mapM Json.asStr with _ | ids
      · rfl
      show none = (require (decide ((id :: ids).length ≤ k + 1) &&
        (decide (id.length ≤ 64) && ids.all (fun x => decide (x.length ≤ 64))))).bind
          (fun _ => some ((id :: ids).map (keyEntry ms)))
      rw [decide_eq_false (by omega : ¬ id.length ≤ 64), Bool.false_and, Bool.and_false]; rfl
    rw [if_neg hl]
    obtain ⟨v, hv, hve⟩ := tlk_get hkv id
    rw [hv]; simp only
    rw [hve]
    have ih' := ih k nx hel
    revert ih'
    generalize rkLoop a kv k nx = r
    rcases js.mapM Json.asStr with _ | ids
    · intro ih'
      rcases r with e | es
      · rfl
      cases ih'
    intro ih'
    show _ = (require (decide ((id :: ids).length ≤ k + 1) &&
      (decide (id.length ≤ 64) && ids.all (fun x => decide (x.length ≤ 64))))).bind
        (fun _ => some (keyEntry ms id :: ids.map (keyEntry ms)))
    change r.toOption = (require (decide (ids.length ≤ k) && ids.all (fun x => decide (x.length ≤ 64)))).bind
      (fun _ => some (ids.map (keyEntry ms))) at ih'
    rw [decide_eq_true (by omega : id.length ≤ 64), Bool.true_and]
    have hk : decide ((id :: ids).length ≤ k + 1) = decide (ids.length ≤ k) := by
      by_cases hk : ids.length ≤ k
      · rw [decide_eq_true hk, decide_eq_true (by simp only [List.length_cons]; omega)]
      · rw [decide_eq_false hk, decide_eq_false (by simp only [List.length_cons]; omega)]
    rw [hk]
    revert ih'
    generalize (decide (ids.length ≤ k) && ids.all (fun x => decide (x.length ≤ 64))) = B
    intro ih'
    rcases r with e | es <;> cases B
    · rfl
    · cases ih'
    · cases ih'
    · cases ih'; rfl

/-- The checks on the role `r` and the `keys` value `kv`. -/
theorem tlk_role {r kv : Bytes} {jr kj : Json} (hr : JVal true r jr) (hk : JVal true kv kj) :
    (rkRole r kv).toOption = kj.asObj.bind fun ms =>
      (jr.field (ascii!"keyids") >>= Json.asArr).bind fun js => (js.mapM Json.asStr).bind fun ids =>
        (require (decide (ids.length ≤ 8) && ids.all (fun x => decide (x.length ≤ 64)))).bind
          fun _ => some (ids.map (keyEntry ms)) := by
  have ho := (CurOpen true kv kj 0 hk).1
  unfold rkRole
  by_cases hc : kv.length = 0 ∨ kv.getD 0 0 ≠ 123
  · rw [if_pos hc]
    rw [tlm_open.mp hc] at ho
    rcases hA : kj.asObj with _ | ms
    · rfl
    rw [hA] at ho; cases ho
  rw [if_neg hc]
  rcases hA : kj.asObj with _ | ms
  · rcases hcu : curOpen 123 0 kv with _ | _
    · exact absurd (tlm_open.mpr hcu) hc
    rw [hcu, hA] at ho; cases ho
  have hj := tlm_asObj hA
  subst hj
  rw [Option.bind_some]
  have hf := ObjField true r jr (ascii!"keyids") hr
  rcases hq : jr.field (ascii!"keyids") with _ | ja
  · rw [hq] at hf; simp only at hf; rw [hf]; rfl
  rw [hq] at hf; simp only at hf
  obtain ⟨ip, il, ho2, hd⟩ := hf
  rw [ho2]; simp only
  rw [show (some ja >>= Json.asArr) = ja.asArr from rfl]
  unfold rkIds
  have ho3 := (CurOpen true _ ja 0 hd.2).2.1
  by_cases hc2 : (slice r ip il).length = 0 ∨ (slice r ip il).getD 0 0 ≠ 91
  · rw [if_pos hc2]
    rw [tlm_open.mp hc2] at ho3
    rcases hB : ja.asArr with _ | js
    · rfl
    rw [hB] at ho3; cases ho3
  rw [if_neg hc2]
  rcases hB : ja.asArr with _ | js
  · rcases hcu : curOpen 91 0 (slice r ip il) with _ | _
    · exact absurd (tlm_open.mpr hcu) hc2
    rw [hcu, hB] at ho3; cases ho3
  have hj := tlm_asArr hB
  subst hj
  exact tlk_loop hk js 8 _ (Elements true _ js hd.2)

/-- `RoleKeys::read` in the spec: the threshold of the role `role` in the
root's `signed` value `delegator`, and each listed key ID with the key
that `keys` gives for it, if any. The checks are those of `thresholdMet`. -/
def roleKeys (delegator : Json) (role : Bytes) : Option (Nat × List (Bytes × Option TufKey)) := do
  let r ← delegator.field (ascii!"roles") >>= Json.field role
  let threshold ← r.field (ascii!"threshold") >>= Json.asNum
  require (threshold ≥ 1)
  let keys ← delegator.field (ascii!"keys") >>= Json.asObj
  let ids ← (← r.field (ascii!"keyids") >>= Json.asArr).mapM Json.asStr
  require (ids.length ≤ 8 && ids.all (·.length ≤ 64))
  pure (threshold, ids.map fun id => (id, keys.lookup id >>= decodeKey))

/-- An entry of `roleKeys` as the model writes it. -/
def rkTag (e : Bytes × Option TufKey) : RkEntry := (e.1, e.2.map keyTag)

theorem tlk_map (ms : List (Bytes × Json)) : ∀ ids : List Bytes,
    ids.map (keyEntry ms) = (ids.map fun id => (id, ms.lookup id >>= decodeKey)).map rkTag
  | [] => rfl
  | id :: ids => by
    simp only [List.map_cons]
    rw [← tlk_map ms ids]; rfl

/-- `rkModel` on the `signed` bytes `d` of a root is `roleKeys` on its
value, with each key as the model writes it. -/
theorem rkModel_spec {d role : Bytes} {dj : Json} (h : JVal true d dj) :
    (rkModel d role).toOption = (roleKeys dj role).map fun r => (r.1, r.2.map rkTag) := by
  unfold rkModel roleKeys
  simp only [Option.bind_eq_bind]
  have hf := ObjField true d dj (ascii!"roles") h
  rcases hq : dj.field (ascii!"roles") with _ | jr
  · rw [hq] at hf; simp only at hf; rw [hf]; rfl
  rw [hq] at hf; simp only at hf
  obtain ⟨rp, rl, ho, hd⟩ := hf
  rw [ho]; simp only [Option.bind_some]
  have hf := ObjField true _ jr role hd.2
  rcases hq : jr.field role with _ | jq
  · rw [hq] at hf; simp only at hf; rw [hf]; rfl
  rw [hq] at hf; simp only at hf
  obtain ⟨qp, ql, ho, hd⟩ := hf
  rw [ho]; simp only [Option.bind_some]
  have hf := ObjField true _ jq (ascii!"threshold") hd.2
  rcases hq : jq.field (ascii!"threshold") with _ | jt
  · rw [hq] at hf; simp only at hf; rw [hf]; rfl
  rw [hq] at hf; simp only at hf
  obtain ⟨tp, tl, ho, hd'⟩ := hf
  rw [ho]; simp only [Option.bind_some]
  rw [U64Val true _ jt hd'.2]
  rcases jt.asNum with _ | t
  · rfl
  simp only [Option.bind_some]
  by_cases ht : t = 0
  · rw [if_pos ht]
    show none = Option.map _ ((require (decide (t ≥ 1))).bind _)
    rw [decide_eq_false (by omega)]; rfl
  rw [if_neg ht]
  show _ = Option.map _ ((require (decide (t ≥ 1))).bind _)
  rw [decide_eq_true (by omega)]
  show _ = Option.map _ ((dj.field (ascii!"keys")).bind Json.asObj |>.bind _)
  have hf := ObjField true d dj (ascii!"keys") h
  rcases hq : dj.field (ascii!"keys") with _ | jk
  · rw [hq] at hf; simp only at hf; rw [hf]; rfl
  rw [hq] at hf; simp only at hf
  obtain ⟨kp, kl, ho, hdk⟩ := hf
  rw [ho]; simp only [Option.bind_some]
  have hr := tlk_role (r := slice (slice d rp rl) qp ql) (kv := slice d kp kl) hd.2 hdk.2
  revert hr
  generalize rkRole (slice (slice d rp rl) qp ql) (slice d kp kl) = R
  simp only [Option.bind_eq_bind]
  rcases jk.asObj with _ | ms
  · intro hr; rcases R with e | es
    · rfl
    · cases hr
  simp only [Option.bind_some]
  rcases jq.field (ascii!"keyids") with _ | ja
  · intro hr; rcases R with e | es
    · rfl
    · cases hr
  simp only [Option.bind_some]
  rcases ja.asArr with _ | js
  · intro hr; rcases R with e | es
    · rfl
    · cases hr
  simp only [Option.bind_some]
  rcases js.mapM Json.asStr with _ | ids
  · intro hr; rcases R with e | es
    · rfl
    · cases hr
  simp only [Option.bind_some]
  generalize (decide (ids.length ≤ 8) && ids.all (fun x => decide (x.length ≤ 64))) = B
  intro hr
  rcases R with e | es <;> cases B
  · rfl
  · cases hr
  · cases hr
  · cases hr
    show some (t, ids.map (keyEntry ms)) = some (t, _)
    rw [tlk_map]
    rfl

/-- The rest of `thresholdMet` after `roleKeys`: the distinct keys among
`es` with a valid signature in `md`, against the threshold `t`. -/
def metOf (md : Meta) (t : Nat) (es : List (Bytes × Option TufKey)) : Bool :=
  let msg := encode md.signed
  let good := es.filterMap fun e => do
    let key ← e.2
    let sig ← md.sigs.lookup e.1
    if sigValid key msg sig then some key else none
  good.eraseDups.length ≥ t

theorem tlk_fm {α β γ : Type} (f : α → β) (g : β → Option γ) :
    ∀ l : List α, (l.map f).filterMap g = l.filterMap (fun a => g (f a))
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.filterMap_cons, tlk_fm f g l]

theorem thresholdMet_roleKeys (md : Meta) (dj : Json) (role : Bytes) :
    thresholdMet md dj role = (roleKeys dj role).map fun r => metOf md r.1 r.2 := by
  unfold thresholdMet roleKeys metOf
  simp only [Option.bind_eq_bind]
  rcases dj.field (ascii!"roles") with _ | jr
  · rfl
  simp only [Option.bind_some]
  rcases jr.field role with _ | jq
  · rfl
  simp only [Option.bind_some]
  rcases (jq.field (ascii!"threshold")).bind Json.asNum with _ | t
  · rfl
  simp only [Option.bind_some]
  rcases require (decide (t ≥ 1)) with _ | _
  · rfl
  simp only [Option.bind_some]
  rcases (dj.field (ascii!"keys")).bind Json.asObj with _ | ms
  · rfl
  simp only [Option.bind_some]
  rcases (jq.field (ascii!"keyids")).bind Json.asArr with _ | js
  · rfl
  simp only [Option.bind_some]
  rcases js.mapM Json.asStr with _ | ids
  · rfl
  simp only [Option.bind_some]
  rcases require (decide (ids.length ≤ 8) && ids.all (fun x => decide (x.length ≤ 64))) with _ | _
  · rfl
  simp only [Option.bind_some]
  have key : ∀ A B : List TufKey, A = B →
      some (decide (A.eraseDups.length ≥ t)) = some (decide (B.eraseDups.length ≥ t)) := fun _ _ h => h ▸ rfl
  refine key _ _ ?_
  show _ = List.filterMap _ (List.map _ ids)
  rw [tlk_fm]

end C3.Json
