import C3BootProofs.Proofs.TufRoleKeysReadAt
import C3BootProofs.Proofs.TufParseRoot
import C3BootProofs.Proofs.TufPemSpki
import C3BootProofs.Proofs.TufHexDecode
import C3BootProofs.Proofs.CtAssign
import C3BootProofs.Proofs.TufExpires

/-!
# `tuf::RoleKeys`: the model and the layout

`RoleKeys::read(root, role)` reads a role's threshold and its listed key
IDs from a root's `signed` object, and decodes the key that `keys` names for
each ID with `decode_key`. This file holds the model of the function on the
bytes of the root, the layout of a `RoleKeys` in memory, and the code it
runs; `TufRoleKeysRead.lean` proves the machine-code contract.

A key is a pair of a tag and its bytes: 0 for a P-256 point, 1 for a P-384
point, and 2 for an Ed25519 key, as the compiled `Option<Key>` stores them.
-/

namespace C3.Json

/-- An ECDSA key that `decode_key` reads from the PEM text `pub`: the bytes
after the SPKI prefix `pfx` in the key `pem_spki` decodes, when `kl` bytes
follow it, tagged `t`. -/
def rkSpki (t : Nat) (pfx : Bytes) (kl : Nat) (pub : Bytes) : Option (Nat × Bytes) :=
  match pemSpkiModel pub with
  | none => none
  | some der => if der.take pfx.length = pfx ∧ der.length = pfx.length + kl then some (t, der.drop pfx.length)
    else none

/-- An Ed25519 key that `decode_key` reads from the hex text `pub`: 32
bytes, from at most 256 hex digits. -/
def rkHex (pub : Bytes) : Option (Nat × Bytes) :=
  match (if pub.length ≤ 256 then parseHex pub else none) with
  | none => none
  | some k => if k.length = 32 then some (2, k) else none

/-- The key `decode_key` reads for the key type `kt`, the scheme `sc`, and
the public key text `pub`. -/
def rkKey (kt sc pub : Bytes) : Option (Nat × Bytes) :=
  if sc = ascii!"ecdsa-sha2-nistp256" ∧ (kt = ascii!"ecdsa" ∨ kt = ascii!"ecdsa-sha2-nistp256") then
    rkSpki 0 p256SpkiPrefix 65 pub
  else if sc = ascii!"ecdsa-sha2-nistp384" ∧ (kt = ascii!"ecdsa" ∨ kt = ascii!"ecdsa-sha2-nistp384") then
    rkSpki 1 p384SpkiPrefix 97 pub
  else if kt = ascii!"ed25519" ∧ sc = ascii!"ed25519" then rkHex pub
  else none

/-- `tuf::decode_key` on the key object `v`. -/
def rkDecode (v : Bytes) : Option (Nat × Bytes) :=
  match objField v (ascii!"keytype") with
  | .error _ => none
  | .ok (tp, tl) =>
    match strBody (slice v tp tl) with
    | none => none
    | some kt =>
      match objField v (ascii!"scheme") with
      | .error _ => none
      | .ok (sp, sl) =>
        match strBody (slice v sp sl) with
        | none => none
        | some sc =>
          match objField v (ascii!"keyval") with
          | .error _ => none
          | .ok (vp, vl) =>
            match objField (slice v vp vl) (ascii!"public") with
            | .error _ => none
            | .ok (pp, pl) =>
              match strBody (slice (slice v vp vl) pp pl) with
              | none => none
              | some pub => rkKey kt sc pub

/-- A listed key: its ID and the key that decoded, if any. -/
abbrev RkEntry := Bytes × Option (Nat × Bytes)

/-- The loop over the `keyids` array `a` from `pos`, with the `keys`
object `kv` and `k` free slots: each key ID, at most 64 bytes, and the key
`kv` names for it. -/
def rkLoop (a kv : Bytes) : Nat → Nat → Except Nat (List RkEntry)
  | k, pos =>
    match nextElement a pos with
    | none => .error 0x20
    | some none => .ok []
    | some (some (ep, el, nx)) =>
      match strBody (slice a ep el) with
      | none => .error 0x21
      | some id =>
        match k with
        | 0 => .error 0x21
        | k + 1 =>
          if 64 < id.length then .error 0x21
          else
            match objGet kv id with
            | .error e => .error e
            | .ok v =>
              match rkLoop a kv k nx with
              | .error e => .error e
              | .ok es => .ok ((id, v.bind fun x => rkDecode (slice kv x.1 x.2)) :: es)

/-- The checks on the `keyids` value `a` of the role, and the loop. -/
def rkIds (a kv : Bytes) : Except Nat (List RkEntry) :=
  if a.length = 0 ∨ a.getD 0 0 ≠ 91 then .error 0x21 else rkLoop a kv 8 (skipWs a 1)

/-- The checks on the role `r` and the `keys` value `kv`, after the
threshold. -/
def rkRole (r kv : Bytes) : Except Nat (List RkEntry) :=
  if kv.length = 0 ∨ kv.getD 0 0 ≠ 123 then .error 0x21
  else
    match objField r (ascii!"keyids") with
    | .error e => .error e
    | .ok (ip, il) => rkIds (slice r ip il) kv

/-- `RoleKeys::read` on the root's `signed` value `d` and the role name
`role`: the threshold and the listed keys, or the error byte (`0x21` for
the schema, `0x20` for JSON outside the profile). -/
def rkModel (d role : Bytes) : Except Nat (Nat × List RkEntry) :=
  match objField d (ascii!"roles") with
  | .error e => .error e
  | .ok (rp, rl) =>
    match objField (slice d rp rl) role with
    | .error e => .error e
    | .ok (qp, ql) =>
      match objField (slice (slice d rp rl) qp ql) (ascii!"threshold") with
      | .error e => .error e
      | .ok (tp, tl) =>
        match u64Val (slice (slice (slice d rp rl) qp ql) tp tl) with
        | none => .error 0x21
        | some t =>
          if t = 0 then .error 0x21
          else
            match objField d (ascii!"keys") with
            | .error e => .error e
            | .ok (kp, kl) =>
              match rkRole (slice (slice d rp rl) qp ql) (slice d kp kl) with
              | .error e => .error e
              | .ok es => .ok (t, es)

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

/-! ## The layout of a `RoleKeys`

The compiler lays a `RoleKeys` out in 0x540 bytes: the eight
`Option<Key>`s of 98 bytes each (a tag byte, 0xFF for `None`, then the
key's bytes), the threshold's low and high words at 0x310, the key IDs of
64 bytes each at 0x318, their lengths at 0x518, and the count of listed
keys at 0x538. The bytes of a slot's key after the key's length, and the
last four bytes, are not specified. -/

/-- The little-endian word at `o` in the bytes `b`. -/
def w32 (b : Nat → BitVec 8) (o : Nat) : Word := b (o + 3) ++ b (o + 2) ++ b (o + 1) ++ b o

/-- The `Option<Key>` at `o`. -/
def RkKeyB (b : Nat → BitVec 8) (o : Nat) : Option (Nat × Bytes) → Prop
  | none => b o = 0xFF
  | some (t, k) => b o = BitVec.ofNat 8 t ∧ k.length ≤ 97 ∧
      ∀ j < k.length, b (o + 1 + j) = BitVec.ofNat 8 (k.getD j 0)

/-- Slot `i`: the key ID, zero after its length, the length, and the key. -/
def RkSlot (b : Nat → BitVec 8) (i : Nat) (e : RkEntry) : Prop :=
  e.1.length ≤ 64 ∧ (∀ j < 64, b (0x318 + 64 * i + j) = BitVec.ofNat 8 (e.1.getD j 0)) ∧
    w32 b (0x518 + 4 * i) = BitVec.ofNat 32 e.1.length ∧ RkKeyB b (98 * i) e.2

/-- The bytes `b` hold a `RoleKeys` with the threshold `t` and the listed
keys `es`; the slots after them are empty. -/
def RkB (b : Nat → BitVec 8) (t : Nat) (es : List RkEntry) : Prop :=
  es.length ≤ 8 ∧ (w32 b 0x314).toNat * 2 ^ 32 + (w32 b 0x310).toNat = t ∧
    w32 b 0x538 = BitVec.ofNat 32 es.length ∧ ∀ i < 8, RkSlot b i (es.getD i ([], none))

/-- The `RoleKeys` at `a`. -/
def RkAt (M : Word → BitVec 8) (a : Word) (t : Nat) (es : List RkEntry) : Prop :=
  RkB (fun o => M (a + BitVec.ofNat 32 o)) t es

theorem w32_congr {b b' : Nat → BitVec 8} {o : Nat} (h : ∀ j < 4, b' (o + j) = b (o + j)) : w32 b' o = w32 b o := by
  unfold w32
  rw [h 3 (by decide), h 2 (by decide), h 1 (by decide)]
  have := h 0 (by decide)
  rw [Nat.add_zero] at this
  rw [this]

theorem RkKeyB.congr {b b' : Nat → BitVec 8} {o : Nat} {k : Option (Nat × Bytes)} (h : RkKeyB b o k)
    (hb : ∀ j < 98, b' (o + j) = b (o + j)) : RkKeyB b' o k := by
  rcases k with _ | ⟨t, k⟩
  · show b' o = 0xFF
    have := hb 0 (by decide)
    rw [Nat.add_zero] at this
    rw [this]; exact h
  · obtain ⟨h0, hl, hk⟩ := h
    refine ⟨?_, hl, fun j hj => ?_⟩
    · have := hb 0 (by decide)
      rw [Nat.add_zero] at this
      rw [this]; exact h0
    · rw [show o + 1 + j = o + (1 + j) by omega, hb _ (by omega), ← show o + 1 + j = o + (1 + j) by omega]
      exact hk j hj

theorem RkSlot.congr {b b' : Nat → BitVec 8} {i : Nat} {e : RkEntry} (h : RkSlot b i e)
    (hid : ∀ j < 64, b' (0x318 + 64 * i + j) = b (0x318 + 64 * i + j))
    (hln : ∀ j < 4, b' (0x518 + 4 * i + j) = b (0x518 + 4 * i + j))
    (hk : ∀ j < 98, b' (98 * i + j) = b (98 * i + j)) : RkSlot b' i e := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨h0, fun j hj => (hid j hj).trans (h1 j hj), (w32_congr hln).trans h2, h3.congr hk⟩

/-- A `RoleKeys` depends only on its 0x540 bytes. -/
theorem RkB.congr {b b' : Nat → BitVec 8} {t : Nat} {es : List RkEntry} (h : RkB b t es)
    (hb : ∀ o < 0x540, b' o = b o) : RkB b' t es := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨h0, ?_, ?_, fun i hi => (h3 i hi).congr (fun j hj => hb _ (by omega)) (fun j hj => hb _ (by omega))
    (fun j hj => hb _ (by omega))⟩
  · rw [w32_congr (o := 0x314) (fun j hj => hb _ (by omega)), w32_congr (o := 0x310) (fun j hj => hb _ (by omega))]
    exact h1
  · rw [w32_congr (o := 0x538) (fun j hj => hb _ (by omega))]; exact h2

/-- The slot after the listed keys, filled with the entry `(id, key)`, and
the count raised: the bytes outside the ID's first `id.length` bytes, the
length, the slot's key, and the count are as before. -/
theorem RkB.push {b b' : Nat → BitVec 8} {t : Nat} {es : List RkEntry} {id : Bytes} {key : Option (Nat × Bytes)}
    (h : RkB b t es) (hl : es.length < 8) (hid : id.length ≤ 64)
    (hO : ∀ o < 0x540, ¬(0x318 + 64 * es.length ≤ o ∧ o < 0x318 + 64 * es.length + id.length) →
      ¬(0x518 + 4 * es.length ≤ o ∧ o < 0x518 + 4 * es.length + 4) → ¬(98 * es.length ≤ o ∧ o < 98 * es.length + 98) →
      ¬(0x538 ≤ o ∧ o < 0x53C) → b' o = b o)
    (hids : ∀ j < id.length, b' (0x318 + 64 * es.length + j) = BitVec.ofNat 8 (id.getD j 0))
    (hlen : w32 b' (0x518 + 4 * es.length) = BitVec.ofNat 32 id.length) (hk : RkKeyB b' (98 * es.length) key)
    (hls : w32 b' 0x538 = BitVec.ofNat 32 (es.length + 1)) :
    RkB b' t (es ++ [(id, key)]) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨by rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega, ?_, ?_, fun i hi => ?_⟩
  · rw [w32_congr (o := 0x314) (fun j hj => hO _ (by omega) (by omega) (by omega) (by omega) (by omega)),
      w32_congr (o := 0x310) (fun j hj => hO _ (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact h1
  · rw [hls, List.length_append]; rfl
  · rcases Nat.lt_trichotomy i es.length with hi' | hi' | hi'
    · have e : (es ++ [(id, key)]).getD i ([], none) = es.getD i ([], none) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
      rw [e]
      refine (h3 i hi).congr (fun j hj => hO _ (by omega) (by omega) (by omega) (by omega) (by omega))
        (fun j hj => hO _ (by omega) (by omega) (by omega) (by omega) (by omega))
        (fun j hj => hO _ (by omega) (by omega) (by omega) (by omega) (by omega))
    · subst hi'
      have e : (es ++ [(id, key)]).getD es.length ([], none) = (id, key) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      have e0 : es.getD es.length ([], none) = ([], none) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_refl _), Option.getD_none]
      have h3i := h3 es.length hi
      rw [e0] at h3i
      rw [e]
      refine ⟨hid, fun j hj => ?_, hlen, hk⟩
      by_cases hj' : j < id.length
      · exact hids j hj'
      · rw [hO _ (by omega) (by omega) (by omega) (by omega) (by omega), h3i.2.1 j hj]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none,
          List.getElem?_eq_none (show id.length ≤ j by omega)]
    · have e : (es ++ [(id, key)]).getD i ([], none) = ([], none) := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega)]
        rfl
      have e0 : es.getD i ([], none) = ([], none) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show es.length ≤ i by omega), Option.getD_none]
      have h3i := h3 i hi
      rw [e0] at h3i
      rw [e]
      exact h3i.congr (fun j hj => hO _ (by omega) (by omega) (by omega) (by omega) (by omega))
        (fun j hj => hO _ (by omega) (by omega) (by omega) (by omega) (by omega))
        (fun j hj => hO _ (by omega) (by omega) (by omega) (by omega) (by omega))

end C3.RV32
