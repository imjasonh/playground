import C3BootProofs.Proofs.TufRoleKeys
import C3BootProofs.Spec.Tuf

/-!
# `RoleKeys::met`: the model

`RoleKeys::met(meta)` counts the distinct keys of a `RoleKeys` that signed
the message of `meta`, and compares the count with the threshold. For each
listed key ID with a key, it finds the first signature with that key ID,
skips a key that it already counted, and checks the signature.

`metLookup` is the search through the signatures array `a`, the way the
compiled loop reads it. `sigOkT` is `sigValid` on a key as `RoleKeys`
stores it, a tag and bytes. `MetSound` is what a result of `Ok(true)`
shows: at least `t` distinct keys, each listed with a key ID whose
signature checks.
-/

namespace C3.Json

/-- The search for the key ID `id` from `pos` in the signatures array `a`:
`some none` when no item has the key ID, `some (some sig)` for the first
item that has it, and `none` when an item before it, or that item, has no
string `keyid` or no string `sig`. -/
def metSig (a id : Bytes) : Nat → Nat → Option (Option Bytes)
  | 0, _ => none
  | k + 1, pos =>
    match nextElement a pos with
    | none => none
    | some none => some none
    | some (some (ep, el, nx)) =>
      match objField (slice a ep el) (ascii!"keyid") with
      | .error _ => none
      | .ok (kp, kl) =>
        match strBody (slice (slice a ep el) kp kl) with
        | none => none
        | some k2 =>
          if k2 = id then
            match objField (slice a ep el) (ascii!"sig") with
            | .error _ => none
            | .ok (gp, gl) => (strBody (slice (slice a ep el) gp gl)).map some
          else metSig a id k nx

/-- The search for the key ID `id` in the signatures array `a`. -/
def metLookup (a id : Bytes) : Option (Option Bytes) :=
  if a.length = 0 ∨ a.getD 0 0 ≠ 91 then none else metSig a id (a.length + 1) (skipWs a 1)

/-- `sigValid` on a key as `RoleKeys` stores it. -/
def sigOkT (k : Nat × Bytes) (msg sig : Bytes) : Bool :=
  match k with
  | (0, p) => sigValid (.p256 p) msg sig
  | (1, p) => sigValid (.p384 p) msg sig
  | (2, p) => sigValid (.ed25519 p) msg sig
  | _ => false

/-- The bytes of `l` as memory holds them. -/
def nb (l : Bytes) : Bytes := l.map (· % 256)

/-- An entry as memory holds it. -/
def nbE (e : RkEntry) : RkEntry := (nb e.1, e.2.map fun k => (k.1, nb k.2))

/-- Each key in `es` has a tag and a length that `decode_key` gives: 65
bytes for P-256, 97 for P-384, and 32 for Ed25519. -/
def RkWf (es : List RkEntry) : Prop :=
  ∀ e ∈ es, ∀ k, e.2 = some k → (k.1 = 0 ∧ k.2.length = 65) ∨ (k.1 = 1 ∧ k.2.length = 97) ∨
    (k.1 = 2 ∧ k.2.length = 32)

/-- At least `t` distinct keys in `es`, each listed under a key ID whose
first signature in `a` checks over `msg`. -/
def MetSound (a msg : Bytes) (t : Nat) (es : List RkEntry) : Prop :=
  ∃ ks : List (Nat × Bytes), ks.Nodup ∧ t ≤ ks.length ∧
    ∀ k ∈ ks, ∃ id sig, (id, some k) ∈ es ∧ metLookup a id = some (some sig) ∧ sigOkT k msg sig = true

end C3.Json
