import C3BootProofs.Spec.Sha256

/-!
# Merkle inclusion proofs

RFC 6962 tree hashing and the RFC 9162 section 2.1.3.2 algorithm that
computes the root an inclusion proof implies, as `c3_verify::merkle` takes
it: the proof is the audit path's 32-byte hashes, concatenated, and has at
most 64 of them.
-/

namespace C3

/-- The RFC 6962 hash of a leaf. -/
def leafHash (data : Bytes) : Bytes := sha256 (0x00 :: data)

/-- The RFC 6962 hash of an interior node. -/
def nodeHash (left right : Bytes) : Bytes := sha256 (0x01 :: left ++ right)

/-- The most hashes an inclusion proof can have, for trees of up to 2^64 leaves. -/
def maxProofHashes : Nat := 64

/-- The 32-byte hashes of `bytes`, or `none` when bytes are left over. -/
def hashes32 : Nat → Bytes → Option (List Bytes)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, bytes@(_ :: _) =>
    if bytes.length < 32 then none else (bytes.take 32 :: ·) <$> hashes32 n (bytes.drop 32)

/-- Shifts `f` and `s` right together until `f` is odd or zero (step 4b ii). -/
def shiftEven (f s : Nat) : Nat × Nat :=
  if h : f % 2 = 0 ∧ f ≠ 0 then shiftEven (f / 2) (s / 2) else (f, s)
termination_by f
decreasing_by omega

/-- Step 4 for the hashes left: `f` and `s` are `fn` and `sn`, and `r` the
hash so far. Returns the final `sn` and `r`. -/
def inclusionPath : Nat → Nat → Bytes → List Bytes → Option (Nat × Bytes)
  | _, s, r, [] => some (s, r)
  | f, s, r, p :: ps =>
    if s = 0 then none
    else if f % 2 = 1 ∨ f = s then
      let (f, s) := shiftEven f s
      inclusionPath (f / 2) (s / 2) (nodeHash p r) ps
    else inclusionPath (f / 2) (s / 2) (nodeHash r p) ps

/-- The root that an inclusion proof for the leaf hash `leaf` at `index` in
a tree of `size` leaves implies, or `none` when the proof is malformed or
has the wrong number of hashes for that position. -/
def rootFromInclusion (index size : Nat) (leaf proof : Bytes) : Option Bytes := do
  let hashes ← hashes32 proof.length proof
  require (hashes.length ≤ maxProofHashes && index < size)
  let (s, r) ← inclusionPath index (size - 1) leaf hashes
  require (s == 0)
  pure r

end C3
