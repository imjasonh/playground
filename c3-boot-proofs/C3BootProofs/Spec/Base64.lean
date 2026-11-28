import C3BootProofs.Spec.Formats

/-!
# Base64

Standard padded base64, RFC 4648 section 4, as `c3_verify::base64` encodes
and decodes it. Decoding accepts only canonical text: a multiple of four
characters, padding only in the last group, and zero bits in the unused low
bits of the last character.
-/

namespace C3

/-- The character for a 6-bit value. -/
def b64Char (v : Nat) : Nat :=
  let v := v % 64
  if v < 26 then 65 + v else if v < 52 then 71 + v else if v < 62 then v - 4 else if v = 62 then 43 else 47

/-- The 6-bit value of a character, or `none` if it isn't in the alphabet. -/
def b64Value (c : Nat) : Option Nat :=
  if 65 ≤ c ∧ c ≤ 90 then some (c - 65)
  else if 97 ≤ c ∧ c ≤ 122 then some (c - 71)
  else if 48 ≤ c ∧ c ≤ 57 then some (c + 4)
  else if c = 43 then some 62
  else if c = 47 then some 63
  else none

/-- The padding character `=`. -/
def b64Pad : Nat := 61

/-- The standard padded base64 encoding of `data`. -/
def base64Encode : Bytes → Bytes
  | a :: b :: c :: rest =>
    let bits := a * 2 ^ 16 + b * 2 ^ 8 + c
    [b64Char (bits / 2 ^ 18), b64Char (bits / 2 ^ 12), b64Char (bits / 2 ^ 6), b64Char bits] ++
      base64Encode rest
  | [a, b] =>
    let bits := a * 2 ^ 16 + b * 2 ^ 8
    [b64Char (bits / 2 ^ 18), b64Char (bits / 2 ^ 12), b64Char (bits / 2 ^ 6), b64Pad]
  | [a] =>
    let bits := a * 2 ^ 16
    [b64Char (bits / 2 ^ 18), b64Char (bits / 2 ^ 12), b64Pad, b64Pad]
  | [] => []

/-- One group of four characters, with `pad` of them padding: the bytes it
holds, or `none` if a character isn't in the alphabet or the bits the
padding drops aren't zero. -/
def b64Group (c0 c1 c2 c3 pad : Nat) : Option Bytes := do
  let v0 ← b64Value c0
  let v1 ← b64Value c1
  let v2 ← if pad ≥ 2 then some 0 else b64Value c2
  let v3 ← if pad ≥ 1 then some 0 else b64Value c3
  let bits := ((v0 * 64 + v1) * 64 + v2) * 64 + v3
  let bytes := [bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256]
  require ((bytes.drop (3 - pad)).all (· == 0))
  pure (bytes.take (3 - pad))

/-- Decodes canonical base64 text, or `none`. -/
def base64Decode : Bytes → Option Bytes
  | [] => some []
  | [c0, c1, c2, c3] =>
    let pad := if c2 = b64Pad ∧ c3 = b64Pad then 2 else if c3 = b64Pad then 1 else 0
    b64Group c0 c1 c2 c3 pad
  | c0 :: c1 :: c2 :: c3 :: rest@(_ :: _) => do
    let g ← b64Group c0 c1 c2 c3 0
    pure (g ++ (← base64Decode rest))
  | _ => none

end C3
