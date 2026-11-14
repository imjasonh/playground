/-!
Hex text for the differential harnesses: `decode-check` and
`sigstore-check` read inputs as hex and print results as hex.
-/

namespace C3

/-- The value of an ASCII hex digit, `0`-`9` or `a`-`f`. -/
def hexDigit (c : Nat) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else none

def parseHex : List Nat → Option (List Nat)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexDigit a
    let lo ← hexDigit b
    pure ((16 * hi + lo) :: (← parseHex rest))
  | [_] => none

/-- Hex bytes, with `-` for none. -/
def parseHexTok (s : String) : Option (List Nat) :=
  if s = "-" then some [] else parseHex (s.toUTF8.data.toList.map UInt8.toNat)

def hexStr (b : List Nat) : String :=
  if b.isEmpty then "-"
  else String.join (b.map fun x => String.ofList ((Nat.toDigits 16 (256 + x)).drop 1))

end C3
