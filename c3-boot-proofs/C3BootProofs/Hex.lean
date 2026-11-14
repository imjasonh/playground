/-!
Hex text for the differential harnesses: `decode-check` and
`sigstore-check` read inputs as hex and print results as hex.
-/

namespace C3

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def parseHex : List Char → Option (List Nat)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexDigit a
    let lo ← hexDigit b
    pure ((16 * hi + lo) :: (← parseHex rest))
  | [_] => none

/-- Hex bytes, with `-` for none. -/
def parseHexTok (s : String) : Option (List Nat) := if s = "-" then some [] else parseHex s.toList

def hexStr (b : List Nat) : String :=
  if b.isEmpty then "-"
  else String.join (b.map fun x => String.ofList ((Nat.toDigits 16 (256 + x)).drop 1))

end C3
