import C3BootProofs.Spec.Formats

/-!
# ASN.1 times

`UTCTime` and `GeneralizedTime` contents as `c3_verify::time` reads them,
as seconds since the Unix epoch. Times before 1970 are rejected.
-/

namespace C3

/-- `n` ASCII decimal digits from the front, as a number. -/
def readDigits : Nat → Bytes → Option (Nat × Bytes)
  | 0, rest => some (0, rest)
  | n + 1, b :: rest => do
    require (48 ≤ b && b ≤ 57)
    let (v, rest) ← readDigits n rest
    pure ((b - 48) * 10 ^ n + v, rest)
  | _ + 1, [] => none

def isLeapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysInMonth (y m : Nat) : Nat :=
  if m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 8 ∨ m = 10 ∨ m = 12 then 31
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30
  else if m = 2 then (if isLeapYear y then 29 else 28)
  else 0

/-- Days from 1970-01-01 to a valid date in 1970 or later (Howard Hinnant's
`days_from_civil`). -/
def daysFromCivil (year month day : Nat) : Nat :=
  let y := if month ≤ 2 then year - 1 else year
  let era := y / 400
  let yoe := y % 400
  let mp := if month > 2 then month - 3 else month + 9
  let doy := (153 * mp + 2) / 5 + day - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- `MMDDHHMMSS` after a year, as seconds since the epoch. -/
def readDateTime (year : Nat) (bytes : Bytes) : Option (Nat × Bytes) := do
  let (month, bytes) ← readDigits 2 bytes
  let (day, bytes) ← readDigits 2 bytes
  let (hour, bytes) ← readDigits 2 bytes
  let (minute, bytes) ← readDigits 2 bytes
  let (second, bytes) ← readDigits 2 bytes
  require (year ≥ 1970 && 1 ≤ month && month ≤ 12 && 1 ≤ day && day ≤ daysInMonth year month &&
    hour ≤ 23 && minute ≤ 59 && second ≤ 59)
  pure (daysFromCivil year month day * 86400 + hour * 3600 + minute * 60 + second, bytes)

/-- The `Z` that ends a time. -/
def asciiZ : Nat := 0x5A

/-- A `UTCTime`, `YYMMDDHHMMSSZ`: years 50 to 99 are 1950 to 1999, and 00 to
49 are 2000 to 2049. -/
def utcTime (content : Bytes) : Option Nat := do
  let (yy, rest) ← readDigits 2 content
  let (t, rest) ← readDateTime (yy + if yy ≥ 50 then 1900 else 2000) rest
  require (rest == [asciiZ])
  pure t

/-- A `GeneralizedTime`, `YYYYMMDDHHMMSSZ` or `YYYYMMDDHHMMSS.fZ` with one or
more fraction digits not ending in `0`. The fraction is dropped. -/
def generalizedTime (content : Bytes) : Option Nat := do
  let (year, rest) ← readDigits 4 content
  let (t, rest) ← readDateTime year rest
  match rest with
  | [0x5A] => pure t
  | 0x2E :: fz =>
    match fz.reverse with
    | 0x5A :: frac =>
      require (!frac.isEmpty && frac.all (fun d => 48 ≤ d && d ≤ 57) && frac.head? != some 48)
      pure t
    | _ => none
  | _ => none

end C3
