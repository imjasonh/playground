import C3BootProofs.Spec.Ecdsa

/-!
# Ed25519

Signature verification as `c3_crypto::ed25519_verify` defines it: RFC 8032
section 5.1.7 without the cofactor, with the strict rules
`docs/esp32c3-verified-ota-plan.md` adds: `S` below the group order `L`,
and `A` and `R` canonical encodings of points that don't have small order.
Points are affine `(x, y)` on the twisted Edwards curve
`-x² + y² = 1 + d x² y²` modulo `p = 2^255 - 19`.
-/

namespace C3

namespace Ed25519

def p : Nat := 2 ^ 255 - 19

/-- The order of the base point. -/
def L : Nat := 2 ^ 252 + 27742317777372353535851937790883648493

def inv (x : Nat) : Nat := powMod x (p - 2) p

/-- `-121665 / 121666`. -/
def d : Nat := (p - 121665) * inv 121666 % p

/-- A square root of -1. -/
def sqrtM1 : Nat := powMod 2 ((p - 1) / 4) p

/-- The sum of two points (the curve's complete addition law). -/
def add (a b : Nat × Nat) : Nat × Nat :=
  let (x1, y1) := a
  let (x2, y2) := b
  let t := d * x1 % p * x2 % p * y1 % p * y2 % p
  ((x1 * y2 + y1 * x2) % p * inv ((1 + t) % p) % p,
    (y1 * y2 + x1 * x2) % p * inv ((1 + p - t) % p) % p)

/-- The neutral element. -/
def zero : Nat × Nat := (0, 1)

/-- `k` times a point. -/
def mul (k : Nat) (q : Nat × Nat) : Nat × Nat :=
  if k = 0 then zero
  else
    let h := mul (k / 2) q
    let d2 := add h h
    if k % 2 = 1 then add d2 q else d2
termination_by k
decreasing_by omega

/-- Little-endian bytes as a number. -/
def leNum (b : Bytes) : Nat := b.foldr (fun x acc => x + 256 * acc) 0

/-- The `x` with sign bit `sign` on the curve at `y`, or `none` if there is
none (RFC 8032 section 5.1.3). -/
def recoverX (y sign : Nat) : Option Nat := do
  let u := (y * y + p - 1) % p
  let v := (d * y % p * y + 1) % p
  let x := u * powMod v 3 p % p * powMod (u * powMod v 7 p % p) ((p - 5) / 8) p % p
  let x ← if v * x % p * x % p == u then some x
    else if v * x % p * x % p == (p - u) % p then some (x * sqrtM1 % p) else none
  require !(x == 0 && sign == 1)
  pure (if x % 2 == sign then x else p - x)

/-- The point a 32-byte encoding names, if the encoding is canonical: `y`
below `p`, and the sign bit clear when `x` is 0. -/
def decode (enc : Bytes) : Option (Nat × Nat) := do
  require (enc.length == 32)
  let n := leNum enc
  let y := n % 2 ^ 255
  let sign := n / 2 ^ 255
  require (y < p)
  let x ← recoverX y sign
  pure (x, y)

/-- The base point: `y = 4/5`, `x` even. -/
def B : Nat × Nat :=
  let y := 4 * inv 5 % p
  ((recoverX y 0).getD 0, y)

/-- Whether a point has small order: eight times it is the neutral element. -/
def smallOrder (q : Nat × Nat) : Bool := mul 8 q == zero

end Ed25519

open Ed25519 in
/-- `c3_crypto::ed25519_verify`. -/
def ed25519Verify (publicKey message signature : Bytes) : Bool :=
  match decode publicKey, decode (signature.take 32) with
  | some a, some r =>
    let s := leNum (signature.drop 32)
    signature.length == 64 && s < L && !smallOrder a && !smallOrder r &&
      let k := leNum (sha512 (signature.take 32 ++ publicKey ++ message)) % L
      mul s B == add r (mul k a)
  | _, _ => false

end C3

/-! RFC 8032 section 7.1, test 1: the empty message. -/

#guard C3.ed25519Verify
  [0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07, 0x3a,
    0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07, 0x51, 0x1a] []
  [0xe5, 0x56, 0x43, 0x00, 0xc3, 0x60, 0xac, 0x72, 0x90, 0x86, 0xe2, 0xcc, 0x80, 0x6e, 0x82, 0x8a,
    0x84, 0x87, 0x7f, 0x1e, 0xb8, 0xe5, 0xd9, 0x74, 0xd8, 0x73, 0xe0, 0x65, 0x22, 0x49, 0x01, 0x55,
    0x5f, 0xb8, 0x82, 0x15, 0x90, 0xa3, 0x3b, 0xac, 0xc6, 0x1e, 0x39, 0x70, 0x1c, 0xf9, 0xb4, 0x6b,
    0xd2, 0x5b, 0xf5, 0xf0, 0x59, 0x5b, 0xbe, 0x24, 0x65, 0x51, 0x41, 0x43, 0x8e, 0x7a, 0x10, 0x0b]
