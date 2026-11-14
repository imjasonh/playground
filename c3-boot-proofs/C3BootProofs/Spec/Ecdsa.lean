import C3BootProofs.Spec.Sha512

/-!
# ECDSA over P-256 and P-384

Signature verification as `c3_crypto::p256_verify_prehash` and
`p384_verify_prehash` define it: FIPS 186-5's verification over the curve's
affine points, with the digest used as given (`prehash`), and the rules
`c3-boot/docs/formats.md` adds: `r` and `s` in 1 through `n - 1`, and the
key an uncompressed point on the curve. The arithmetic is on natural
numbers modulo the field prime or the group order.
-/

namespace C3

/-- Big-endian bytes as a number. -/
def beNat (b : Bytes) : Nat := b.foldl (fun acc x => acc * 256 + x) 0

/-- `a ^ e` modulo `m`, by repeated squaring. -/
def powMod (a e m : Nat) : Nat :=
  if e = 0 then 1 % m
  else
    let r := powMod (a * a % m) (e / 2) m
    if e % 2 = 1 then r * a % m else r
termination_by e
decreasing_by omega

/-- A short Weierstrass curve `y² = x³ + a x + b` over the prime field of
order `p`, with a base point `(gx, gy)` of prime order `n`. -/
structure Curve where
  p : Nat
  a : Nat
  b : Nat
  n : Nat
  gx : Nat
  gy : Nat
  /-- The bytes in a field element and in a scalar. -/
  size : Nat

/-- An affine point, or `none` for the point at infinity. -/
abbrev ECPoint := Option (Nat × Nat)

namespace Curve

/-- The inverse of a nonzero `x` modulo the prime `p`. -/
def inv (c : Curve) (x : Nat) : Nat := powMod x (c.p - 2) c.p

/-- The sum of two points. -/
def add (c : Curve) : ECPoint → ECPoint → ECPoint
  | none, q => q
  | q, none => q
  | some (x1, y1), some (x2, y2) =>
    let p := c.p
    if x1 = x2 then
      if (y1 + y2) % p = 0 then none
      else
        let l := (3 * x1 * x1 + c.a) * c.inv (2 * y1 % p) % p
        let x3 := (l * l + 2 * p - 2 * x1) % p
        some (x3, (l * (x1 + p - x3) + p - y1) % p)
    else
      let l := (y2 + p - y1) * c.inv ((x2 + p - x1) % p) % p
      let x3 := (l * l + 2 * p - x1 - x2) % p
      some (x3, (l * (x1 + p - x3) + p - y1) % p)

/-- `k` times a point. -/
def mul (c : Curve) (k : Nat) (q : ECPoint) : ECPoint :=
  if k = 0 then none
  else
    let h := c.mul (k / 2) q
    let d := c.add h h
    if k % 2 = 1 then c.add d q else d
termination_by k
decreasing_by omega

/-- The point an uncompressed SEC 1 encoding names: `0x04`, then `x` and
`y` big-endian, each below `p`, on the curve. -/
def decodePoint (c : Curve) (bytes : Bytes) : Option (Nat × Nat) := do
  require (bytes.length == 1 + 2 * c.size && bytes.head? == some 0x04)
  let x := beNat ((bytes.drop 1).take c.size)
  let y := beNat (bytes.drop (1 + c.size))
  require (x < c.p && y < c.p && (y * y) % c.p == (x * x % c.p * x + c.a * x + c.b) % c.p)
  pure (x, y)

/-- The scalar a digest names: its first `size` bytes, big-endian, modulo
`n`. -/
def digestScalar (c : Curve) (prehash : Bytes) : Nat := beNat (prehash.take c.size) % c.n

/-- Whether `(r, s)` is a valid signature by the key `point` on the digest
`prehash`. -/
def verify (c : Curve) (point prehash r s : Bytes) : Bool :=
  match c.decodePoint point with
  | none => false
  | some q =>
    let r' := beNat r
    let s' := beNat s
    r.length == c.size && s.length == c.size && 1 ≤ r' && r' < c.n && 1 ≤ s' && s' < c.n &&
      let w := powMod s' (c.n - 2) c.n
      let u1 := c.digestScalar prehash * w % c.n
      let u2 := r' * w % c.n
      match c.add (c.mul u1 (some (c.gx, c.gy))) (c.mul u2 (some q)) with
      | none => false
      | some (x, _) => x % c.n == r'

end Curve

/-- NIST P-256 (FIPS 186-5 and SEC 2). -/
def p256 : Curve where
  p := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  a := 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
  b := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  n := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  gx := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
  gy := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
  size := 32

/-- NIST P-384 (FIPS 186-5 and SEC 2). -/
def p384 : Curve where
  p := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
  a := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffc
  b := 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
  n := 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
  gx := 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
  gy := 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
  size := 48

/-- `c3_crypto::p256_verify_prehash`. -/
def p256Verify (point prehash r s : Bytes) : Bool := p256.verify point prehash r s

/-- `c3_crypto::p384_verify_prehash`. -/
def p384Verify (point prehash r s : Bytes) : Bool := p384.verify point prehash r s

end C3

/-! The base points are on their curves and have the stated order. -/

#guard C3.p256.decodePoint (0x04 :: (List.range 32).reverse.map (fun i => C3.p256.gx / 2 ^ (8 * i) % 256) ++
  (List.range 32).reverse.map (fun i => C3.p256.gy / 2 ^ (8 * i) % 256)) == some (C3.p256.gx, C3.p256.gy)
#guard C3.p256.mul C3.p256.n (some (C3.p256.gx, C3.p256.gy)) == none
#guard C3.p384.mul C3.p384.n (some (C3.p384.gx, C3.p384.gy)) == none
