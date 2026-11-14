import C3BootProofs.Spec.Sha256

/-!
# SHA-512

SHA-512 as FIPS 180-4 defines it, over bytes as natural numbers below 256.
Words are `BitVec 64`. The constants are the ones section 4.2.3 and
section 5.3.5 list: the first 64 bits of the fractional parts of the cube
roots of the first 80 primes, and of the square roots of the first 8.
-/

namespace C3

namespace Sha512

/-- A 64-bit word. -/
abbrev W64 := BitVec 64

def rotr (x : W64) (n : Nat) : W64 := x.rotateRight n

def ch (x y z : W64) : W64 := (x &&& y) ^^^ (~~~x &&& z)

def maj (x y z : W64) : W64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSigma0 (x : W64) : W64 := rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39

def bigSigma1 (x : W64) : W64 := rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41

def smallSigma0 (x : W64) : W64 := rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)

def smallSigma1 (x : W64) : W64 := rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6)

/-- The round constants, section 4.2.3. -/
def k : Array W64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- The initial hash value, section 5.3.5. -/
def h0 : List W64 := [
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The big-endian word in bytes `8 * i` to `8 * i + 7` of a block. -/
def wordAt (block : Bytes) (i : Nat) : W64 :=
  BitVec.ofNat 64 ((List.range 8).foldl (fun acc j => acc * 256 + block.getD (8 * i + j) 0) 0)

/-- The message schedule `W₀` to `W₇₉`, section 6.4.2 step 1. -/
def schedule (block : Bytes) : Array W64 :=
  (List.range 64).foldl (fun w t =>
      let t := t + 16
      w.push (smallSigma1 w[t - 2]! + w[t - 7]! + smallSigma0 w[t - 15]! + w[t - 16]!))
    ((List.range 16).toArray.map (wordAt block))

/-- One round of section 6.4.2 step 3, on the working variables `a` to `h`. -/
def round (w : Array W64) (v : List W64) (t : Nat) : List W64 :=
  match v with
  | [a, b, c, d, e, f, g, h] =>
    let t1 := h + bigSigma1 e + ch e f g + k[t]! + w[t]!
    let t2 := bigSigma0 a + maj a b c
    [t1 + t2, a, b, c, d + t1, e, f, g]
  | _ => v

/-- The hash value after one 128-byte block, section 6.4.2. -/
def compress (hv : List W64) (block : Bytes) : List W64 :=
  let w := schedule block
  let v := (List.range 80).foldl (round w) hv
  List.zipWith (· + ·) hv v

/-- The 16 bytes of `n` as a big-endian 128-bit integer. -/
def be128 (n : Nat) : Bytes := (List.range 16).reverse.map fun i => n / 2 ^ (8 * i) % 256

/-- The padded message, section 5.1.2: the message, the byte 0x80, zero
bytes to 112 modulo 128, and the message's length in bits. -/
def pad (msg : Bytes) : Bytes :=
  msg ++ [0x80] ++ List.replicate ((239 - msg.length % 128) % 128) 0 ++ be128 (8 * msg.length)

/-- The 128-byte blocks of `bytes`, at most `fuel` of them. -/
def blocks : Nat → Bytes → List Bytes
  | 0, _ => []
  | n + 1, bytes => if bytes.isEmpty then [] else bytes.take 128 :: blocks n (bytes.drop 128)

/-- The 8 bytes of a word, big-endian. -/
def wordBytes (x : W64) : Bytes := (List.range 8).reverse.map fun i => x.toNat / 2 ^ (8 * i) % 256

end Sha512

open Sha512 in
/-- The SHA-512 digest of `msg`, 64 bytes. -/
def sha512 (msg : Bytes) : Bytes :=
  let p := pad msg
  ((blocks p.length p).foldl compress h0).flatMap wordBytes

/-- SHA-384's initial hash value, section 5.3.4. -/
def Sha512.h0384 : List Sha512.W64 := [
  0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
  0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4]

open Sha512 in
/-- The SHA-384 digest of `msg`, 48 bytes: SHA-512's computation from
SHA-384's initial hash value, truncated (section 6.5). -/
def sha384 (msg : Bytes) : Bytes :=
  let p := pad msg
  (((blocks p.length p).foldl compress h0384).flatMap wordBytes).take 48

end C3

/-! The examples from FIPS 180-2 appendix C, and the empty message. -/

#guard C3.sha512 [] =
  [0xcf, 0x83, 0xe1, 0x35, 0x7e, 0xef, 0xb8, 0xbd, 0xf1, 0x54, 0x28, 0x50, 0xd6, 0x6d, 0x80, 0x07, 0xd6, 0x20,
    0xe4, 0x05, 0x0b, 0x57, 0x15, 0xdc, 0x83, 0xf4, 0xa9, 0x21, 0xd3, 0x6c, 0xe9, 0xce, 0x47, 0xd0, 0xd1,
    0x3c, 0x5d, 0x85, 0xf2, 0xb0, 0xff, 0x83, 0x18, 0xd2, 0x87, 0x7e, 0xec, 0x2f, 0x63, 0xb9, 0x31, 0xbd,
    0x47, 0x41, 0x7a, 0x81, 0xa5, 0x38, 0x32, 0x7a, 0xf9, 0x27, 0xda, 0x3e]

#guard C3.sha512 [0x61, 0x62, 0x63] =
  [0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba, 0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31, 0x12, 0xe6,
    0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2, 0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a, 0x21, 0x92, 0x99,
    0x2a, 0x27, 0x4f, 0xc1, 0xa8, 0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd, 0x45, 0x4d, 0x44, 0x23,
    0x64, 0x3c, 0xe8, 0x0e, 0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f]

#guard C3.sha512 ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toList.map Char.toNat) =
  [0x8e, 0x95, 0x9b, 0x75, 0xda, 0xe3, 0x13, 0xda, 0x8c, 0xf4, 0xf7, 0x28, 0x14, 0xfc, 0x14, 0x3f, 0x8f, 0x77,
    0x79, 0xc6, 0xeb, 0x9f, 0x7f, 0xa1, 0x72, 0x99, 0xae, 0xad, 0xb6, 0x88, 0x90, 0x18, 0x50, 0x1d, 0x28,
    0x9e, 0x49, 0x00, 0xf7, 0xe4, 0x33, 0x1b, 0x99, 0xde, 0xc4, 0xb5, 0x43, 0x3a, 0xc7, 0xd3, 0x29, 0xee,
    0xb6, 0xdd, 0x26, 0x54, 0x5e, 0x96, 0xe5, 0x5b, 0x87, 0x4b, 0xe9, 0x09]

#guard C3.sha384 [0x61, 0x62, 0x63] =
  [0xcb, 0x00, 0x75, 0x3f, 0x45, 0xa3, 0x5e, 0x8b, 0xb5, 0xa0, 0x3d, 0x69, 0x9a, 0xc6, 0x50, 0x07, 0x27, 0x2c,
    0x32, 0xab, 0x0e, 0xde, 0xd1, 0x63, 0x1a, 0x8b, 0x60, 0x5a, 0x43, 0xff, 0x5b, 0xed, 0x80, 0x86, 0x07,
    0x2b, 0xa1, 0xe7, 0xcc, 0x23, 0x58, 0xba, 0xec, 0xa1, 0x34, 0xc8, 0x25, 0xa7]
