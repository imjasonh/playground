import C3BootProofs.Spec.Formats

/-!
# SHA-256

SHA-256 as FIPS 180-4 defines it, over bytes as natural numbers below 256.
Words are `BitVec 32`, the type the machine model's registers hold.
-/

namespace C3

namespace Sha256

/-- A 32-bit word. -/
abbrev W32 := BitVec 32

def rotr (x : W32) (n : Nat) : W32 := x.rotateRight n

def ch (x y z : W32) : W32 := (x &&& y) ^^^ (~~~x &&& z)

def maj (x y z : W32) : W32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSigma0 (x : W32) : W32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

def bigSigma1 (x : W32) : W32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

def smallSigma0 (x : W32) : W32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

def smallSigma1 (x : W32) : W32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The round constants, section 4.2.2. -/
def k : Array W32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value, section 5.3.3. -/
def h0 : List W32 :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The big-endian word in bytes `4 * i` to `4 * i + 3` of a block. -/
def wordAt (block : Bytes) (i : Nat) : W32 :=
  BitVec.ofNat 32 (block.getD (4 * i) 0 * 2 ^ 24 + block.getD (4 * i + 1) 0 * 2 ^ 16 +
    block.getD (4 * i + 2) 0 * 2 ^ 8 + block.getD (4 * i + 3) 0)

/-- The message schedule `W₀` to `W₆₃`, section 6.2.2 step 1. -/
def schedule (block : Bytes) : Array W32 :=
  (List.range 48).foldl (fun w t =>
      let t := t + 16
      w.push (smallSigma1 w[t - 2]! + w[t - 7]! + smallSigma0 w[t - 15]! + w[t - 16]!))
    ((List.range 16).toArray.map (wordAt block))

/-- One round of section 6.2.2 step 3, on the working variables `a` to `h`. -/
def round (w : Array W32) (v : List W32) (t : Nat) : List W32 :=
  match v with
  | [a, b, c, d, e, f, g, h] =>
    let t1 := h + bigSigma1 e + ch e f g + k[t]! + w[t]!
    let t2 := bigSigma0 a + maj a b c
    [t1 + t2, a, b, c, d + t1, e, f, g]
  | _ => v

/-- The hash value after one 64-byte block, section 6.2.2. -/
def compress (hv : List W32) (block : Bytes) : List W32 :=
  let w := schedule block
  let v := (List.range 64).foldl (round w) hv
  List.zipWith (· + ·) hv v

/-- The 8 bytes of `n` as a big-endian 64-bit integer. -/
def be64 (n : Nat) : Bytes := (List.range 8).reverse.map fun i => n / 2 ^ (8 * i) % 256

/-- The padded message, section 5.1.1: the message, the byte 0x80, zero
bytes to 56 modulo 64, and the message's length in bits. -/
def pad (msg : Bytes) : Bytes :=
  msg ++ [0x80] ++ List.replicate ((119 - msg.length % 64) % 64) 0 ++ be64 (8 * msg.length)

/-- The 64-byte blocks of `bytes`, at most `fuel` of them. -/
def blocks : Nat → Bytes → List Bytes
  | 0, _ => []
  | n + 1, bytes => if bytes.isEmpty then [] else bytes.take 64 :: blocks n (bytes.drop 64)

/-- The 4 bytes of a word, big-endian. -/
def wordBytes (x : W32) : Bytes := [x.toNat / 2 ^ 24, x.toNat / 2 ^ 16 % 256, x.toNat / 2 ^ 8 % 256, x.toNat % 256]

end Sha256

open Sha256 in
/-- The SHA-256 digest of `msg`, 32 bytes. -/
def sha256 (msg : Bytes) : Bytes :=
  let p := pad msg
  ((blocks p.length p).foldl compress h0).flatMap wordBytes

end C3

/-! The examples from FIPS 180-2 appendix B. -/

#guard C3.sha256 [] = [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f,
  0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55]

#guard C3.sha256 [0x61, 0x62, 0x63] = [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde,
  0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00,
  0x15, 0xad]

#guard C3.sha256 ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toList.map Char.toNat) =
  [0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8, 0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39, 0xa3, 0x3c,
    0xe4, 0x59, 0x64, 0xff, 0x21, 0x67, 0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1]
