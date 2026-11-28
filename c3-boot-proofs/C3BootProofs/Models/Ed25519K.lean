import C3BootProofs.Models.Ed25519KSub
import C3BootProofs.Models.Ed25519KPack
import C3BootProofs.Models.Ed25519KDigest
import C3BootProofs.Models.Ed25519KAdd
import C3BootProofs.Image.BootloaderData7

/-!
# The challenge scalar's reduction

`kOK` proves `KOK M` for any memory that holds the two Montgomery constants
`from_bytes_wide` reads (`KImage`): `R = 2^261 mod L` at `edMontRAddress` and
`R² = 2^522 mod L` at `edMontRRAddress`, each as nine 32-bit limbs of 29 bits.
-/

namespace C3.RV32.EdK

open C3.RV32 C3.RV32.EdM C3.Image

/-- `R = 2^261 mod L`, nine little-endian 32-bit limbs. -/
def edRData : List Nat :=
  [237, 249, 77, 17, 3, 115, 97, 26, 140, 9, 124, 15, 103, 49, 121, 22, 110, 101, 253, 31, 255, 255, 255, 31, 255,
    255, 255, 31, 255, 255, 255, 31, 255, 255, 15, 0]

/-- `R² = 2^522 mod L`, nine little-endian 32-bit limbs. -/
def edRRData : List Nat :=
  [18, 157, 95, 11, 23, 27, 20, 30, 61, 127, 141, 21, 87, 55, 63, 20, 129, 215, 114, 25, 124, 235, 47, 4, 61, 199,
    238, 28, 30, 77, 24, 30, 109, 4, 5, 0]

/-- The constants `from_bytes_wide` reads. -/
structure KImage (M : Word → BitVec 8) : Prop where
  r : memBytes M (BitVec.ofNat 32 (img% edMontRAddress)) 36 = edRData
  rr : memBytes M (BitVec.ofNat 32 (img% edMontRRAddress)) 36 = edRRData

theorem limbAt_bytes36 (M : Word → BitVec 8) (a : Word) {i : Nat} (hi : i < 9) :
    limbAt M a i = le32 ((memBytes M a 36).getD (4 * i) 0) ((memBytes M a 36).getD (4 * i + 1) 0)
      ((memBytes M a 36).getD (4 * i + 2) 0) ((memBytes M a 36).getD (4 * i + 3) 0) := by
  unfold limbAt
  rw [memLoad32_toNat, memBytes_getD (by omega), memBytes_getD (by omega), memBytes_getD (by omega),
    memBytes_getD (by omega), show (1 : Word) = BitVec.ofNat 32 1 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]

theorem smmIn_data {M : Word → BitVec 8} {a : Word} {data : List Nat} (h : memBytes M a 36 = data) {i : Nat}
    (hi : i < 9) :
    smmIn M a i = le32 (data.getD (4 * i) 0) (data.getD (4 * i + 1) 0) (data.getD (4 * i + 2) 0)
      (data.getD (4 * i + 3) 0) := by
  unfold smmIn
  simp only [hi, ↓reduceIte]
  rw [limbAt_bytes36 M a hi, h]

theorem smmIn_const {M : Word → BitVec 8} {a : Word} {data : List Nat} (h : memBytes M a 36 = data) (v : Nat)
    (hl : ∀ i, i < 9 → le32 (data.getD (4 * i) 0) (data.getD (4 * i + 1) 0) (data.getD (4 * i + 2) 0)
      (data.getD (4 * i + 3) 0) < 2 ^ 29)
    (hv : le32 (data.getD 0 0) (data.getD 1 0) (data.getD 2 0) (data.getD 3 0) +
      2 ^ 29 * le32 (data.getD 4 0) (data.getD 5 0) (data.getD 6 0) (data.getD 7 0) +
      2 ^ 58 * le32 (data.getD 8 0) (data.getD 9 0) (data.getD 10 0) (data.getD 11 0) +
      2 ^ 87 * le32 (data.getD 12 0) (data.getD 13 0) (data.getD 14 0) (data.getD 15 0) +
      2 ^ 116 * le32 (data.getD 16 0) (data.getD 17 0) (data.getD 18 0) (data.getD 19 0) +
      2 ^ 145 * le32 (data.getD 20 0) (data.getD 21 0) (data.getD 22 0) (data.getD 23 0) +
      2 ^ 174 * le32 (data.getD 24 0) (data.getD 25 0) (data.getD 26 0) (data.getD 27 0) +
      2 ^ 203 * le32 (data.getD 28 0) (data.getD 29 0) (data.getD 30 0) (data.getD 31 0) +
      2 ^ 232 * le32 (data.getD 32 0) (data.getD 33 0) (data.getD 34 0) (data.getD 35 0) = v) :
    (∀ i, i < 9 → smmIn M a i < 2 ^ 29) ∧ sv9 (smmIn M a) = v := by
  refine ⟨fun i hi => by rw [smmIn_data h hi]; exact hl i hi, ?_⟩
  unfold sv9
  rw [smmIn_data h (show 0 < 9 by decide), smmIn_data h (show 1 < 9 by decide), smmIn_data h (show 2 < 9 by decide),
    smmIn_data h (show 3 < 9 by decide), smmIn_data h (show 4 < 9 by decide), smmIn_data h (show 5 < 9 by decide),
    smmIn_data h (show 6 < 9 by decide), smmIn_data h (show 7 < 9 by decide), smmIn_data h (show 8 < 9 by decide)]
  exact hv

theorem KImage.rLimbs {M : Word → BitVec 8} (K : KImage M) :
    (∀ i, i < 9 → smmIn M (BitVec.ofNat 32 (img% edMontRAddress)) i < 2 ^ 29) ∧
      sv9 (smmIn M (BitVec.ofNat 32 (img% edMontRAddress))) =
        7237005577332262213973186563042994226653049657365262595645758789353026222573 :=
  smmIn_const K.r _ (by decide) (by decide)

theorem KImage.rrLimbs {M : Word → BitVec 8} (K : KImage M) :
    (∀ i, i < 9 → smmIn M (BitVec.ofNat 32 (img% edMontRRAddress)) i < 2 ^ 29) ∧
      sv9 (smmIn M (BitVec.ofNat 32 (img% edMontRRAddress))) =
        2269390412388210757387596145591141548687583832901957660833925789855294397714 :=
  smmIn_const K.rr _ (by decide) (by decide)

set_option exponentiation.threshold 600 in
theorem cancel261 {a b : Nat} (h : 2 ^ 261 * a % Ed25519.L = 2 ^ 261 * b % Ed25519.L) :
    a % Ed25519.L = b % Ed25519.L := by
  have hI : 2 ^ 261 * 2853205326802785441228897529650942859810315295445226391519200280554739541986 =
      1 + 1460841127323026145909195535181282744217281446807063794674545094323019697126939 * Ed25519.L := by
    unfold Ed25519.L; rfl
  have e : ∀ x, x % Ed25519.L =
      2 ^ 261 * x * 2853205326802785441228897529650942859810315295445226391519200280554739541986 % Ed25519.L := by
    intro x
    rw [Nat.mul_comm (2 ^ 261) x, Nat.mul_assoc, hI, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
      Nat.add_mul_mod_self_right]
  rw [e a, e b, Nat.mul_mod, h, ← Nat.mul_mod]

set_option exponentiation.threshold 600 in
theorem kmod {lo hi X Y N1 N2 : Nat}
    (h1 : 2 ^ 261 * X =
      hi * 2269390412388210757387596145591141548687583832901957660833925789855294397714 + N1 * Ed25519.L)
    (h2 : 2 ^ 261 * Y =
      lo * 7237005577332262213973186563042994226653049657365262595645758789353026222573 + N2 * Ed25519.L) :
    (X % Ed25519.L + Y % Ed25519.L) % Ed25519.L = (lo + 2 ^ 261 * hi) % Ed25519.L := by
  have hR : 2 ^ 261 = 7237005577332262213973186563042994226653049657365262595645758789353026222573 +
      511 * Ed25519.L := by
    unfold Ed25519.L; rfl
  have hRR : 2 ^ 522 = 2269390412388210757387596145591141548687583832901957660833925789855294397714 +
      1897137590064188545819787018382342682260702946610423502977170686005395312870190310 * Ed25519.L := by
    unfold Ed25519.L; rfl
  rw [← Nat.add_mod]
  apply cancel261
  have e1 : 2 ^ 261 * (X + Y) =
      hi * 2269390412388210757387596145591141548687583832901957660833925789855294397714 +
        lo * 7237005577332262213973186563042994226653049657365262595645758789353026222573 +
        (N1 + N2) * Ed25519.L := by
    rw [Nat.mul_add, h1, h2, Nat.add_mul]
    omega
  have e2 : 2 ^ 261 * (lo + 2 ^ 261 * hi) =
      hi * 2269390412388210757387596145591141548687583832901957660833925789855294397714 +
        lo * 7237005577332262213973186563042994226653049657365262595645758789353026222573 +
        (lo * 511 + hi * 1897137590064188545819787018382342682260702946610423502977170686005395312870190310) *
          Ed25519.L := by
    rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]
    rw [show 261 + 261 = 522 from rfl, hRR, hR]
    generalize Ed25519.L = L
    ring_eq
  rw [e1, e2, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]

theorem L_lt : Ed25519.L < 2 ^ 253 := by unfold Ed25519.L; omega

set_option exponentiation.threshold 600 in
set_option maxHeartbeats 4000000 in
/-- `from_bytes_wide` reduces a SHA-512 digest modulo `L`, given the constants
`R` and `R²` in memory. -/
theorem kOK {M : Word → BitVec 8} (K : KImage M) : KOK M := by
  intro m
  have hB := sha512_byt m
  have hl := sha512_length m
  have hm : ∀ b, leL (sha512 m) b 4 % 2 ^ 32 = leL (sha512 m) b 4 := fun b => Nat.mod_eq_of_lt (leL4_lt hB b)
  obtain ⟨hRl, hRv⟩ := K.rLimbs
  obtain ⟨hRRl, hRRv⟩ := K.rrLimbs
  have hL := L_lt
  unfold kOf
  obtain ⟨hlo, hhi⟩ := split_lt (w := fun t => leL (sha512 m) (4 * t) 4 % 2 ^ 32) (Nat.mod_lt _ (by decide))
  have hs := split_val (w := fun t => leL (sha512 m) (4 * t) 4 % 2 ^ 32) (fun _ _ => Nat.mod_lt _ (by decide))
  generalize (fun t => leL (sha512 m) (4 * t) 4 % 2 ^ 32) = w at hlo hhi hs ⊢
  simp only [hm, Nat.reduceMul] at hs
  rw [leNum64 hl, ← hs]
  obtain ⟨hXl, hXv, N1, hX⟩ := smm_val hhi hRRl (by rw [hRRv]; unfold Ed25519.L; omega)
  obtain ⟨hYl, hYv, N2, hY⟩ := smm_val hlo hRl (by rw [hRv]; unfold Ed25519.L; omega)
  rw [hRRv] at hX
  rw [hRv] at hY
  have sx := s29Out_val hXl hXv
  have sy := s29Out_val hYl hYv
  have mx := Nat.mod_lt (sv9 (smmRed (hi9 w) (smmIn M (BitVec.ofNat 32 (img% edMontRRAddress))))) (show 0 < Ed25519.L by omega)
  have my := Nat.mod_lt (sv9 (smmRed (lo9 w) (smmIn M (BitVec.ofNat 32 (img% edMontRAddress))))) (show 0 < Ed25519.L by omega)
  obtain ⟨hSl, hSv⟩ := add9 (X := s29Out (smmRed (hi9 w) (smmIn M (BitVec.ofNat 32 (img% edMontRRAddress)))))
    (Y := s29Out (smmRed (lo9 w) (smmIn M (BitVec.ofNat 32 (img% edMontRAddress))))) (by rw [sx, sy]; omega)
  have so := s29Out_val hSl (by rw [hSv, sx, sy]; omega)
  have hO8 : s29Out (fun j => s29AddC (s29Out (smmRed (hi9 w) (smmIn M (BitVec.ofNat 32 (img% edMontRRAddress)))))
      (s29Out (smmRed (lo9 w) (smmIn M (BitVec.ofNat 32 (img% edMontRAddress))))) (j + 1) % 2 ^ 29) 8 < 2 ^ 24 := by
    have := Nat.mod_lt (sv9 (fun j => s29AddC (s29Out (smmRed (hi9 w) (smmIn M (BitVec.ofNat 32 (img% edMontRRAddress)))))
      (s29Out (smmRed (lo9 w) (smmIn M (BitVec.ofNat 32 (img% edMontRAddress))))) (j + 1) % 2 ^ 29))
      (show 0 < Ed25519.L by omega)
    rw [← so] at this
    unfold sv9 at this
    omega
  unfold evPackS
  rw [pack9 (fun i _ => s29Out_lt29 _ i) hO8, so, hSv, sx, sy]
  exact kmod hX hY

end C3.RV32.EdK
