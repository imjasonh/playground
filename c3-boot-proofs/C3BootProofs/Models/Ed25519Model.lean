import C3BootProofs.Models.Ed25519Limbs
import C3BootProofs.Models.Ed25519Bytes
import C3BootProofs.Proofs.Ed25519VerifyC

/-!
# `evSpec` accepts only signatures `ed25519Verify` accepts

`evSpec_sound` shows that `ed25519_verify`'s model `evSpec` implies the
specification `ed25519Verify`. It assumes:

* `EdImage M`: the constants `ed25519_verify` reads are in memory.
* `EdGroupLaws`: the curve's addition is a group law.
* `EdFormulas`: what each limb formula of the double-base loop computes.
* `DecOK`, `IsoOK`, `CompressOK`, and `KOK M`: what `decompress`,
  `is_small_order`, `compress`, and the challenge scalar's reduction compute.
* `RecoverXOK`: RFC 8032's square root recovers the `x` of a point on the
  curve.

The proof composes the NAF digit sum (`nafVal_nafSpec`), the table and loop
inductions (`tab_rep`, `ladder_rep`), the byte checks, and the group algebra
(`verify_rearrange`).
-/

namespace C3.RV32.EdM

open C3.Image

/-- The 32 bytes that encode `P`: `y` with the low bit of `x` as bit 255. -/
def encode (P : Nat × Nat) : List Nat :=
  (List.range 32).map fun i => (P.2 + 2 ^ 255 * (P.1 % 2)) / 256 ^ i % 256

/-- RFC 8032's `recoverX` finds the `x` of each point on the curve from `y`
and the low bit of `x`. -/
def RecoverXOK : Prop := ∀ x y, OnCurve (x, y) → Ed25519.recoverX y (x % 2) = some x

/-- `decompress` with the image's `1`, `d`, and `sqrt(-1)` limbs, on 32 bytes
whose low 255 bits `y` are below `p`: when it returns a point `E`, that point
represents `(x, y)` on the curve, where `x` is what `recoverX` finds for `y`
and bit 255, or the encoding is `x = 0` with bit 255 set (`y = ±1`), which
`recoverX` rejects. -/
def DecOK : Prop :=
  ∀ (one dl sm b : List Nat) (E : Pt), Lim (2 ^ 26) one → fv one = 1 → Lim (2 ^ 26) dl → fv dl = Ed25519.d →
    Lim (2 ^ 26) sm → fv sm = Ed25519.sqrtM1 → b.length = 32 → Byt b → Ed25519.leNum b % 2 ^ 255 < Ed25519.p →
    decSpec one dl sm b = some E →
    ∃ x, OnCurve (x, Ed25519.leNum b % 2 ^ 255) ∧ ERep E (x, Ed25519.leNum b % 2 ^ 255) ∧
      (Ed25519.recoverX (Ed25519.leNum b % 2 ^ 255) (Ed25519.leNum b / 2 ^ 255) = some x ∨
        (Ed25519.leNum b / 2 ^ 255 = 1 ∧
          (Ed25519.leNum b % 2 ^ 255 = 1 ∨ Ed25519.leNum b % 2 ^ 255 = Ed25519.p - 1)))

/-- `is_small_order`: when it reports `false` for an extended point, eight
times the point it represents is not the identity. -/
def IsoOK : Prop :=
  ∀ (E : Pt) (P : Nat × Nat), OnCurve P → ERep E P → isoSpec E.1 E.2.1 E.2.2.1 = false →
    Ed25519.smallOrder P = false

/-- `as_extended().compress()` of a projective point is the encoding of the
point it represents. -/
def CompressOK : Prop := ∀ (r : Pr) (P : Nat × Nat), OnCurve P → PRep r P → evCompress r = encode P

/-- `Scalar::from_bytes_mod_order_wide`, with the Montgomery constants as `M`
holds them at `0x3FCC49E4` and `0x3FCC49C0`: the little-endian bytes of a
SHA-512 digest reduced modulo `L`. -/
def KOK (M : Word → BitVec 8) : Prop :=
  ∀ m : Bytes, leL (kOf (smmIn M (BitVec.ofNat 32 0x3FCC49E4)) (smmIn M (BitVec.ofNat 32 0x3FCC49C0)) (sha512 m)) 0 32 =
    Ed25519.leNum (sha512 m) % Ed25519.L

/-- `L`, 32 bytes little-endian. -/
def edLBytes : List Nat :=
  [0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10]

/-- `p`, 32 bytes little-endian. -/
def edPBytes : List Nat :=
  [0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]

/-- `1`, 32 bytes little-endian. -/
def edOneBytes : List Nat :=
  [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- `p - 1`, 32 bytes little-endian. -/
def edPm1Bytes : List Nat :=
  [0xec, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]

/-- The constants `ed25519_verify` reads, as memory `M` holds them: `L` and
`p` as 32 little-endian bytes, the encodings of `y = 1` and `y = p - 1` in
either order, the image's 40-byte field elements `1`, `d`, `sqrt(-1)`, and `2d`, and the
base point's extended coordinates. -/
structure EdImage (M : Word → BitVec 8) : Prop where
  order : memBytes M (BitVec.ofNat 32 0x3FCC4308) 32 = edLBytes
  prime : memBytes M (BitVec.ofNat 32 0x3FCC4328) 32 = edPBytes
  xzero : (memBytes M (BitVec.ofNat 32 0x3FCC42E8) 32 = edOneBytes ∧ memBytes M (BitVec.ofNat 32 0x3FCC4388) 32 = edPm1Bytes) ∨
    (memBytes M (BitVec.ofNat 32 0x3FCC42E8) 32 = edPm1Bytes ∧ memBytes M (BitVec.ofNat 32 0x3FCC4388) 32 = edOneBytes)
  one : memBytes M (BitVec.ofNat 32 edOneAddress) 40 = edOneData
  d : memBytes M (BitVec.ofNat 32 edDAddress) 40 = edDData
  sqrtM1 : memBytes M (BitVec.ofNat 32 edSqrtM1Address) 40 = edSqrtM1Data
  d2 : memBytes M apnD 40 = edwardsD2Data
  base : ERep (ptAt M (BitVec.ofNat 32 0x3FCC4A54)) Ed25519.B

/-- A field element's limbs, from its 40 bytes. -/
def limbsOf (data : List Nat) : List Nat :=
  (List.range 10).map fun i => le32 (data.getD (4 * i) 0) (data.getD (4 * i + 1) 0) (data.getD (4 * i + 2) 0)
    (data.getD (4 * i + 3) 0)

theorem limbAt_bytes (M : Word → BitVec 8) (a : Word) {i : Nat} (hi : i < 10) :
    limbAt M a i = le32 ((memBytes M a 40).getD (4 * i) 0) ((memBytes M a 40).getD (4 * i + 1) 0)
      ((memBytes M a 40).getD (4 * i + 2) 0) ((memBytes M a 40).getD (4 * i + 3) 0) := by
  unfold limbAt
  rw [memLoad32_toNat, memBytes_getD (by omega), memBytes_getD (by omega), memBytes_getD (by omega),
    memBytes_getD (by omega), show (1 : Word) = BitVec.ofNat 32 1 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]

theorem feW_bytes {M : Word → BitVec 8} {a : Word} {data : List Nat} (h : memBytes M a 40 = data) :
    feW M a = limbsOf data := by
  unfold feW limbsOf
  simp only [limbAt_bytes M a (show 0 < 10 by decide), limbAt_bytes M a (show 1 < 10 by decide),
    limbAt_bytes M a (show 2 < 10 by decide), limbAt_bytes M a (show 3 < 10 by decide),
    limbAt_bytes M a (show 4 < 10 by decide), limbAt_bytes M a (show 5 < 10 by decide),
    limbAt_bytes M a (show 6 < 10 by decide), limbAt_bytes M a (show 7 < 10 by decide),
    limbAt_bytes M a (show 8 < 10 by decide), limbAt_bytes M a (show 9 < 10 by decide), h]
  rfl

section
variable {M : Word → BitVec 8}

theorem EdImage.orderN (I : EdImage M) : Ed25519.leNum (memBytes M (BitVec.ofNat 32 0x3FCC4308) 32) = Ed25519.L := by
  rw [I.order]; decide

theorem EdImage.primeN (I : EdImage M) : Ed25519.leNum (memBytes M (BitVec.ofNat 32 0x3FCC4328) 32) = Ed25519.p := by
  rw [I.prime]; decide

theorem EdImage.xzeroN (I : EdImage M) :
    (Ed25519.leNum (memBytes M (BitVec.ofNat 32 0x3FCC42E8) 32) = 1 ∧
      Ed25519.leNum (memBytes M (BitVec.ofNat 32 0x3FCC4388) 32) = Ed25519.p - 1) ∨
    (Ed25519.leNum (memBytes M (BitVec.ofNat 32 0x3FCC42E8) 32) = Ed25519.p - 1 ∧
      Ed25519.leNum (memBytes M (BitVec.ofNat 32 0x3FCC4388) 32) = 1) := by
  rcases I.xzero with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left; rw [e1, e2]; decide
  · right; rw [e1, e2]; decide

theorem EdImage.oneOK (I : EdImage M) :
    Lim (2 ^ 26) (feW M (BitVec.ofNat 32 edOneAddress)) ∧ fv (feW M (BitVec.ofNat 32 edOneAddress)) = 1 := by
  rw [feW_bytes I.one]; decide +kernel

theorem EdImage.dOK (I : EdImage M) :
    Lim (2 ^ 26) (feW M (BitVec.ofNat 32 edDAddress)) ∧ fv (feW M (BitVec.ofNat 32 edDAddress)) = Ed25519.d := by
  rw [feW_bytes I.d]; decide +kernel

theorem EdImage.smOK (I : EdImage M) :
    Lim (2 ^ 26) (feW M (BitVec.ofNat 32 edSqrtM1Address)) ∧
      fv (feW M (BitVec.ofNat 32 edSqrtM1Address)) = Ed25519.sqrtM1 := by
  rw [feW_bytes I.sqrtM1, sqrtM1_eq]; decide +kernel

theorem EdImage.d2OK (I : EdImage M) : Lim (2 ^ 26) (feW M apnD) ∧ fv (feW M apnD) = 2 * Ed25519.d % Ed25519.p := by
  rw [feW_bytes I.d2]; decide +kernel

end

theorem feZ_eq : feZ = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

theorem leL_lv (d : List Nat) : ∀ k, leL d 0 k = lv k d
  | 0 => rfl
  | k + 1 => by simp only [leL, lv, Nat.zero_add, leL_lv d k]

theorem leNum_memBytes (M : Word → BitVec 8) (a : Word) :
    leL (memBytes M a 32) 0 32 = Ed25519.leNum (memBytes M a 32) := by
  rw [leL_lv, leNum_lv, memBytes_length]

theorem encode_getD (P : Nat × Nat) {i : Nat} (hi : i < 32) :
    (encode P).getD i 0 = (P.2 + 2 ^ 255 * (P.1 % 2)) / 256 ^ i % 256 := by
  simp [encode, List.getD, List.getElem?_map, List.getElem?_range hi]

theorem lv_encode (P : Nat × Nat) : ∀ k, k ≤ 32 → lv k (encode P) = (P.2 + 2 ^ 255 * (P.1 % 2)) % 256 ^ k
  | 0, _ => by simp only [lv, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by
    rw [lv, lv_encode P k (by omega), encode_getD P (by omega), Nat.mod_pow_succ, Nat.mul_comm (256 ^ k)]

theorem encode_length (P : Nat × Nat) : (encode P).length = 32 := by simp [encode]

/-- Decoding inverts encoding on the curve. -/
theorem decode_encode (hrx : RecoverXOK) (P : Nat × Nat) (hP : OnCurve P) : Ed25519.decode (encode P) = some P := by
  obtain ⟨x, y⟩ := P
  have hy : y < Ed25519.p := hP.2.1
  have hv : Ed25519.leNum (encode (x, y)) = y + 2 ^ 255 * (x % 2) := by
    rw [leNum_lv, encode_length, lv_encode _ 32 (Nat.le_refl _)]
    apply Nat.mod_eq_of_lt
    have : x % 2 < 2 := Nat.mod_lt _ (by decide)
    unfold Ed25519.p at hy
    show y + 2 ^ 255 * (x % 2) < 256 ^ 32
    omega
  have e1 : Ed25519.leNum (encode (x, y)) % 2 ^ 255 = y := by
    rw [hv]; unfold Ed25519.p at hy; have : x % 2 < 2 := Nat.mod_lt _ (by decide); omega
  have e2 : Ed25519.leNum (encode (x, y)) / 2 ^ 255 = x % 2 := by
    rw [hv]; unfold Ed25519.p at hy; have : x % 2 < 2 := Nat.mod_lt _ (by decide); omega
  have := decode_of_recoverX (encode (x, y)) (encode_length _) (by rw [e1]; exact hy) x
    (by rw [e1, e2]; exact hrx x y hP)
  rwa [e1] at this

theorem evSpecA_some {M : Word → BitVec 8} {pk sig : Word} {E : Pt} (h : evSpecA M pk sig = some E) :
    evChecks M pk sig = true ∧ evDec M (memBytes M pk 32) = some E := by
  unfold evSpecA at h
  by_cases hc : evChecks M pk sig = true
  · rw [ite_eq_left hc] at h
    refine ⟨hc, ?_⟩
    revert h
    cases evDec M (memBytes M pk 32) with
    | none => intro h; cases h
    | some E' =>
      obtain ⟨X, Y, Z, T⟩ := E'
      intro h
      dsimp only at h
      by_cases hr : (evSOk M sig && evRok (evDec M (memBytes M sig 32)) X Y Z) = true
      · rw [ite_eq_left hr] at h; rw [h]
      · rw [ite_eq_right hr] at h; cases h
  · rw [ite_eq_right hc] at h; cases h

section
variable {M : Word → BitVec 8} (I : EdImage M) (hdec : DecOK) (hiso : IsoOK)
include I hdec hiso

/-- A key `ed25519_public_key_ok` accepts decodes to a point on the curve, not
of small order, that `decompress`'s result represents. -/
theorem pk_point (a : Word) (h : evPk M (memBytes M a 32) = true) :
    ∃ P, Ed25519.decode (memBytes M a 32) = some P ∧ OnCurve P ∧ Ed25519.smallOrder P = false ∧
      ∀ E, evDec M (memBytes M a 32) = some E → ERep E P := by
  have hb : (memBytes M a 32).length = 32 := memBytes_length _ _ _
  have hB := byt_memBytes M a 32
  unfold evPk pkOkSpec at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hlt, hnot⟩, hres⟩ := h
  revert hres
  unfold evDec
  cases hd : decSpec (feW M (BitVec.ofNat 32 edOneAddress)) (feW M (BitVec.ofNat 32 edDAddress))
      (feW M (BitVec.ofNat 32 edSqrtM1Address)) (memBytes M a 32) with
  | none => intro hres; simp only [pkRes, Bool.false_eq_true] at hres
  | some E0 =>
    intro hres
    obtain ⟨X0, Y0, Z0, T0⟩ := E0
    simp only [pkRes, Bool.not_eq_eq_eq_not, Bool.not_true] at hres
    obtain ⟨hct, hsg⟩ := leNum_clearTop _ hb hB
    have hy : Ed25519.leNum (memBytes M a 32) % 2 ^ 255 < Ed25519.p := by
      rw [← hct, leNum_lv, clearTop_length, hb, ← I.primeN, leNum_lv, memBytes_length]
      exact ltLEb_lt (byt_clearTop hb hB) (byt_memBytes _ _ _) 32 hlt
    obtain ⟨x, hon, hrep, hor⟩ := hdec _ _ _ _ _ I.oneOK.1 I.oneOK.2 I.dOK.1 I.dOK.2 I.smOK.1 I.smOK.2 hb hB hy hd
    have hdecode : Ed25519.decode (memBytes M a 32) = some (x, Ed25519.leNum (memBytes M a 32) % 2 ^ 255) := by
      rcases hor with hr | ⟨hs, hy1⟩
      · exact decode_of_recoverX _ hb hy x hr
      · exfalso
        have h31 := hB 31
        have h128 : 128 ≤ (memBytes M a 32).getD 31 0 := by omega
        have hE : clearTop (memBytes M a 32) = memBytes M (BitVec.ofNat 32 0x3FCC42E8) 32 ∨
            clearTop (memBytes M a 32) = memBytes M (BitVec.ofNat 32 0x3FCC4388) 32 := by
          have hc := byt_clearTop hb hB
          have hl : (clearTop (memBytes M a 32)).length = 32 := by rw [clearTop_length, hb]
          rcases I.xzeroN with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hy1 with y1 | y1
          · exact Or.inl (eq_of_leNum hc (byt_memBytes _ _ _) hl (memBytes_length _ _ _) (by rw [hct, y1, e1]))
          · exact Or.inr (eq_of_leNum hc (byt_memBytes _ _ _) hl (memBytes_length _ _ _) (by rw [hct, y1, e2]))
          · exact Or.inr (eq_of_leNum hc (byt_memBytes _ _ _) hl (memBytes_length _ _ _) (by rw [hct, y1, e2]))
          · exact Or.inl (eq_of_leNum hc (byt_memBytes _ _ _) hl (memBytes_length _ _ _) (by rw [hct, y1, e1]))
        rcases hE with hE | hE <;> simp [h128, hE] at hnot
    refine ⟨_, hdecode, hon, hiso _ _ hon hrep hres, fun E hE => ?_⟩
    cases hE
    exact hrep

end

theorem L_lt : Ed25519.L < 2 ^ 255 := by decide

/-- **`evSpec` accepts only signatures `ed25519Verify` accepts**, for memory
that holds the image's constants, given the group laws and what each limb
routine computes. -/
theorem evSpec_sound {M : Word → BitVec 8} (I : EdImage M) (G : EdGroupLaws) (F : EdFormulas) (hdec : DecOK)
    (hiso : IsoOK) (hcmp : CompressOK) (hk : KOK M) (hrx : RecoverXOK) (pk sig msg : Word) (len : Nat)
    (h : evSpec M pk sig msg len = true) :
    ed25519Verify (memBytes M pk 32) (memBytes M msg len) (memBytes M sig 64) = true := by
  unfold evSpec at h
  revert h
  cases hA : evSpecA M pk sig with
  | none => intro h; cases h
  | some E =>
    intro h
    obtain ⟨X, Y, Z, T⟩ := E
    dsimp only at h
    obtain ⟨hc, hdA⟩ := evSpecA_some hA
    simp only [evChecks, Bool.and_eq_true] at hc
    obtain ⟨⟨hlt, hpk⟩, hR⟩ := hc
    obtain ⟨A, hdecA, hAon, hAsm, hArep⟩ := pk_point I hdec hiso pk hpk
    obtain ⟨r, hdecR, hron, hrsm, -⟩ := pk_point I hdec hiso sig hR
    have hAE := hArep _ hdA
    have hS : Ed25519.leNum (memBytes M (sig + BitVec.ofNat 32 32) 32) < Ed25519.L := by
      have := ltLEb_lt (byt_memBytes _ _ _) (byt_memBytes _ _ _) 32 hlt
      rwa [← leNum_lv, ← I.orderN, ← leNum_lv] at this
    have hd2 := I.d2OK
    have hTA := tab_rep G F _ hd2.1 hd2.2 _ _ (onCurve_neg _ hAon) (erep_neg feNeg_ok hAon hAE)
    have hTB := tab_rep G F _ hd2.1 hd2.2 _ _ onCurve_B I.base
    have hr0 : PRep (feZ, feW M (BitVec.ofNat 32 0x3FCC4948), feW M (BitVec.ofNat 32 0x3FCC4948))
        (Ed25519.add (zs 0 (neg A)) (zs 0 Ed25519.B)) := by
      rw [show zs (0 : Int) (neg A) = Ed25519.zero from rfl, show zs (0 : Int) Ed25519.B = Ed25519.zero from rfl,
        zero_add' _ onCurve_zero]
      have h1 := I.oneOK
      refine ⟨by rw [feZ_eq]; decide, h1.1, h1.1, by rw [h1.2]; decide, by rw [feZ_eq]; decide, ?_⟩
      rw [h1.2]; rfl
    let K := Ed25519.leNum (sha512 (memBytes M sig 32 ++ memBytes M pk 32 ++ memBytes M msg len)) % Ed25519.L
    let S := Ed25519.leNum (memBytes M (sig + BitVec.ofNat 32 32) 32)
    have hK : K < Ed25519.L := Nat.mod_lt _ (by decide)
    have hl := ladder_rep G F _ _ _ _ (onCurve_neg _ hAon) onCurve_B hTA hTB _ _
      (fun k => (nafSpec_shape _ k).imp id (·.1)) (fun k => nafSpec_range _ k)
      (fun k => (nafSpec_shape _ k).imp id (·.1)) (fun k => nafSpec_range _ k) _ _ 0 0 hr0
    rw [Int.zero_mul, Int.zero_add, Int.zero_mul, Int.zero_add] at hl
    have htop := nafTop_le (nafSpec (leL (kOf (smmIn M (BitVec.ofNat 32 0x3FCC49E4))
      (smmIn M (BitVec.ofNat 32 0x3FCC49C0)) (sha512 (memBytes M sig 32 ++ memBytes M pk 32 ++ memBytes M msg len))) 0 32))
      (nafSpec (leL (memBytes M (sig + BitVec.ofNat 32 32) 32) 0 32)) 256
    rw [nafVal_zero_above _ _ 256 (by omega) (fun j h1 h2 => (nafTop_zero _ _ 256 j (by omega) h2).1),
      nafVal_zero_above _ _ 256 (by omega) (fun j h1 h2 => (nafTop_zero _ _ 256 j (by omega) h2).2),
      nafVal_nafSpec _ (by rw [hk]; exact Nat.lt_trans hK L_lt), hk,
      nafVal_nafSpec _ (by rw [leNum_memBytes]; exact Nat.lt_trans hS L_lt), leNum_memBytes,
      zs_ofNat, zs_ofNat] at hl
    have hPf := G.closed _ _ (nsmul_on G _ (onCurve_neg _ hAon) K) (nsmul_on G _ onCurve_B S)
    have hc := hcmp _ _ hPf hl
    have heq := of_decide_eq_true h
    rw [hc] at heq
    have hrP : Ed25519.add (nsmul K (neg A)) (nsmul S Ed25519.B) = r := by
      have := decode_encode hrx _ hPf
      rw [heq, hdecR] at this
      exact (Option.some.inj this).symm
    have hver := verify_rearrange G A Ed25519.B r hAon onCurve_B K S hrP
    unfold ed25519Verify
    rw [memBytes_take M sig (show 32 ≤ 64 by decide), hdecA, hdecR, memBytes_drop M sig (show 32 ≤ 64 by decide)]
    simp only [memBytes_length, beq_self_eq_true, Bool.true_and, show 64 - 32 = 32 from rfl, decide_eq_true hS,
      hAsm, hrsm, Bool.not_false, Bool.true_and]
    exact beq_iff_eq.mpr hver

end C3.RV32.EdM
