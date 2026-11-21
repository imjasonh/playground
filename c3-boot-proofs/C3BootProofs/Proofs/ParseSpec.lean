import C3BootProofs.Proofs.Parse
import C3BootProofs.Spec.Formats

/-!
# `manifest::parse` agrees with `decodeManifest`

`decodeManifest_parse` proves that `parseErr`, what the compiled `parse`
decides, accepts the 40 bytes exactly when the Lean decoder `decodeManifest`
does, and that the four parts it returns are the decoder's.
`manifestParse_decodes` joins that to `manifestParse_correct`: the compiled
function returns `Ok` with the decoder's manifest, or `Err`, as the decoder
says.

`omega`'s proof of a conjunction or an `↔` depends on `Classical.choice`, so
those goals are split by hand before `omega` sees them.
-/

namespace C3

open RV32

/-- A little-endian 32-bit word from four bytes. -/
abbrev le32 (a b c d : Nat) : Nat := a + 256 * (b + 256 * (c + 256 * d))

theorem decodeManifest_bytes (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23
    b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 : Nat) :
    decodeManifest [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20,
      b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39] =
    if ([b0, b1, b2, b3] == [67, 51, 83, 76]) = true ∧ b4 + 256 * b5 = 1 ∧ b6 = 0 ∧ b7 = 0 ∧
        (37 ≤ le32 b12 b13 b14 b15 ∧ le32 b12 b13 b14 b15 ≤ 0x1D0000) ∧
        (49 ≤ le32 b20 b21 b22 b23 ∧ le32 b20 b21 b22 b23 ≤ 16384) ∧
        (8 ≤ le32 b28 b29 b30 b31 ∧ le32 b28 b29 b30 b31 ≤ 2048) ∧
        (443 ≤ le32 b36 b37 b38 b39 ∧ le32 b36 b37 b38 b39 ≤ 4096) ∧
        le32 b8 b9 b10 b11 = 0x10000 ∧
        le32 b8 b9 b10 b11 + le32 b12 b13 b14 b15 < 2 ^ 32 ∧
        le32 b16 b17 b18 b19 + le32 b20 b21 b22 b23 < 2 ^ 32 ∧
        le32 b24 b25 b26 b27 + le32 b28 b29 b30 b31 < 2 ^ 32 ∧
        le32 b32 b33 b34 b35 + le32 b36 b37 b38 b39 < 2 ^ 32 ∧
        le32 b8 b9 b10 b11 + le32 b12 b13 b14 b15 ≤ le32 b16 b17 b18 b19 ∧
        le32 b16 b17 b18 b19 + le32 b20 b21 b22 b23 ≤ le32 b24 b25 b26 b27 ∧
        le32 b24 b25 b26 b27 + le32 b28 b29 b30 b31 ≤ le32 b32 b33 b34 b35 ∧
        le32 b32 b33 b34 b35 + le32 b36 b37 b38 b39 ≤ 0x1E0000
    then some ⟨⟨le32 b8 b9 b10 b11, le32 b12 b13 b14 b15⟩, ⟨le32 b16 b17 b18 b19, le32 b20 b21 b22 b23⟩,
      ⟨le32 b24 b25 b26 b27, le32 b28 b29 b30 b31⟩, ⟨le32 b32 b33 b34 b35, le32 b36 b37 b38 b39⟩⟩
    else none := by
  simp only [decodeManifest, readHeader, readExpect, readU16, readZeros, readPart, readU32, magicManifest,
    List.take, List.drop, List.length, List.all, require, bind, Option.bind,
    Part.endOf, u32Limit, slotSize, imageOffset, List.isEmpty]
  by_cases h1 : ([b0, b1, b2, b3] == [67, 51, 83, 76]) = true <;> simp [h1]
  by_cases h2 : b4 + 256 * b5 = 1 <;> simp [h2]
  by_cases h3 : b6 = 0 <;> simp [h3]
  by_cases h4 : b7 = 0 <;> simp [h4]
  by_cases h5 : 37 ≤ (b12 + 256 * (b13 + 256 * (b14 + 256 * b15))) ∧ (b12 + 256 * (b13 + 256 * (b14 + 256 * b15))) ≤ 1900544 <;> simp [h5]
  by_cases h6 : 49 ≤ (b20 + 256 * (b21 + 256 * (b22 + 256 * b23))) ∧ (b20 + 256 * (b21 + 256 * (b22 + 256 * b23))) ≤ 16384 <;> simp [h6]
  by_cases h7 : 8 ≤ (b28 + 256 * (b29 + 256 * (b30 + 256 * b31))) ∧ (b28 + 256 * (b29 + 256 * (b30 + 256 * b31))) ≤ 2048 <;> simp [h7]
  by_cases h8 : 443 ≤ (b36 + 256 * (b37 + 256 * (b38 + 256 * b39))) ∧ (b36 + 256 * (b37 + 256 * (b38 + 256 * b39))) ≤ 4096 <;> simp [h8]
  by_cases h9 : (b8 + 256 * (b9 + 256 * (b10 + 256 * b11))) = 65536 <;> simp [h9]
  by_cases h10 : 65536 + (b12 + 256 * (b13 + 256 * (b14 + 256 * b15))) < 4294967296 <;> simp [h10]
  by_cases h11 : (b16 + 256 * (b17 + 256 * (b18 + 256 * b19))) + (b20 + 256 * (b21 + 256 * (b22 + 256 * b23))) < 4294967296 <;> simp [h11]
  by_cases h12 : (b24 + 256 * (b25 + 256 * (b26 + 256 * b27))) + (b28 + 256 * (b29 + 256 * (b30 + 256 * b31))) < 4294967296 <;> simp [h12]
  by_cases h13 : (b32 + 256 * (b33 + 256 * (b34 + 256 * b35))) + (b36 + 256 * (b37 + 256 * (b38 + 256 * b39))) < 4294967296 <;> simp [h13]
  by_cases h14 : 65536 + (b12 + 256 * (b13 + 256 * (b14 + 256 * b15))) ≤ (b16 + 256 * (b17 + 256 * (b18 + 256 * b19))) <;> simp [h14]
  by_cases h15 : (b16 + 256 * (b17 + 256 * (b18 + 256 * b19))) + (b20 + 256 * (b21 + 256 * (b22 + 256 * b23))) ≤ (b24 + 256 * (b25 + 256 * (b26 + 256 * b27))) <;> simp [h15]
  by_cases h16 : (b24 + 256 * (b25 + 256 * (b26 + 256 * b27))) + (b28 + 256 * (b29 + 256 * (b30 + 256 * b31))) ≤ (b32 + 256 * (b33 + 256 * (b34 + 256 * b35))) <;> simp [h16]
  by_cases h17 : (b32 + 256 * (b33 + 256 * (b34 + 256 * b35))) + (b36 + 256 * (b37 + 256 * (b38 + 256 * b39))) ≤ 1966080 <;> simp [h17]


/-- Byte `i` of the manifest at `bp`. -/
abbrev mb (M : Word → BitVec 8) (bp : Word) (i : Nat) : Nat := (M (bp + BitVec.ofNat 32 i)).toNat

/-- The 40 bytes `parse` reads, as the Lean decoders take them. -/
def manifestBytes (M : Word → BitVec 8) (bp : Word) : Bytes :=
  (List.range 40).map (mb M bp)

theorem manifestBytes_eq (M : Word → BitVec 8) (bp : Word) :
    manifestBytes M bp = [mb M bp 0, mb M bp 1, mb M bp 2, mb M bp 3, mb M bp 4, mb M bp 5, mb M bp 6,
      mb M bp 7, mb M bp 8, mb M bp 9, mb M bp 10, mb M bp 11, mb M bp 12, mb M bp 13, mb M bp 14,
      mb M bp 15, mb M bp 16, mb M bp 17, mb M bp 18, mb M bp 19, mb M bp 20, mb M bp 21, mb M bp 22,
      mb M bp 23, mb M bp 24, mb M bp 25, mb M bp 26, mb M bp 27, mb M bp 28, mb M bp 29, mb M bp 30,
      mb M bp 31, mb M bp 32, mb M bp 33, mb M bp 34, mb M bp 35, mb M bp 36, mb M bp 37, mb M bp 38,
      mb M bp 39] := rfl

theorem memLoad32_toNat (M : Word → BitVec 8) (a : Word) :
    (memLoad32 M a).toNat =
      le32 (M a).toNat (M (a + 1)).toNat (M (a + 2)).toNat (M (a + 3)).toNat := by
  unfold memLoad32
  have h0 := (M a).isLt; have h1 := (M (a + 1)).isLt; have h2 := (M (a + 2)).isLt
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt h0, ← Nat.shiftLeft_add_eq_or_of_lt h1,
    ← Nat.shiftLeft_add_eq_or_of_lt h2]
  simp only [Nat.shiftLeft_eq, le32]
  omega

theorem mw_toNat (M : Word → BitVec 8) (bp : Word) (i : Nat) :
    (mw M bp i).toNat = le32 (mb M bp i) (mb M bp (i + 1)) (mb M bp (i + 2)) (mb M bp (i + 3)) := by
  have e1 : bp + BitVec.ofNat 32 i + 1 = bp + BitVec.ofNat 32 (i + 1) := add_ofNat_assoc bp i 1
  have e2 : bp + BitVec.ofNat 32 i + 2 = bp + BitVec.ofNat 32 (i + 2) := add_ofNat_assoc bp i 2
  have e3 : bp + BitVec.ofNat 32 i + 3 = bp + BitVec.ofNat 32 (i + 3) := add_ofNat_assoc bp i 3
  rw [mw, memLoad32_toNat, e1, e2, e3]

theorem version_toNat (x4 x5 : BitVec 8) :
    (((x5.zeroExtend 32 <<< 24 ||| x4.zeroExtend 32 <<< 16 : Word) >>> 16)).toNat = x4.toNat + 256 * x5.toNat := by
  have h4 := x4.isLt; have h5 := x5.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : x4.toNat < 2 ^ 32), Nat.mod_eq_of_lt (by omega : x5.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (show x5.toNat <<< 24 < 2 ^ 32 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show x4.toNat <<< 16 < 2 ^ 32 by rw [Nat.shiftLeft_eq]; omega),
    Nat.shiftRight_or_distrib, show x5.toNat <<< 24 = (x5.toNat <<< 8) <<< 16 by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]; omega,
    Nat.shiftLeft_shiftRight, Nat.shiftLeft_shiftRight, ← Nat.shiftLeft_add_eq_or_of_lt h4, Nat.shiftLeft_eq]
  omega


theorem decodeManifest_parse (M : Word → BitVec 8) (bp : Word) :
    decodeManifest (manifestBytes M bp) =
      match parseErr M bp with
      | some _ => none
      | none => some ⟨⟨(mw M bp 8).toNat, (mw M bp 12).toNat⟩, ⟨(mw M bp 16).toNat, (mw M bp 20).toNat⟩,
          ⟨(mw M bp 24).toNat, (mw M bp 28).toNat⟩, ⟨(mw M bp 32).toNat, (mw M bp 36).toNat⟩⟩ := by
  rw [manifestBytes_eq, decodeManifest_bytes]
  have hb : ∀ i, mb M bp i < 256 := fun i => (M _).isLt
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have cm : (mw M bp 0 == 0x4C533343) = ([mb M bp 0, mb M bp 1, mb M bp 2, mb M bp 3] == [67, 51, 83, 76]) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, mw_toNat,
      show (0x4C533343 : Word).toNat = 1280521027 from rfl]
    simp only [List.cons.injEq, and_true, Nat.reduceAdd, le32]
    constructor
    · intro h; exact ⟨by omega, by omega, by omega, by omega⟩
    · intro ⟨e0, e1, e2, e3⟩; omega
  have cv : (((M (bp + 5)).zeroExtend 32 <<< 24 ||| (M (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1) =
      (mb M bp 4 + 256 * mb M bp 5 == 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, version_toNat]; rfl
  have cz : allZero M (bp + 6) 2 = (mb M bp 6 == 0 && mb M bp 7 == 0) := by
    simp only [allZero, Bool.and_true]
    rw [show bp + 6 + 1 = bp + BitVec.ofNat 32 7 from add_ofNat_assoc bp 6 1]
    have e : ∀ x : BitVec 8, (x == 0) = (x.toNat == 0) := fun x => by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj]; rfl
    rw [e, e]; rfl
  have c8 : (mw M bp 8 == 0x10000) = (le32 (mb M bp 8) (mb M bp 9) (mb M bp 10) (mb M bp 11) == 65536) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, mw_toNat]; rfl
  have lit : ∀ n : Nat, n < 2 ^ 32 → (OfNat.ofNat n : Word).toNat = n := fun n h => Nat.mod_eq_of_lt h
  unfold parseErr
  rw [cm, cv, cz, c8]
  simp only [partOut, BitVec.ult, BitVec.toNat_add, mw_toNat, Nat.reduceAdd, lit 37 (by decide),
    lit 1900544 (by decide), lit 49 (by decide), lit 16384 (by decide), lit 8 (by decide), lit 2048 (by decide),
    lit 443 (by decide), lit 4096 (by decide), lit 4294901759 (by decide), lit 65536 (by decide),
    lit 1966080 (by decide)]
  have hw : ∀ i, le32 (mb M bp i) (mb M bp (i+1)) (mb M bp (i+2)) (mb M bp (i+3)) < 2 ^ 32 := fun i => by
    have := hb i; have := hb (i + 1); have := hb (i + 2); have := hb (i + 3); simp only [le32]; omega
  have w12 := hw 12; have w16 := hw 16; have w20 := hw 20; have w24 := hw 24; have w28 := hw 28
  have w32 := hw 32; have w36 := hw 36
  simp only [Nat.reduceAdd] at w12 w16 w20 w24 w28 w32 w36
  by_cases g1 : ([mb M bp 0, mb M bp 1, mb M bp 2, mb M bp 3] == [67, 51, 83, 76]) = true <;> simp [g1]
  by_cases g2 : mb M bp 4 + 256 * mb M bp 5 = 1 <;> simp [g2]
  by_cases g3 : mb M bp 6 = 0 <;> simp [g3]
  by_cases g4 : mb M bp 7 = 0 <;> simp [g4]
  by_cases g5 : 37 ≤ le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15)
  case neg =>
    have : le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15) < 37 := by omega
    simp [*]
  have r5 : ¬ (le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15) < 37) := by omega
  by_cases g6 : le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15) ≤ 1900544
  case neg =>
    have : 1900544 < le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15) := by omega
    simp [*]
  have r6 : ¬ (1900544 < le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15)) := by omega
  by_cases g7 : 49 ≤ le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23)
  case neg =>
    have : le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) < 49 := by omega
    simp [*]
  have r7 : ¬ (le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) < 49) := by omega
  by_cases g8 : le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) ≤ 16384
  case neg =>
    have : 16384 < le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) := by omega
    simp [*]
  have r8 : ¬ (16384 < le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23)) := by omega
  by_cases g9 : 8 ≤ le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31)
  case neg =>
    have : le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) < 8 := by omega
    simp [*]
  have r9 : ¬ (le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) < 8) := by omega
  by_cases g10 : le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) ≤ 2048
  case neg =>
    have : 2048 < le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) := by omega
    simp [*]
  have r10 : ¬ (2048 < le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31)) := by omega
  by_cases g11 : 443 ≤ le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39)
  case neg =>
    have : le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) < 443 := by omega
    simp [*]
  have r11 : ¬ (le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) < 443) := by omega
  by_cases g12 : le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) ≤ 4096
  case neg =>
    have : 4096 < le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) := by omega
    simp [*]
  have r12 : ¬ (4096 < le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39)) := by omega
  by_cases g13 : le32 (mb M bp 8) (mb M bp 9) (mb M bp 10) (mb M bp 11) = 65536
  case neg => simp [*]
  by_cases g14 : 65536 + le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15) < 4294967296
  case neg =>
    have : 4294901759 < le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15) := by omega
    simp [*]
  have r14 : ¬ (4294901759 < le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15)) := by omega
  by_cases g15 : le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19) + le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) < 4294967296
  case neg =>
    have : (le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) + le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19)) % 4294967296 < le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) := by omega
    simp [*]
  have r15 : ¬ ((le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) + le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19)) % 4294967296 < le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23)) := by omega
  by_cases g16 : le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27) + le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) < 4294967296
  case neg =>
    have : (le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) + le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27)) % 4294967296 < le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) := by omega
    simp [*]
  have r16 : ¬ ((le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) + le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27)) % 4294967296 < le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31)) := by omega
  by_cases g17 : le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35) + le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) < 4294967296
  case neg =>
    have : (le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) + le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35)) % 4294967296 < le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) := by omega
    simp [*]
  have r17 : ¬ ((le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) + le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35)) % 4294967296 < le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39)) := by omega
  by_cases g18 : 65536 + le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15) ≤ le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19)
  case neg =>
    have : le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19) < (65536 + le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15)) % 4294967296 := by omega
    simp [*]
  have r18 : ¬ (le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19) < (65536 + le32 (mb M bp 12) (mb M bp 13) (mb M bp 14) (mb M bp 15)) % 4294967296) := by omega
  by_cases g19 : le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19) + le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) ≤ le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27)
  case neg =>
    have : le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27) < (le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) + le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19)) % 4294967296 := by omega
    simp [*]
  have r19 : ¬ (le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27) < (le32 (mb M bp 20) (mb M bp 21) (mb M bp 22) (mb M bp 23) + le32 (mb M bp 16) (mb M bp 17) (mb M bp 18) (mb M bp 19)) % 4294967296) := by omega
  by_cases g20 : le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27) + le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) ≤ le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35)
  case neg =>
    have : le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35) < (le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) + le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27)) % 4294967296 := by omega
    simp [*]
  have r20 : ¬ (le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35) < (le32 (mb M bp 28) (mb M bp 29) (mb M bp 30) (mb M bp 31) + le32 (mb M bp 24) (mb M bp 25) (mb M bp 26) (mb M bp 27)) % 4294967296) := by omega
  by_cases g21 : le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35) + le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) ≤ 1966080
  case neg =>
    have : 1966080 < (le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) + le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35)) % 4294967296 := by omega
    simp [*]
  have r21 : ¬ (1966080 < (le32 (mb M bp 36) (mb M bp 37) (mb M bp 38) (mb M bp 39) + le32 (mb M bp 32) (mb M bp 33) (mb M bp 34) (mb M bp 35)) % 4294967296) := by omega
  simp [*]


theorem RV32.parseErr_none_mw8 {M : Word → BitVec 8} {bp : Word} (h : parseErr M bp = none) :
    mw M bp 8 = 0x10000 := by
  cases h8 : (mw M bp 8 == 0x10000)
  · exfalso
    revert h
    unfold parseErr
    simp only [h8, Bool.not_false, ↓reduceIte]
    repeat' split
    all_goals intro h; cases h
  · exact beq_iff_eq.mp h8

/-- `parseMem` writes only the 36 bytes of the result. -/
theorem RV32.parseMem_frame {M : Word → BitVec 8} {out bp x : Word} (h : Sep out 36 x 1) :
    parseMem M out bp x = M x := by
  have ne : ∀ j, j < 36 → x ≠ out + BitVec.ofNat 32 j := fun j hj e =>
    h j hj 0 (by omega) (by rw [add_ofNat_zero]; exact e.symm)
  have so : ∀ c, c + 4 ≤ 36 → Sep (out + BitVec.ofNat 32 c) 4 x 1 := fun c hc => h.sub (c := c) (l := 4) hc
  have n0 : x ≠ out := by have := ne 0 (by omega); rwa [add_ofNat_zero] at this
  cases hp : parseErr M bp with
  | some e =>
    unfold parseMem; rw [hp]; dsimp only
    rw [memStore8_ne n0, memStore8_ne (show x ≠ out + 1 from ne 1 (by omega))]
  | none =>
    unfold parseMem; rw [hp]; dsimp only
    rw [memStore8_ne n0, memStore32_get_sep (show Sep (out + 0x20) 4 x 1 from so 32 (by omega)),
      memStore32_get_sep (show Sep (out + 0x1C) 4 x 1 from so 28 (by omega)),
      memStore32_get_sep (show Sep (out + 0x18) 4 x 1 from so 24 (by omega)),
      memStore32_get_sep (show Sep (out + 0x14) 4 x 1 from so 20 (by omega)),
      memStore32_get_sep (show Sep (out + 0x10) 4 x 1 from so 16 (by omega)),
      memStore32_get_sep (show Sep (out + 0x0C) 4 x 1 from so 12 (by omega)),
      memStore32_get_sep (show Sep (out + 8) 4 x 1 from so 8 (by omega)),
      memStore32_get_sep (show Sep (out + 4) 4 x 1 from so 4 (by omega))]

/-- **The compiled `manifest::parse` decodes as the Lean spec does.** Under
`manifestParse_correct`'s hypotheses, `parse` returns with tag 1 (`Err`)
at `out` when `decodeManifest` rejects the 40 bytes at `bp`, and with tag 0
(`Ok`) and the decoder's four parts from `out + 4` when it accepts them. It
changes no memory outside the result and its 144 bytes of stack. -/
theorem manifestParse_decodes (m : Machine) (P retAddr out bp R G : Word)
    (code : PCode m.mem P) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = bp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hspG : reg m sp = G + 0x40)
    (env : PEnv P R G bp out) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
      (∀ x, Sep R 144 x 1 → Sep out 36 x 1 → m'.mem x = m.mem x) ∧
      match decodeManifest (manifestBytes m.mem bp) with
      | none => m'.mem out = 1
      | some man =>
        m'.mem out = 0 ∧
        memLoad32 m'.mem (out + 4) = BitVec.ofNat 32 man.image.offset ∧
        memLoad32 m'.mem (out + 8) = BitVec.ofNat 32 man.image.length ∧
        memLoad32 m'.mem (out + 0x0C) = BitVec.ofNat 32 man.bundle.offset ∧
        memLoad32 m'.mem (out + 0x10) = BitVec.ofNat 32 man.bundle.length ∧
        memLoad32 m'.mem (out + 0x14) = BitVec.ofNat 32 man.chain.offset ∧
        memLoad32 m'.mem (out + 0x18) = BitVec.ofNat 32 man.chain.length ∧
        memLoad32 m'.mem (out + 0x1C) = BitVec.ofNat 32 man.blob.offset ∧
        memLoad32 m'.mem (out + 0x20) = BitVec.ofNat 32 man.blob.length := by
  obtain ⟨m', st, pc, sp', regs, mem⟩ := manifestParse_correct m P retAddr out bp R G code hpc ha0 ha1 hra hret
    hspG env
  refine ⟨m', st, pc, sp', regs, fun x h1 h2 => (mem x h1).trans (parseMem_frame h2), ?_⟩
  have hO : ∀ j, j < 36 → m'.mem (out + BitVec.ofNat 32 j) = parseMem m.mem out bp (out + BitVec.ofNat 32 j) :=
    fun j hj => mem _ (env.hOS.sub (c := j) (l := 1) (by omega)).symm
  have o0 : m'.mem out = parseMem m.mem out bp out := by
    have := hO 0 (by omega); rwa [add_ofNat_zero] at this
  have L : ∀ j, j + 4 ≤ 36 → memLoad32 m'.mem (out + BitVec.ofNat 32 j) =
      memLoad32 (parseMem m.mem out bp) (out + BitVec.ofNat 32 j) := fun j hj =>
    memLoad32_congr fun i hi => by rw [add_ofNat_assoc]; exact hO (j + i) (by omega)
  have tw : ∀ x : Word, BitVec.ofNat 32 x.toNat = x := fun x => by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [decodeManifest_parse]
  cases hp : parseErr m.mem bp with
  | some e =>
    dsimp only
    rw [o0]; unfold parseMem; rw [hp]; exact memStore8_same _ _ _
  | none =>
    dsimp only
    have so : ∀ c d, c + 4 ≤ 36 → d + 4 ≤ 36 → c + 4 ≤ d ∨ d + 4 ≤ c →
        Sep (out + BitVec.ofNat 32 c) 4 (out + BitVec.ofNat 32 d) 4 :=
      fun c d h1 h2 h => sep_offsets out h (by omega) (by omega)
    have s8 : ∀ d, 4 ≤ d → d + 4 ≤ 36 → Sep out 1 (out + BitVec.ofNat 32 d) 4 := fun d h1 h2 => by
      have := sep_offsets out (c := 0) (n := 1) (d := d) (k := 4) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have pm : parseMem m.mem out bp = memStore8 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
        (memStore32 (memStore32 (memStore32 m.mem (out + 4) 0x10000) (out + 8) (mw m.mem bp 12))
        (out + 0x0C) (mw m.mem bp 16)) (out + 0x10) (mw m.mem bp 20)) (out + 0x14) (mw m.mem bp 24))
        (out + 0x18) (mw m.mem bp 28)) (out + 0x1C) (mw m.mem bp 32)) (out + 0x20) (mw m.mem bp 36)) out 0 := by
      unfold parseMem; rw [hp]
    simp only [tw]
    rw [parseErr_none_mw8 hp, o0, pm]
    refine ⟨memStore8_same _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show memLoad32 m'.mem (out + 4) = memLoad32 (parseMem m.mem out bp) (out + 4) from L 4 (by omega),
        pm,
        memLoad32_store8_sep (show Sep out 1 (out + 4) 4 from s8 4 (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x20) 4 (out + 4) 4 from so 32 4 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x1C) 4 (out + 4) 4 from so 28 4 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x18) 4 (out + 4) 4 from so 24 4 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x14) 4 (out + 4) 4 from so 20 4 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x10) 4 (out + 4) 4 from so 16 4 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x0C) 4 (out + 4) 4 from so 12 4 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 8) 4 (out + 4) 4 from so 8 4 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [show memLoad32 m'.mem (out + 8) = memLoad32 (parseMem m.mem out bp) (out + 8) from L 8 (by omega),
        pm,
        memLoad32_store8_sep (show Sep out 1 (out + 8) 4 from s8 8 (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x20) 4 (out + 8) 4 from so 32 8 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x1C) 4 (out + 8) 4 from so 28 8 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x18) 4 (out + 8) 4 from so 24 8 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x14) 4 (out + 8) 4 from so 20 8 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x10) 4 (out + 8) 4 from so 16 8 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x0C) 4 (out + 8) 4 from so 12 8 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [show memLoad32 m'.mem (out + 0x0C) = memLoad32 (parseMem m.mem out bp) (out + 0x0C) from L 12 (by omega),
        pm,
        memLoad32_store8_sep (show Sep out 1 (out + 0x0C) 4 from s8 12 (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x20) 4 (out + 0x0C) 4 from so 32 12 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x1C) 4 (out + 0x0C) 4 from so 28 12 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x18) 4 (out + 0x0C) 4 from so 24 12 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x14) 4 (out + 0x0C) 4 from so 20 12 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x10) 4 (out + 0x0C) 4 from so 16 12 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [show memLoad32 m'.mem (out + 0x10) = memLoad32 (parseMem m.mem out bp) (out + 0x10) from L 16 (by omega),
        pm,
        memLoad32_store8_sep (show Sep out 1 (out + 0x10) 4 from s8 16 (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x20) 4 (out + 0x10) 4 from so 32 16 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x1C) 4 (out + 0x10) 4 from so 28 16 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x18) 4 (out + 0x10) 4 from so 24 16 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x14) 4 (out + 0x10) 4 from so 20 16 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [show memLoad32 m'.mem (out + 0x14) = memLoad32 (parseMem m.mem out bp) (out + 0x14) from L 20 (by omega),
        pm,
        memLoad32_store8_sep (show Sep out 1 (out + 0x14) 4 from s8 20 (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x20) 4 (out + 0x14) 4 from so 32 20 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x1C) 4 (out + 0x14) 4 from so 28 20 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x18) 4 (out + 0x14) 4 from so 24 20 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [show memLoad32 m'.mem (out + 0x18) = memLoad32 (parseMem m.mem out bp) (out + 0x18) from L 24 (by omega),
        pm,
        memLoad32_store8_sep (show Sep out 1 (out + 0x18) 4 from s8 24 (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x20) 4 (out + 0x18) 4 from so 32 24 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x1C) 4 (out + 0x18) 4 from so 28 24 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [show memLoad32 m'.mem (out + 0x1C) = memLoad32 (parseMem m.mem out bp) (out + 0x1C) from L 28 (by omega),
        pm,
        memLoad32_store8_sep (show Sep out 1 (out + 0x1C) 4 from s8 28 (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (out + 0x20) 4 (out + 0x1C) 4 from so 32 28 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [show memLoad32 m'.mem (out + 0x20) = memLoad32 (parseMem m.mem out bp) (out + 0x20) from L 32 (by omega),
        pm,
        memLoad32_store8_sep (show Sep out 1 (out + 0x20) 4 from s8 32 (by omega) (by omega)),
        memLoad32_store32_same]

end C3
