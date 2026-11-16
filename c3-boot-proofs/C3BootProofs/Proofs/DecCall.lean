import C3BootProofs.Proofs.IsSmallOrder
import C3BootProofs.Proofs.Pow22501
import C3BootProofs.Proofs.FeCondNeg
import C3BootProofs.Proofs.FeIsNeg
import C3BootProofs.Proofs.FeLoad

/-!
# Calls from `CompressedEdwardsY::decompress`

`decompress` is a chain of about fifty calls to the proved field
operations. This file states what the function computes on limb lists
(`decSpec`) and gives one lemma per kind of call that runs it from the
invariant `DecSt` and restates the callee's theorem over limb lists. The
frame is 0x2A0 bytes at `R + 0x450`, below it the callees' frames, and the
whole 0x6F0 bytes from `R` are the stack the function may write.
-/

namespace C3.RV32

open C3.Image

/-! ## Limb lists -/

/-- A limb list as the word function the callee theorems take. -/
def limbF (l : List Nat) : Nat → Word := fun i => BitVec.ofNat 32 (l.getD i 0)

/-- The first ten words of a word function, as a limb list. -/
def ofW (x : Nat → Word) : List Nat :=
  [(x 0).toNat, (x 1).toNat, (x 2).toNat, (x 3).toNat, (x 4).toNat, (x 5).toNat, (x 6).toNat, (x 7).toNat,
   (x 8).toNat, (x 9).toNat]

/-- A limb list with each of its first ten limbs taken modulo 2^32. -/
def wl (L : List Nat) : List Nat := ofW (limbF L)

/-- `FieldElement2625::reduce` of ten `u64` limbs. -/
def redL (z : List Nat) : List Nat :=
  feReduceSpec (z.getD 0 0) (z.getD 1 0) (z.getD 2 0) (z.getD 3 0) (z.getD 4 0) (z.getD 5 0) (z.getD 6 0)
    (z.getD 7 0) (z.getD 8 0) (z.getD 9 0)

/-- `pow22501`'s first result, `x^(2^250 - 1)`. -/
def pw19L (l : List Nat) : List Nat := ofW (pwT19 (limbF l))

/-- `<&FieldElement2625 as Neg>::neg` on limbs. -/
def negL (l : List Nat) : List Nat :=
  feReduceSpec (feNegZ (limbF l) 0).toNat (feNegZ (limbF l) 1).toNat (feNegZ (limbF l) 2).toNat
    (feNegZ (limbF l) 3).toNat (feNegZ (limbF l) 4).toNat (feNegZ (limbF l) 5).toNat (feNegZ (limbF l) 6).toNat
    (feNegZ (limbF l) 7).toNat (feNegZ (limbF l) 8).toNat (feNegZ (limbF l) 9).toNat

/-- `is_negative`: the low bit of the canonical encoding. -/
def isNegL (l : List Nat) : Bool := (bytesL l).getD 0 0 % 2 == 1

/-- `conditional_negate`. -/
def condNegL (l : List Nat) (c : Bool) : List Nat := if c then wl (negL l) else l

/-- `ct_eq`: whether the canonical encodings agree. -/
def feEqL (a b : List Nat) : Bool := decide (bytesL a = bytesL b)

/-- The ten `u64` limbs `FieldElement2625::from_bytes` builds from 32 bytes,
before it reduces them. -/
def decLoad (b : Bytes) : List Nat :=
  let g := fun i => b.getD i 0
  let l3 := fun i => g i + 2 ^ 8 * g (i + 1) + 2 ^ 16 * g (i + 2)
  let l4 := fun i => l3 i + 2 ^ 24 * g (i + 3)
  [l4 0, l3 4 * 2 ^ 6 % 2 ^ 32, l3 7 * 2 ^ 5 % 2 ^ 32, l3 10 * 2 ^ 3 % 2 ^ 32, l3 13 * 2 ^ 2 % 2 ^ 32, l4 16,
   l3 20 * 2 ^ 7 % 2 ^ 32, l3 23 * 2 ^ 5 % 2 ^ 32, l3 26 * 2 ^ 4 % 2 ^ 32, l3 29 * 2 ^ 9 % 2 ^ 32 / 2 ^ 7]

/-- `FieldElement2625::sqrt_ratio_i(u, v)`: whether `u / v` is a square, and
the nonnegative root it computes. -/
def decSqrtRatio (sqrtM1 u v : List Nat) : Bool × List Nat :=
  let v3 := mulL (sqL v) v
  let v7 := mulL (sqL v3) v
  let uv3 := mulL u v3
  let uv7 := mulL u v7
  let r := mulL uv3 (mulL uv7 (sqIter 2 (pw19L uv7)))
  let check := mulL v (sqL r)
  let cs := feEqL check u
  let fs := feEqL check (negL u)
  let fsi := feEqL check (mulL (negL u) sqrtM1)
  let r := if fs || fsi then mulL sqrtM1 r else r
  (cs || fs, condNegL r (isNegL r))

/-- What `decompress` computes from the 32 bytes `b`, with the image's
field elements `one`, `d`, and `sqrtM1`: the point's extended coordinates
`X`, `Y`, `Z`, `T` on limbs, or `none` when `b` names no point. -/
def decSpec (one d sqrtM1 : List Nat) (b : Bytes) : Option (List Nat × List Nat × List Nat × List Nat) :=
  let Y := redL (decLoad b)
  let YY := sqL Y
  let u := subL YY one
  let v := addL (mulL YY d) one
  let s := decSqrtRatio sqrtM1 u v
  if s.1 then
    let X := condNegL s.2 (b.getD 31 0 / 128 == 1)
    some (X, Y, one, mulL X Y)
  else none

/-! ## Limb-list forms of the callee theorems -/

theorem feW_ofW (M : Word → BitVec 8) (a : Word) : feW M a = ofW (limbs M a) := rfl

theorem limbs_limbF {M : Word → BitVec 8} {a : Word} : ∀ i, i < 10 → limbs M a i = limbF (feW M a) i :=
  limbs_of_feW rfl

theorem pwT19_congr {x x' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) : pwT19 x = pwT19 x' := by
  have e0 : pwT0 x = pwT0 x' := feSqW_congr hx
  have e1 : pwT1 x = pwT1 x' := by unfold pwT1 pwT0s; rw [e0]
  have e2 : pwT2 x = pwT2 x' := by unfold pwT2; rw [feMulW_congr hx (fun _ _ => rfl), e1]
  have e5 : pwT5 x = pwT5 x' := by unfold pwT5 pwT4 pwT3; rw [e0, e2]
  have e7 : pwT7 x = pwT7 x' := by unfold pwT7 pwT6; rw [e5]
  have e13 : pwT13 x = pwT13 x' := by unfold pwT13 pwT12 pwT11 pwT10 pwT9 pwT8; rw [e7]
  unfold pwT19 pwT18 pwT17 pwT16 pwT15 pwT14; rw [e13]

theorem feNegZ_congr {x x' : Nat → Word} (hx : ∀ i, i < 10 → x i = x' i) :
    ∀ i, i < 10 → feNegZ x i = feNegZ x' i := fun i hi => by unfold feNegZ; rw [hx i hi]

/-- `feW` of a list of words read back from `wordsAt`. -/
theorem feW_of_words {M : Word → BitVec 8} {a : Word} {L : List Nat} (h : (wordsAt M a 10).map BitVec.toNat = L) :
    feW M a = L := by rw [← feW_words, h]

theorem feW_limbs_eq {M M' : Word → BitVec 8} {a b : Word} (h : ∀ i, i < 10 → limbs M' a i = limbs M b i) :
    feW M' a = feW M b := by
  rw [feW_ofW, feW_ofW]; unfold ofW
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]

theorem feW_limbs_ofW {M : Word → BitVec 8} {a : Word} {x : Nat → Word} (h : ∀ i, i < 10 → limbs M a i = x i) :
    feW M a = ofW x := by
  rw [feW_ofW]; unfold ofW
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]

theorem feW_sq {M M' : Word → BitVec 8} {o x : Word}
    (h : (wordsAt M' o 10).map BitVec.toNat =
      feSquareSpec (limbAt M x 0) (limbAt M x 1) (limbAt M x 2) (limbAt M x 3) (limbAt M x 4) (limbAt M x 5)
        (limbAt M x 6) (limbAt M x 7) (limbAt M x 8) (limbAt M x 9)) :
    feW M' o = sqL (feW M x) := by rw [← feW_words, h]; rfl

theorem feW_neg {M M' : Word → BitVec 8} {o x : Word}
    (h : (wordsAt M' o 10).map BitVec.toNat =
      feReduceSpec (feNegZ (limbs M x) 0).toNat (feNegZ (limbs M x) 1).toNat (feNegZ (limbs M x) 2).toNat
        (feNegZ (limbs M x) 3).toNat (feNegZ (limbs M x) 4).toNat (feNegZ (limbs M x) 5).toNat
        (feNegZ (limbs M x) 6).toNat (feNegZ (limbs M x) 7).toNat (feNegZ (limbs M x) 8).toNat
        (feNegZ (limbs M x) 9).toNat) :
    feW M' o = negL (feW M x) := by
  rw [← feW_words, h]
  have e := feNegZ_congr (limbs_limbF (M := M) (a := x))
  unfold negL
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide)]

theorem feW_condNeg {M M' : Word → BitVec 8} {x c : Word} (hc : c = 0 ∨ c = 1)
    (h : ∀ i, i < 10 → limbs M' x i = feCondNegW M x c i) :
    feW M' x = condNegL (feW M x) (c == 1) := by
  rw [feW_limbs_ofW h]
  rcases hc with rfl | rfl
  · rfl
  · show ofW (feCondNegW M x 1) = wl (negL (feW M x))
    have e := feNegZ_congr (limbs_limbF (M := M) (a := x))
    unfold wl negL feCondNegW
    simp only [ite_true]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
      e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide)]
    rfl

theorem feW_pw19 {M M' : Word → BitVec 8} {o x : Word} (h : ∀ i, i < 10 → limbs M' o i = pwT19 (limbs M x) i) :
    feW M' o = pw19L (feW M x) := by
  rw [feW_limbs_ofW h, pwT19_congr (limbs_limbF (M := M) (a := x))]; rfl

/-! ## Where `decompress` runs -/

abbrev DEC : Word := BitVec.ofNat 32 edDecompressAddress

/-- The code `decompress` runs and its callees', and the three field
elements it loads from the image. -/
structure DecEnv (M : Word → BitVec 8) : Prop where
  cod : CodeIn M DEC edDecompressCode
  l3 : CodeIn M (BitVec.ofNat 32 feLoad3Address) feLoad3Code
  l4 : CodeIn M (BitVec.ofNat 32 feLoad4Address) feLoad4Code
  red : CodeIn M (BitVec.ofNat 32 feReduceAddress) feReduceCode
  sq : CodeIn M (BitVec.ofNat 32 feSquareAddress) feSquareCode
  sqi : CodeIn M (BitVec.ofNat 32 feSquareInnerAddress) feSquareInnerCode
  sub : CodeIn M (BitVec.ofNat 32 feSubAddress) feSubCode
  add : CodeIn M (BitVec.ofNat 32 feAddAddress) feAddCode
  mul : CodeIn M (BitVec.ofNat 32 feMulAddress) feMulCode
  pw : CodeIn M (BitVec.ofNat 32 pow22501Address) pow22501Code
  pk : CodeIn M (BitVec.ofNat 32 fePow2kAddress) fePow2kCode
  ce : CodeIn M (BitVec.ofNat 32 feCtEqAddress) feCtEqCode
  tb : CodeIn M (BitVec.ofNat 32 feToBytesAddress) feToBytesCode
  cs : CodeIn M (BitVec.ofNat 32 ctEqSliceAddress) ctEqSliceCode
  cu : CodeIn M (BitVec.ofNat 32 ctEqU8Address) ctEqU8Code
  bb : CodeIn M (BitVec.ofNat 32 blackBoxU8Address) blackBoxU8Code
  neg : CodeIn M (BitVec.ofNat 32 feNegAddress) feNegCode
  fca : CodeIn M (BitVec.ofNat 32 feCondAssignAddress) feCondAssignCode
  isn : CodeIn M (BitVec.ofNat 32 feIsNegativeAddress) feIsNegativeCode
  cn : CodeIn M (BitVec.ofNat 32 feCondNegAddress) feCondNegCode
  mcs : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  mcb : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode

/-- The stack `decompress` may write: 0x6F0 bytes from `R`, aligned, all
below the code. -/
structure DecCtx (M0 : Word → BitVec 8) (R : Word) : Prop where
  E : DecEnv M0
  hR : R.toNat % 4 = 0
  hRw : R.toNat + 0x6F0 ≤ 0x40000000

/-- Between calls: `sp` is `R + 0x450`, the registers no code here writes
hold `r0`'s values, memory agrees with the entry memory `M0` outside the
stack, and the frame's top 28 bytes, where the prologue saved registers,
are as in `Ms`. -/
structure DecSt (M0 Ms : Word → BitVec 8) (R : Word) (r0 : Fin 32 → Word) (M : Word → BitVec 8) (nm : Machine)
    (off : Nat) : Prop where
  st : St M DEC nm off (reg nm)
  hsp : reg nm sp = R + BitVec.ofNat 32 0x450
  keep : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg nm q = r0 q
  agree : ∀ x, Sep R 0x6F0 x 1 → M x = M0 x
  slots : ∀ c, 0x6D4 ≤ c → c < 0x6F0 → M (R + BitVec.ofNat 32 c) = Ms (R + BitVec.ofNat 32 c)

/-- An operand a callee reads: aligned and apart from the callees' frames. -/
def OpOK (R x : Word) : Prop := x.toNat % 4 = 0 ∧ Sep x 40 R 0x450

section Ctx

variable {M0 Ms M : Word → BitVec 8} {R : Word} {r0 : Fin 32 → Word} {nm : Machine} {off : Nat}

theorem DecCtx.toNat_off (C : DecCtx M0 R) {c : Nat} (h : c ≤ 0x6F0) : (R + BitVec.ofNat 32 c).toNat = R.toNat + c := by
  have := C.hRw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem DecCtx.code (C : DecCtx M0 R) (hM : ∀ x, Sep R 0x6F0 x 1 → M x = M0 x) {b : Word} {code : List Nat}
    (hc : CodeIn M0 b code) (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn M b code :=
  hc.hi (fun x hx => hM x (sep_of_le (by have := C.hRw; omega) (by have := x.isLt; omega))) hb hbl

theorem DecCtx.hiSep (C : DecCtx M0 R) {c l : Nat} (h : c + l ≤ 0x6F0) {b : Word} {k : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + k ≤ 2 ^ 32) : Sep (R + BitVec.ofNat 32 c) l b k :=
  sep_of_le (by rw [C.toNat_off (by omega)]; have := C.hRw; omega) hbl

theorem DecCtx.offs (_ : DecCtx M0 R) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 0x6F0)
    (hd : d + k ≤ 0x6F0) : Sep (R + BitVec.ofNat 32 c) n (R + BitVec.ofNat 32 d) k :=
  sep_offsets R h (by omega) (by omega)

theorem DecCtx.offs0 (C : DecCtx M0 R) {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 0x6F0) :
    Sep R n (R + BitVec.ofNat 32 d) k := by
  have := C.offs (c := 0) (n := n) (d := d) (k := k) (Or.inl (by omega)) (by omega) hd
  rwa [add_ofNat_zero] at this

theorem DecCtx.inR (_ : DecCtx M0 R) {c l : Nat} (h : c + l ≤ 0x6F0) {x : Word} (hx : Sep R 0x6F0 x 1) :
    Sep (R + BitVec.ofNat 32 c) l x 1 := (hx.symm.subR h).symm

theorem DecCtx.hiSep0 (C : DecCtx M0 R) {l : Nat} (h : l ≤ 0x6F0) {b : Word} {k : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + k ≤ 2 ^ 32) : Sep R l b k := by
  have := C.hiSep (c := 0) (l := l) (by omega) hb hbl; rwa [add_ofNat_zero] at this

set_option maxRecDepth 20000 in
theorem DecCtx.pwCode (C : DecCtx M0 R) {c l : Nat} (h : c + l ≤ 0x6F0) :
    PwCode (BitVec.ofNat 32 pow22501Address) (R + BitVec.ofNat 32 c) l :=
  ⟨C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide),
    C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide),
    C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide),
    C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide),
    C.hiSep h (by decide) (by decide), C.hiSep h (by decide) (by decide)⟩

theorem DecCtx.even (_ : DecCtx M0 R) (k : Nat) (hk : k % 2 = 0) : (DEC + BitVec.ofNat 32 k).toNat % 2 = 0 :=
  even_at DEC (by decide) k hk

/-- A frame slot is apart from a callee's frame and from an output below 0x6D4. -/
theorem DecSt.keepSlots (D : DecSt M0 Ms R r0 M nm off) (C : DecCtx M0 R) {M' : Word → BitVec 8} {k n : Nat}
    (hk : k + n ≤ 0x6D4)
    (hf : ∀ z, Sep (R + BitVec.ofNat 32 k) n z 1 → Sep R 0x450 z 1 → M' z = M z) :
    ∀ c, 0x6D4 ≤ c → c < 0x6F0 → M' (R + BitVec.ofNat 32 c) = Ms (R + BitVec.ofNat 32 c) := fun c h1 h2 => by
  rw [hf _ (C.offs (Or.inl (by omega)) (by omega) (by omega)) (C.offs0 (by omega) (by omega)), D.slots c h1 h2]

theorem DecSt.keepAgree (D : DecSt M0 Ms R r0 M nm off) (C : DecCtx M0 R) {M' : Word → BitVec 8} {k n : Nat}
    (hk : k + n ≤ 0x6F0)
    (hf : ∀ z, Sep (R + BitVec.ofNat 32 k) n z 1 → Sep R 0x450 z 1 → M' z = M z) :
    ∀ x, Sep R 0x6F0 x 1 → M' x = M0 x := fun x hx => by
  rw [hf x (C.inR hk hx) (by have := hx.sub (c := 0) (l := 0x450) (by omega); rwa [add_ofNat_zero] at this),
    D.agree x hx]

theorem DecSt.keepSlots0 (D : DecSt M0 Ms R r0 M nm off) (C : DecCtx M0 R) {M' : Word → BitVec 8}
    (hf : ∀ z, Sep R 0x450 z 1 → M' z = M z) :
    ∀ c, 0x6D4 ≤ c → c < 0x6F0 → M' (R + BitVec.ofNat 32 c) = Ms (R + BitVec.ofNat 32 c) := fun c h1 h2 => by
  rw [hf _ (C.offs0 (by omega) (by omega)), D.slots c h1 h2]

theorem DecSt.keepAgree0 (D : DecSt M0 Ms R r0 M nm off) {M' : Word → BitVec 8}
    (hf : ∀ z, Sep R 0x450 z 1 → M' z = M z) : ∀ x, Sep R 0x6F0 x 1 → M' x = M0 x := fun x hx => by
  rw [hf x (by have := hx.sub (c := 0) (l := 0x450) (by omega); rwa [add_ofNat_zero] at this), D.agree x hx]

theorem DecSt.zero (D : DecSt M0 Ms R r0 M nm off) : reg nm 0 = 0 := D.st.zero

end Ctx

/-! ## One lemma per kind of call -/

section Calls

variable {M0 Ms M : Word → BitVec 8} {R : Word} {r0 : Fin 32 → Word} {nm : Machine} {off : Nat}

set_option maxRecDepth 20000 in
/-- A call of `mul` with the product at `R + k`. -/
theorem DecSt.mul (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feMulAddress) (hev : off % 2 = 0)
    {k : Nat} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (hx : OpOK R (reg nm a1)) (hy : OpOK R (reg nm a2)) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = mulL (feW M (reg nm a1)) (feW M (reg nm a2)) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFEC0 = R + BitVec.ofNat 32 0x310 := by rw [BitVec.add_assoc]; rfl
  have env : FeMEnv M (BitVec.ofNat 32 feMulAddress) (reg nm sp) (reg nm a0) (reg nm a1) (reg nm a2) := by
    rw [D.hsp, ha0]
    exact { hP := by decide
            code := C.code D.agree C.E.mul (by decide) (by decide)
            red := by
              rw [show (BitVec.ofNat 32 feMulAddress : Word) + 0xAF0 = BitVec.ofNat 32 feReduceAddress by decide]
              exact C.code D.agree C.E.red (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hout := aligned_add C.hR hk
            hx := hx.1
            hy := hy.1
            sGC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOR := C.hiSep (by omega) (by decide) (by decide)
            sOG := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide)
            sXG := by rw [eS]; exact hx.2.subR (by decide)
            sYG := by rw [eS]; exact hy.2.subR (by decide) }
  obtain ⟨n2, c2, u2, sp2, k2, w2, f2⟩ := D.st.callFeMulL hc h1 h2 hb (C.even _ (by omega)) env
  rw [D.hsp, ha0, eS] at f2
  rw [ha0] at w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR =>
    f2 z (by have := hR.sub (c := 0x310) (l := 0x140) (by decide); exact this) hz
  refine ⟨n2, c2, ⟨u2, by rw [sp2, D.hsp], fun q hq => ?_, D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩,
    w2, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), D.keep q hq]
  · exact k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)

set_option maxRecDepth 20000 in
/-- A call of `square` with the result at `R + k`. -/
theorem DecSt.sq (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feSquareAddress) (hev : off % 2 = 0)
    {k : Nat} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (hx : OpOK R (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = sqL (feW M (reg nm a1)) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFF50 = R + BitVec.ofNat 32 0x3A0 := by rw [BitVec.add_assoc]; rfl
  have env : FeSquareEnv M (BitVec.ofNat 32 feSquareAddress) (reg nm sp) (reg nm a0) (reg nm a1) := by
    rw [D.hsp, ha0]
    exact { hP := by decide
            code := C.code D.agree C.E.sq (by decide) (by decide)
            sqi := by
              rw [show (BitVec.ofNat 32 feSquareAddress : Word) + 0x26 = BitVec.ofNat 32 feSquareInnerAddress by decide]
              exact C.code D.agree C.E.sqi (by decide) (by decide)
            red := by
              rw [show (BitVec.ofNat 32 feSquareAddress : Word) + 0xFFFFFC8C = BitVec.ofNat 32 feReduceAddress by decide]
              exact C.code D.agree C.E.red (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hout := aligned_add C.hR hk
            hx := hx.1
            sGC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGI := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOR := C.hiSep (by omega) (by decide) (by decide)
            sOG := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide)
            sXG := by rw [eS]; exact hx.2.subR (by decide) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feSquare_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega))) (r1 sp (by decide))
  rw [mem1] at w2 f2
  rw [D.hsp, ha0, eS] at f2
  rw [ha0] at w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR =>
    f2 z (hR.sub (c := 0x3A0) (l := 0xB0) (by decide)) hz
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, D.hsp], fun q hq => ?_,
    D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩, feW_sq w2, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `sub` with the difference at `R + k`. -/
theorem DecSt.sub (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feSubAddress) (hev : off % 2 = 0)
    {k : Nat} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (hx : OpOK R (reg nm a1)) (hy : OpOK R (reg nm a2)) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = subL (feW M (reg nm a1)) (feW M (reg nm a2)) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eG : R + BitVec.ofNat 32 0x3A0 + 0xB0 = R + BitVec.ofNat 32 0x450 := by rw [BitVec.add_assoc]; rfl
  have env : FeSubEnv M (BitVec.ofNat 32 feSubAddress) (R + BitVec.ofNat 32 0x3A0) (reg nm a0) (reg nm a1)
      (reg nm a2) := by
    rw [ha0]
    exact { hP := by decide
            code := C.code D.agree C.E.sub (by decide) (by decide)
            red := by
              rw [show (BitVec.ofNat 32 feSubAddress : Word) + 0xFFFFF72E = BitVec.ofNat 32 feReduceAddress by decide]
              exact C.code D.agree C.E.red (by decide) (by decide)
            hG := aligned_add C.hR (by decide)
            hGt := by rw [C.toNat_off (by decide)]; have := C.hRw; omega
            hx := hx.1
            hy := hy.1
            hout := aligned_add C.hR hk
            sGC := C.hiSep (by decide) (by decide) (by decide)
            sGR := C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOG := C.offs (Or.inr (by omega)) (by omega) (by decide)
            sXG := hx.2.subR (by decide)
            sYG := hy.2.subR (by decide) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feSub_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega))) (by rw [r1 sp (by decide), D.hsp, eG])
  rw [mem1] at w2 f2
  rw [ha0] at f2 w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR =>
    f2 z (hR.sub (c := 0x3A0) (l := 0xB0) (by decide)) hz
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, eG], fun q hq => ?_,
    D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩, feW_sub w2, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `add` with the sum at `R + k`. -/
theorem DecSt.add (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feAddAddress) (hev : off % 2 = 0)
    {k : Nat} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (hx : OpOK R (reg nm a1)) (hy : OpOK R (reg nm a2))
    (hxw : (reg nm a1).toNat + 40 < 2 ^ 32) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = addL (feW M (reg nm a1)) (feW M (reg nm a2)) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eG : R + BitVec.ofNat 32 0x400 + 0x50 = R + BitVec.ofNat 32 0x450 := by rw [BitVec.add_assoc]; rfl
  have env : FeAddEnv M (BitVec.ofNat 32 feAddAddress) (R + BitVec.ofNat 32 0x400) (reg nm a0) (reg nm a1)
      (reg nm a2) := by
    rw [ha0]
    exact { hP := by decide
            code := C.code D.agree C.E.add (by decide) (by decide)
            mcS := by
              rw [show (BitVec.ofNat 32 feAddAddress : Word) + 0x5D88 = BitVec.ofNat 32 memcpyStubAddress by decide]
              exact C.code D.agree C.E.mcs (by decide) (by decide)
            mcB := by
              rw [show (BitVec.ofNat 32 feAddAddress : Word) + 0x5D90 = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
              exact C.code D.agree C.E.mcb (by decide) (by decide)
            hG := aligned_add C.hR (by decide)
            hGt := by rw [C.toNat_off (by decide)]; have := C.hRw; omega
            hy := hy.1
            hout := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            hx := hxw
            sGC := C.hiSep (by decide) (by decide) (by decide)
            sGS := C.hiSep (by decide) (by decide) (by decide)
            sGB := C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOB := C.hiSep (by omega) (by decide) (by decide)
            sOG := C.offs (Or.inr (by omega)) (by omega) (by decide)
            sXG := hx.2.subR (by decide)
            sYG := hy.2.subR (by decide) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feAdd_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega))) (by rw [r1 sp (by decide), D.hsp, eG])
  rw [mem1] at w2 f2
  rw [ha0] at f2 w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR =>
    f2 z (hR.sub (c := 0x400) (l := 0x50) (by decide)) hz
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, eG], fun q hq => ?_,
    D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩, feW_add w2, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `reduce` of the ten `u64`s at `R + j` with the result at `R + k`. -/
theorem DecSt.reduce (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feReduceAddress) (hev : off % 2 = 0)
    {k j : Nat} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4) (hj : j % 4 = 0) (hj1 : 0x450 ≤ j)
    (hj2 : j + 80 ≤ 0x6F0)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (ha1 : reg nm a1 = R + BitVec.ofNat 32 j) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = redL ((List.range 10).map (u64At M (R + BitVec.ofNat 32 j))) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFFE0 = R + BitVec.ofNat 32 0x430 := by rw [BitVec.add_assoc]; rfl
  have env : FREnv M (BitVec.ofNat 32 feReduceAddress) (reg nm sp) (reg nm a0) (reg nm a1) := by
    rw [D.hsp, ha0, ha1]
    exact { hP := by decide
            code := C.code D.agree C.E.red (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hout := aligned_add C.hR hk
            hzp := aligned_add C.hR hj
            sSC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOS := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide)
            sZS := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feReduce_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega))) (r1 sp (by decide))
  rw [mem1] at w2 f2
  rw [D.hsp, ha0, eS] at f2
  rw [ha0, ha1] at w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR =>
    f2 z (hR.sub (c := 0x430) (l := 0x20) (by decide)) hz
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, D.hsp], fun q hq => ?_,
    D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩, feW_of_words w2, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `pow22501` with the result pair at `R + k`; the first of the
pair is `pw19L` of the operand. -/
theorem DecSt.pow22501 (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 pow22501Address) (hev : off % 2 = 0)
    {k : Nat} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 0x50 ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (hx : OpOK R (reg nm a1)) (hxo : Sep (reg nm a1) 40 (R + BitVec.ofNat 32 k) 0x50) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = pw19L (feW M (reg nm a1)) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 0x50 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFBB0 = R := by rw [BitVec.add_assoc]; exact BitVec.add_zero R
  have cd : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn M b code := fun hc' h1 h2 => C.code D.agree hc' h1 h2
  have env : PWEnv M (BitVec.ofNat 32 pow22501Address) (reg nm sp) (reg nm a0) (reg nm a1) := by
    rw [D.hsp, ha0]
    exact { hP := by decide
            cod := cd C.E.pw (by decide) (by decide)
            sq := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x1A8 = BitVec.ofNat 32 feSquareAddress by decide]
              exact cd C.E.sq (by decide) (by decide)
            sqi := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x1A8 + 0x26 = BitVec.ofNat 32 feSquareInnerAddress by
                decide]
              exact cd C.E.sqi (by decide) (by decide)
            sqR := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x1A8 + 0xFFFFFC8C = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact cd C.E.red (by decide) (by decide)
            mul := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0xFFFFF344 = BitVec.ofNat 32 feMulAddress by decide]
              exact cd C.E.mul (by decide) (by decide)
            mulR := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0xFFFFF344 + 0xAF0 = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact cd C.E.red (by decide) (by decide)
            pk := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 = BitVec.ofNat 32 fePow2kAddress by decide]
              exact cd C.E.pk (by decide) (by decide)
            pkS := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0x52 = BitVec.ofNat 32 feSquareAddress by decide]
              exact cd C.E.sq (by decide) (by decide)
            pkI := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0x78 = BitVec.ofNat 32 feSquareInnerAddress by
                decide]
              exact cd C.E.sqi (by decide) (by decide)
            pkR := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0xFFFFFCDE = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact cd C.E.red (by decide) (by decide)
            pkMS := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0x62EA = BitVec.ofNat 32 memcpyStubAddress by
                decide]
              exact cd C.E.mcs (by decide) (by decide)
            pkMB := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x156 + 0x62F2 = BitVec.ofNat 32 memcpyStubAddress + 8 by
                decide]
              exact cd C.E.mcb (by decide) (by decide)
            mcS := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x6440 = BitVec.ofNat 32 memcpyStubAddress by decide]
              exact cd C.E.mcs (by decide) (by decide)
            mcB := by
              rw [show (BitVec.ofNat 32 pow22501Address : Word) + 0x6440 + 8 = BitVec.ofNat 32 memcpyStubAddress + 8 by
                decide]
              exact cd C.E.mcb (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hout := aligned_add C.hR hk
            hxp := hx.1
            how := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            sG := by rw [eS]; have := C.pwCode (c := 0) (l := 0x450) (by decide); rwa [add_ofNat_zero] at this
            sO := C.pwCode (by omega)
            sOG := by rw [eS]; exact (C.offs0 (by omega) (by omega)).symm
            sXG := by rw [eS]; exact hx.2
            sXO := hxo }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := pow22501_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega)))
  rw [mem1] at w2 f2
  rw [D.hsp, ha0, eS] at f2
  rw [ha0] at w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 0x50 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR => f2 z hR hz
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, D.hsp], fun q hq => ?_,
    D.keepAgree C (n := 0x50) (by omega) fr, D.keepSlots C hk2 fr⟩, feW_pw19 fun i hi => (w2 i hi).1,
    fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `pow2k` with the result at `R + k`. -/
theorem DecSt.pow2k (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word} {e : Nat}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 fePow2kAddress) (hev : off % 2 = 0)
    (he0 : 0 < e) (he1 : e < 2 ^ 32)
    {k : Nat} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (hx : OpOK R (reg nm a1)) (ha2 : reg nm a2 = BitVec.ofNat 32 e) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = sqIter e (feW M (reg nm a1)) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eG : R + BitVec.ofNat 32 0x340 + 0x110 = R + BitVec.ofNat 32 0x450 := by rw [BitVec.add_assoc]; rfl
  have cd : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn M b code := fun hc' h1 h2 => C.code D.agree hc' h1 h2
  have env : FpkEnv M (BitVec.ofNat 32 fePow2kAddress) (R + BitVec.ofNat 32 0x340) (reg nm a0) (reg nm a1) := by
    rw [ha0]
    exact { hP := by decide
            code := cd C.E.pk (by decide) (by decide)
            sq := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0x52 = BitVec.ofNat 32 feSquareAddress by decide]
              exact cd C.E.sq (by decide) (by decide)
            sqi := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0x78 = BitVec.ofNat 32 feSquareInnerAddress by decide]
              exact cd C.E.sqi (by decide) (by decide)
            red := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0xFFFFFCDE = BitVec.ofNat 32 feReduceAddress by decide]
              exact cd C.E.red (by decide) (by decide)
            mcS := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0x62EA = BitVec.ofNat 32 memcpyStubAddress by decide]
              exact cd C.E.mcs (by decide) (by decide)
            mcB := by
              rw [show (BitVec.ofNat 32 fePow2kAddress : Word) + 0x62F2 = BitVec.ofNat 32 memcpyStubAddress + 8 by decide]
              exact cd C.E.mcb (by decide) (by decide)
            hG := aligned_add C.hR (by decide)
            hGt := by rw [C.toNat_off (by decide)]; have := C.hRw; omega
            hout := aligned_add C.hR hk
            hot := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            hx := hx.1
            sGC := C.hiSep (by decide) (by decide) (by decide)
            sGQ := C.hiSep (by decide) (by decide) (by decide)
            sGI := C.hiSep (by decide) (by decide) (by decide)
            sGR := C.hiSep (by decide) (by decide) (by decide)
            sGM := C.hiSep (by decide) (by decide) (by decide)
            sGB := C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOB := C.hiSep (by omega) (by decide) (by decide)
            sOG := C.offs (Or.inr (by omega)) (by omega) (by decide)
            sXG := hx.2.subR (by decide) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := fePow2k_correct n1 (by rw [mem1]; exact env) he0 he1 pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [r1 a2 (by decide), ha2]) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega))) (by rw [r1 sp (by decide), D.hsp, eG])
  rw [mem1] at w2 f2
  rw [ha0] at f2 w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR =>
    f2 z (hR.sub (c := 0x340) (l := 0x110) (by decide)) hz
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, eG], fun q hq => ?_,
    D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩, w2, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `ct_eq`. -/
theorem DecSt.ctEq (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feCtEqAddress) (hev : off % 2 = 0)
    (hx : OpOK R (reg nm a0)) (hy : OpOK R (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      reg nm' a0 = (if bytesL (feW M (reg nm a0)) = bytesL (feW M (reg nm a1)) then 1 else 0) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFF00 = R + BitVec.ofNat 32 0x350 := by rw [BitVec.add_assoc]; rfl
  have cd : ∀ {b : Word} {code : List Nat}, CodeIn M0 b code → 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn M b code := fun hc' h1 h2 => C.code D.agree hc' h1 h2
  have env : FCEEnv M (BitVec.ofNat 32 feCtEqAddress) (reg nm sp) (reg nm a0) (reg nm a1) := by
    rw [D.hsp]
    exact { hP := by decide
            cod := cd C.E.ce (by decide) (by decide)
            tb := by
              rw [show (BitVec.ofNat 32 feCtEqAddress : Word) + 0xFFFFE096 = BitVec.ofNat 32 feToBytesAddress by decide]
              exact cd C.E.tb (by decide) (by decide)
            red := by
              rw [show (BitVec.ofNat 32 feCtEqAddress : Word) + 0xFFFFE096 + 0x210 = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact cd C.E.red (by decide) (by decide)
            cs := by
              rw [show (BitVec.ofNat 32 feCtEqAddress : Word) + 0xFFFFEF72 = BitVec.ofNat 32 ctEqSliceAddress by decide]
              exact cd C.E.cs (by decide) (by decide)
            ce := by
              rw [show (BitVec.ofNat 32 feCtEqAddress : Word) + 0xFFFFEF72 + 0xFFFFFFE8 = BitVec.ofNat 32 ctEqU8Address by
                decide]
              exact cd C.E.cu (by decide) (by decide)
            bb := by
              rw [show (BitVec.ofNat 32 feCtEqAddress : Word) + 0xFFFFEF72 + 0xFFFFE836 = BitVec.ofNat 32 blackBoxU8Address by
                decide]
              exact cd C.E.bb (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hxp := hx.1
            hyp := hy.1
            sGC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGT := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGS := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGE := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGB := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sXG := by rw [eS]; exact hx.2.subR (by decide)
            sYG := by rw [eS]; exact hy.2.subR (by decide) }
  obtain ⟨n2, c2, u2, sp2, a02, k2, f2⟩ := D.st.callFeCtEq hc h1 h2 hb (C.even _ (by omega)) env
  rw [D.hsp, eS] at f2
  have fr : ∀ z, Sep R 0x450 z 1 → n2.mem z = M z := fun z hR => f2 z (hR.sub (c := 0x350) (l := 0x100) (by decide))
  refine ⟨n2, c2, ⟨u2, by rw [sp2, D.hsp], fun q hq => ?_, D.keepAgree0 fr, D.keepSlots0 C fr⟩, a02,
    fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), D.keep q hq]
  · exact k2 q (by revert hq; revert q; decide)

set_option maxRecDepth 20000 in
/-- A call of `neg` with the result at `R + k`. -/
theorem DecSt.neg (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feNegAddress) (hev : off % 2 = 0)
    {k : Nat} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (hx : OpOK R (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = negL (feW M (reg nm a1)) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFF60 = R + BitVec.ofNat 32 0x3B0 := by rw [BitVec.add_assoc]; rfl
  have env : FNEnv M (BitVec.ofNat 32 feNegAddress) (reg nm sp) (reg nm a0) (reg nm a1) := by
    rw [D.hsp, ha0]
    exact { hP := by decide
            cod := C.code D.agree C.E.neg (by decide) (by decide)
            red := by
              rw [show (BitVec.ofNat 32 feNegAddress : Word) + 0xFFFFE370 = BitVec.ofNat 32 feReduceAddress by decide]
              exact C.code D.agree C.E.red (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hout := aligned_add C.hR hk
            hip := hx.1
            sGC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sOC := C.hiSep (by omega) (by decide) (by decide)
            sOG := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide)
            sIG := by rw [eS]; exact hx.2.subR (by decide) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feNeg_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega)))
  rw [mem1] at w2 f2
  rw [D.hsp, ha0, eS] at f2
  rw [ha0] at w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR =>
    f2 z (hR.sub (c := 0x3B0) (l := 0xA0) (by decide)) hz
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, D.hsp], fun q hq => ?_,
    D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩, feW_neg w2, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `conditional_assign` of `R + j` to `R + k` on the choice `c`. -/
theorem DecSt.condAssign (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feCondAssignAddress) (hev : off % 2 = 0)
    {k j : Nat} {c : Word} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4) (hj : j % 4 = 0)
    (hj2 : j + 40 ≤ 0x6F0) (hkj : k + 40 ≤ j ∨ j + 40 ≤ k)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (ha1 : reg nm a1 = R + BitVec.ofNat 32 j) (ha2 : reg nm a2 = c)
    (hc01 : c = 0 ∨ c = 1) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) =
        (if c = 1 then feW M (R + BitVec.ofNat 32 j) else feW M (R + BitVec.ofNat 32 k)) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, k2, w2, f2⟩ := feCondAssign_correct n1
    (by rw [mem1]; exact C.code D.agree C.E.fca (by decide) (by decide)) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) hc01 (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega))) (aligned_add C.hR hk) (aligned_add C.hR hj)
    (by rw [C.toNat_off (by omega)]; have := C.hRw; omega) (C.hiSep (by omega) (by decide) (by decide))
    (C.offs hkj (by omega) (by omega))
  rw [mem1] at w2 f2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz _ => f2 z hz
  have hw : feW n2.mem (R + BitVec.ofNat 32 k) =
      (if c = 1 then feW M (R + BitVec.ofNat 32 j) else feW M (R + BitVec.ofNat 32 k)) := by
    by_cases h : c = 1
    · simp only [h, ↓reduceIte]; exact feW_limbs_eq fun i hi => by rw [w2 i hi]; simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]; exact feW_limbs_eq fun i hi => by rw [w2 i hi]; simp only [h, ↓reduceIte]
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [k2 sp (by decide), r1 sp (by decide), D.hsp],
    fun q hq => ?_, D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩, hw, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `is_negative`. -/
theorem DecSt.isNeg (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feIsNegativeAddress) (hev : off % 2 = 0)
    (hx : OpOK R (reg nm a0)) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      reg nm' a0 = BitVec.ofNat 32 ((bytesL (feW M (reg nm a0))).getD 0 0 % 2) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFF20 = R + BitVec.ofNat 32 0x370 := by rw [BitVec.add_assoc]; rfl
  have env : FINEnv M (BitVec.ofNat 32 feIsNegativeAddress) (reg nm sp) (reg nm a0) := by
    rw [D.hsp]
    exact { hP := by decide
            cod := C.code D.agree C.E.isn (by decide) (by decide)
            tb := by
              rw [show (BitVec.ofNat 32 feIsNegativeAddress : Word) + 0xFFFFE2E6 = BitVec.ofNat 32 feToBytesAddress by
                decide]
              exact C.code D.agree C.E.tb (by decide) (by decide)
            red := by
              rw [show (BitVec.ofNat 32 feIsNegativeAddress : Word) + 0xFFFFE2E6 + 0x210 = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact C.code D.agree C.E.red (by decide) (by decide)
            bb := by
              rw [show (BitVec.ofNat 32 feIsNegativeAddress : Word) + 0xFFFFD9F8 = BitVec.ofNat 32 blackBoxU8Address by
                decide]
              exact C.code D.agree C.E.bb (by decide) (by decide)
            hsp := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hfp := hx.1
            sGC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGT := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGB := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sFG := by rw [eS]; exact hx.2.subR (by decide) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, a02, k2, f2⟩ := feIsNegative_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega)))
  rw [mem1, feBytesOf_eq] at a02
  rw [mem1, D.hsp, eS] at f2
  have fr : ∀ z, Sep R 0x450 z 1 → n2.mem z = M z := fun z hR => f2 z (hR.sub (c := 0x370) (l := 0xE0) (by decide))
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, D.hsp], fun q hq => ?_,
    D.keepAgree0 fr, D.keepSlots0 C fr⟩, a02, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `conditional_negate` of the element at `R + k` on the choice `c`. -/
theorem DecSt.condNeg (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feCondNegAddress) (hev : off % 2 = 0)
    {k : Nat} {c : Word} (hk : k % 4 = 0) (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (ha1 : reg nm a1 = c) (hc01 : c = 0 ∨ c = 1) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = condNegL (feW M (R + BitVec.ofNat 32 k)) (c == 1) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFF20 = R + BitVec.ofNat 32 0x370 := by rw [BitVec.add_assoc]; rfl
  have env : FCNEnv M (BitVec.ofNat 32 feCondNegAddress) (reg nm sp) (reg nm a0) := by
    rw [D.hsp, ha0]
    exact { hP := by decide
            cod := C.code D.agree C.E.cn (by decide) (by decide)
            neg := by
              rw [show (BitVec.ofNat 32 feCondNegAddress : Word) + 0x164 = BitVec.ofNat 32 feNegAddress by decide]
              exact C.code D.agree C.E.neg (by decide) (by decide)
            red := by
              rw [show (BitVec.ofNat 32 feCondNegAddress : Word) + 0x164 + 0xFFFFE370 = BitVec.ofNat 32 feReduceAddress by
                decide]
              exact C.code D.agree C.E.red (by decide) (by decide)
            fca := by
              rw [show (BitVec.ofNat 32 feCondNegAddress : Word) + 0x30 = BitVec.ofNat 32 feCondAssignAddress by decide]
              exact C.code D.agree C.E.fca (by decide) (by decide)
            hsa := aligned_add C.hR (by decide)
            hS := by rw [C.toNat_off (by decide)]; omega
            hx := aligned_add C.hR hk
            hxw := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            sGC := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGN := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGR := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sGA := by rw [eS]; exact C.hiSep (by decide) (by decide) (by decide)
            sXG := by rw [eS]; exact C.offs (Or.inr (by omega)) (by omega) (by decide)
            sXA := C.hiSep (by omega) (by decide) (by decide)
            sXC := C.hiSep (by omega) (by decide) (by decide) }
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feCondNeg_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (by rw [r1 a1 (by decide), ha1]) hc01 (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega)))
  rw [mem1] at w2 f2
  rw [D.hsp, ha0, eS] at f2
  rw [ha0] at w2
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR =>
    f2 z (hR.sub (c := 0x370) (l := 0xE0) (by decide)) hz
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, D.hsp], fun q hq => ?_,
    D.keepAgree C (n := 40) (by omega) fr, D.keepSlots C hk2 fr⟩, feW_condNeg hc01 w2, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
/-- A call of `subtle::black_box::<u8>`. -/
theorem DecSt.blackBox (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 blackBoxU8Address) (hev : off % 2 = 0) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      reg nm' a0 = ((reg nm a0).extractLsb' 0 8).zeroExtend 32 ∧
      (∀ q, q ≠ a0 → q ≠ ra → reg nm' q = reg nm q) ∧
      ∀ z, Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFFFF = R + BitVec.ofNat 32 0x44F := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, a02, k2, f2⟩ := blackBoxU8_correct n1
    (by rw [mem1]; exact C.code D.agree C.E.bb (by decide) (by decide)) pc1
    (by rw [regs1]; simp +decide [upd]) (even_clear _ (C.even (off + 8) (by omega)))
    (by rw [r1 sp (by decide), D.hsp, eS]; exact C.hiSep (by decide) (by decide) (by decide))
  rw [mem1, r1 sp (by decide), D.hsp, eS] at f2
  rw [r1 a0 (by decide)] at a02
  have fr : ∀ z, Sep R 0x450 z 1 → n2.mem z = M z := fun z hR => f2 z (hR.sub (c := 0x44F) (l := 1) (by decide))
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [k2 sp (by decide), r1 sp (by decide), D.hsp],
    fun q hq => ?_, D.keepAgree0 fr, D.keepSlots0 C fr⟩, a02, fun q h0 hr => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q h0, r1 q hr]

set_option maxRecDepth 20000 in
/-- A call of `load3_at` on the bytes at `b + i`. -/
theorem DecSt.load3 (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feLoad3Address) (hev : off % 2 = 0) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 M nm' (off + 8) ∧
      (reg nm' a0).toNat = (M (reg nm a0 + reg nm a1)).toNat + 2 ^ 8 * (M (reg nm a0 + reg nm a1 + 1)).toNat +
        2 ^ 16 * (M (reg nm a0 + reg nm a1 + 2)).toNat ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ ra → reg nm' q = reg nm q) := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, a02, _, k2, mem2⟩ := feLoad3_correct n1
    (by rw [mem1]; exact C.code D.agree C.E.l3 (by decide) (by decide)) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega)))
  rw [mem1] at a02
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], by rw [mem2, mem1], fun _ => rfl⟩,
    by rw [k2 sp (by decide) (by decide) (by decide), r1 sp (by decide), D.hsp], fun q hq => ?_, D.agree, D.slots⟩,
    a02, fun q h0 h1' h2' hr => ?_⟩
  · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q h0 h1' h2', r1 q hr]

set_option maxRecDepth 20000 in
/-- A call of `load4_at` on the bytes at `b + i`. -/
theorem DecSt.load4 (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 feLoad4Address) (hev : off % 2 = 0) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 M nm' (off + 8) ∧
      (reg nm' a0).toNat = (M (reg nm a0 + reg nm a1)).toNat + 2 ^ 8 * (M (reg nm a0 + reg nm a1 + 1)).toNat +
        2 ^ 16 * (M (reg nm a0 + reg nm a1 + 2)).toNat + 2 ^ 24 * (M (reg nm a0 + reg nm a1 + 3)).toNat ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg nm' q = reg nm q) := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  obtain ⟨n2, c2, pc2, a02, _, k2, mem2⟩ := feLoad4_correct n1
    (by rw [mem1]; exact C.code D.agree C.E.l4 (by decide) (by decide)) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ (C.even (off + 8) (by omega)))
  rw [mem1] at a02
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], by rw [mem2, mem1], fun _ => rfl⟩,
    by rw [k2 sp (by decide) (by decide) (by decide) (by decide), r1 sp (by decide), D.hsp], fun q hq => ?_, D.agree,
    D.slots⟩, a02, fun q h0 h1' h2' h3' hr => ?_⟩
  · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide), D.keep q hq]
  · rw [k2 q h0 h1' h2' h3', r1 q hr]

set_option maxRecDepth 20000 in
/-- A call of `memcpy` of `N` bytes from `src` to `R + k`. -/
theorem DecSt.memcpy (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm off) {imm o src : Word} {N : Nat}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memcpyStubAddress) (hev : off % 2 = 0)
    {k : Nat} (hk1 : 0x450 ≤ k) (hk2 : k + N ≤ 0x6D4)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (ha1 : reg nm a1 = src) (ha2 : reg nm a2 = BitVec.ofNat 32 N)
    (hsS : Sep src N R 0x450) (hsw : src.toNat + N < 2 ^ 32) (hsep : Sep (R + BitVec.ofNat 32 k) N src N) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      (∀ x, Sep R 0x450 x 1 → nm'.mem x = copyBytes M (R + BitVec.ofNat 32 k) src N x) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) N z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  have hc : CodeIn M DEC edDecompressCode := C.code D.agree C.E.cod (by decide) (by decide)
  have eS : R + BitVec.ofNat 32 0x450 + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x440 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := D.st.callRa hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 D.zero
  have E : McEnv n1.mem (BitVec.ofNat 32 memcpyStubAddress + 8) (R + BitVec.ofNat 32 k) src
      (reg n1 sp + 0xFFFFFFF0) N := by
    rw [mem1, r1 sp (by decide), D.hsp, eS]
    exact { code := C.code D.agree C.E.mcb (by decide) (by decide)
            hDC := C.hiSep (by omega) (by decide) (by decide)
            hFC := C.hiSep (by decide) (by decide) (by decide)
            hdF := C.offs (Or.inr (by omega)) (by omega) (by decide)
            hsF := hsS.subR (by decide)
            hsep := hsep
            hF := aligned_add C.hR (by decide)
            hFw := by rw [C.toNat_off (by decide)]; have := C.hRw; omega
            hdw := by rw [C.toNat_off (by omega)]; have := C.hRw; omega
            hsw := hsw }
  obtain ⟨n2, c2, pc2, sp2, _, f2, k2⟩ := memcpy_correct n1 (BitVec.ofNat 32 memcpyStubAddress)
    (DEC + BitVec.ofNat 32 (off + 8)) (R + BitVec.ofNat 32 k) src N
    (fun i hi => by rw [mem1]; exact C.code D.agree C.E.mcs (by decide) (by decide) i hi) (by decide) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ (C.even (off + 8) (by omega))) E
  rw [mem1, r1 sp (by decide), D.hsp, eS] at f2
  have cp : ∀ x, Sep R 0x450 x 1 → n2.mem x = copyBytes M (R + BitVec.ofNat 32 k) src N x := fun x hR =>
    f2 x (hR.sub (c := 0x440) (l := 16) (by decide))
  have fr : ∀ z, Sep (R + BitVec.ofNat 32 k) N z 1 → Sep R 0x450 z 1 → n2.mem z = M z := fun z hz hR => by
    rw [cp z hR, copyBytes_sep hz (Nat.le_refl N)]
  refine ⟨n2, c1.trans c2, ⟨⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, r1 sp (by decide), D.hsp], fun q hq => ?_,
    D.keepAgree C (n := N) (by omega) fr, D.keepSlots C hk2 fr⟩, cp, fun q hq => ?_, fr⟩
  · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide),
      D.keep q hq]
  · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]

end Calls

end C3.RV32
