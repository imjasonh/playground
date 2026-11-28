import C3BootProofs.Proofs.TufParseMetadataAt
import C3BootProofs.Proofs.TufMetaCalls
import C3BootProofs.Proofs.TufExpires
import C3BootProofs.Proofs.FeLoad
import C3BootProofs.Proofs.ShrWide12

/-!
# `tuf::parse_metadata`, as compiled

`parse_metadata(doc, kind)` parses the `n` bytes at `p` with `json::parse`
in canonical mode, so the top value is an object whose keys are sorted and
distinct. The object must have exactly two members, `signatures` and then
`signed`, in that order. `signed` must have a string `_type` whose body is
`kind`, and `signatures` must be an array whose elements each have a string
`keyid` and a string `sig`, with no key ID repeated in a later element. The
function returns the `signed` and `signatures` values, or an error byte:
`0x20` for JSON outside the profile and `0x21` for metadata of the wrong
shape.

`pmModel` gives the result on the document's bytes as positions in the
document. `tufParseMetadata_correct` is the machine-level contract: with
`sp = s + 532`, the function writes the result at `out` in the layout
`PmRes` describes and changes memory only in the 532 bytes at `s` and the
16 bytes at `out`.
-/

namespace C3.Json

/-- The rest of a check after `r`: `k` when `r` succeeded. -/
def pmThen {α : Type} (r : Except Nat Unit) (k : Except Nat α) : Except Nat α :=
  match r with
  | .error e => .error e
  | .ok () => k

/-- The inner loop over the signatures array `a` from `pos`: no element
has the key ID `kid`. -/
def pmLater (a kid : Bytes) : Nat → Nat → Except Nat Unit
  | 0, _ => .error 0x20
  | k + 1, pos =>
    match nextElement a pos with
    | none => .error 0x20
    | some none => .ok ()
    | some (some (ep, el, nx)) =>
      match objField (slice a ep el) (ascii!"keyid") with
      | .error e => .error e
      | .ok (kp, kl) =>
        match strBody (slice (slice a ep el) kp kl) with
        | none => .error 0x21
        | some k2 => if k2 = kid then .error 0x21 else pmLater a kid k nx

/-- The outer loop over the signatures array `a` from `pos`: each element
has a string `keyid` and a string `sig`, and no later element repeats the
key ID. -/
def pmSigs (a : Bytes) : Nat → Nat → Except Nat Unit
  | 0, _ => .error 0x20
  | k + 1, pos =>
    match nextElement a pos with
    | none => .error 0x20
    | some none => .ok ()
    | some (some (ep, el, nx)) =>
      match objField (slice a ep el) (ascii!"keyid") with
      | .error e => .error e
      | .ok (kp, kl) =>
        match strBody (slice (slice a ep el) kp kl) with
        | none => .error 0x21
        | some kid =>
          match objField (slice a ep el) (ascii!"sig") with
          | .error e => .error e
          | .ok (sp, sl) =>
            match strBody (slice (slice a ep el) sp sl) with
            | none => .error 0x21
            | some _ => pmThen (pmLater a kid (a.length + 1) nx) (pmSigs a k nx)

/-- The checks on the `signatures` array `a`. -/
def pmArr (a : Bytes) : Except Nat Unit :=
  if a.length = 0 ∨ a.getD 0 0 ≠ 91 then .error 0x21 else pmSigs a (a.length + 1) (skipWs a 1)

/-- The checks on `signed`, the value `v`, once the object has no third
member: a string `_type` whose body is `kind`, then the checks on the
`signatures` value `a`. -/
def pmTy (v a kind : Bytes) : Except Nat Unit :=
  match objField v (ascii!"_type") with
  | .error e => .error e
  | .ok (yp, yl) =>
    match strBody (slice v yp yl) with
    | none => .error 0x21
    | some ty => if ty = kind then pmArr a else .error 0x21

/-- The checks on the top-level object `t` after its two members, from `a2`. -/
def pmRest (t kind : Bytes) (a2 v1p v1l v2p v2l : Nat) : Except Nat Unit :=
  match nextMember t a2 with
  | none => .error 0x20
  | some (some _) => .error 0x21
  | some none => pmTy (slice t v2p v2l) (slice t v1p v1l) kind

/-- The second member of `t`, from `a1`, and the checks after it, given the
first member's key and value. -/
def pmTwo (t kind : Bytes) (a1 k1p k1l v1p v1l : Nat) : Except Nat (Nat × Nat × Nat × Nat) :=
  match nextMember t a1 with
  | none => .error 0x20
  | some none => .error 0x21
  | some (some (k2p, k2l, v2p, v2l, a2)) =>
    if slice t k1p k1l = ascii!"signatures" ∧ slice t k2p k2l = ascii!"signed" then
      pmThen (pmRest t kind a2 v1p v1l v2p v2l) (.ok (v2p, v2l, v1p, v1l))
    else .error 0x21

/-- The members of the object `t` from `pos`. -/
def pmMembers (t kind : Bytes) (pos : Nat) : Except Nat (Nat × Nat × Nat × Nat) :=
  match nextMember t pos with
  | none => .error 0x20
  | some none => .error 0x21
  | some (some (k1p, k1l, v1p, v1l, a1)) => pmTwo t kind a1 k1p k1l v1p v1l

/-- The checks on the top-level object `t`, and the positions in `t` of
`signed` and `signatures`. -/
def pmObj (t kind : Bytes) : Except Nat (Nat × Nat × Nat × Nat) :=
  if t.length = 0 ∨ t.getD 0 0 ≠ 123 then .error 0x21 else pmMembers t kind (skipWs t 1)

/-- `tuf::parse_metadata` on the document `d` and the type `kind`: the
positions in `d` of `signed` and `signatures`, or the error byte. -/
def pmModel (d kind : Bytes) : Except Nat (Nat × Nat × Nat × Nat) :=
  match parseModel true d with
  | .error e => .error e
  | .ok (tp, tl) =>
    match pmObj (slice d tp tl) kind with
    | .error e => .error e
    | .ok (a, b, c, e) => .ok (tp + a, b, tp + c, e)

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

abbrev TPM_JP : Word := BitVec.ofNat 32 jsonParseAddress
abbrev TPM_JF : Word := BitVec.ofNat 32 jsonFieldAddress
abbrev TPM_JS : Word := BitVec.ofNat 32 jsonStrAddress
abbrev TPM_JEL : Word := BitVec.ofNat 32 jsonElementsAddress
abbrev TPM_JNE : Word := BitVec.ofNat 32 jsonNextElementAddress
abbrev TPM_KS : Word := BitVec.ofNat 32 tufSignaturesKeyAddress
abbrev TPM_KT : Word := BitVec.ofNat 32 tufTypeKeyAddress
abbrev TPM_KK : Word := BitVec.ofNat 32 tufKeyidKeyAddress
abbrev TPM_KG : Word := BitVec.ofNat 32 tufSigKeyAddress
/-- `json::get`, which `parse` and `field` call, and whose callees
`parse_metadata` also calls. -/
abbrev TPM_JG : Word := TPM_JP + 0xFFFFF372

/-- The code `parse_metadata` runs, and the keys it compares. -/
structure PmCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M TPM tufParseMetadataCode
  parse : ParseCode M TPM_JP
  field : CodeIn M TPM_JF jsonFieldCode
  str : CodeIn M TPM_JS jsonStrCode
  el : CodeIn M TPM_JEL jsonElementsCode
  ne : CodeIn M TPM_JNE jsonNextElementCode
  ks : CodeIn M TPM_KS tufSignaturesKeyData
  kt : CodeIn M TPM_KT tufTypeKeyData
  kk : CodeIn M TPM_KK tufKeyidKeyData
  kg : CodeIn M TPM_KG tufSigKeyData

/-- The stack below the code and apart from the read-only window is apart
from `parse` and its callees at their addresses in the image. -/
theorem tpm_parseSep {s : Word} {k : Nat} (hs : s.toNat + k ≤ 0x40000000)
    (hro : Sep s k (BitVec.ofNat 32 roWindowAddress) roWindowSize) : ParseSep s k TPM_JP := by
  have hg := (tuf_fieldSep hs hro).get
  rw [show BitVec.ofNat 32 jsonFieldAddress + 0x16C = TPM_JG by decide] at hg
  exact ⟨lowSep hs (by decide) (by decide), hg, lowSep hs (by decide) (by decide)⟩

section
variable {M M' : Word → BitVec 8} {s : Word} {k : Nat}

theorem tpm_codeIn {b : Word} {code : List Nat} (h : CodeIn M b code) (hO : Out M M' s k)
    (hs : s.toNat + k ≤ 0x40000000) (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + code.length ≤ 2 ^ 32) :
    CodeIn M' b code :=
  hO.codeIn h (lowSep hs hb hbl)

theorem PmCode.of_out (h : PmCode M) (hO : Out M M' s k) (hs : s.toNat + k ≤ 0x40000000)
    (hro : Sep s k (BitVec.ofNat 32 roWindowAddress) roWindowSize) : PmCode M' :=
  ⟨tpm_codeIn h.self hO hs (by decide) (by decide), h.parse.out hO (tpm_parseSep hs hro),
    tpm_codeIn h.field hO hs (by decide) (by decide), tpm_codeIn h.str hO hs (by decide) (by decide),
    tpm_codeIn h.el hO hs (by decide) (by decide), tpm_codeIn h.ne hO hs (by decide) (by decide),
    hO.codeIn h.ks (tuf_sep_ro hro (by decide) (by decide)), hO.codeIn h.kt (tuf_sep_ro hro (by decide) (by decide)),
    hO.codeIn h.kk (tuf_sep_ro hro (by decide) (by decide)), hO.codeIn h.kg (tuf_sep_ro hro (by decide) (by decide))⟩

theorem PmCode.get (h : PmCode M) : GetCode M TPM_JG := h.parse.get

theorem PmCode.fieldC (h : PmCode M) : FieldCode M TPM_JF :=
  ⟨h.field, by rw [show TPM_JF + 0x16C = TPM_JG by decide]; exact h.get⟩

theorem PmCode.ri (h : PmCode M) : RiCode M (TPM_JNE + 0xFFFFF7E0) := by
  rw [show TPM_JNE + 0xFFFFF7E0 = TPM_JG + 0xFFFFF616 by decide]; exact h.get.ri

theorem PmCode.sw (h : PmCode M) : CodeIn M (TPM_JEL + 0xFFFFFAB2) jsonSkipWsCode := by
  rw [show TPM_JEL + 0xFFFFFAB2 = TPM_JG + 0xFFFFF616 + 0x288 by decide]; exact h.get.ri.sw

theorem PmCode.mc (h : PmCode M) : CodeIn M (BitVec.ofNat 32 memcmpAddress) memcmpCode := by
  rw [show BitVec.ofNat 32 memcmpAddress = TPM_JG + 0xFFFFF616 + 0xC93C by decide]; exact h.get.ri.mc

theorem tpm_ks (h : PmCode M) : memBytes M TPM_KS 10 = ascii!"signatures" := tuf_codeIn_memBytes h.ks (by decide)
theorem tpm_kt (h : PmCode M) : memBytes M TPM_KT 5 = ascii!"_type" := tuf_codeIn_memBytes h.kt (by decide)
theorem tpm_kk (h : PmCode M) : memBytes M TPM_KK 5 = ascii!"keyid" := tuf_codeIn_memBytes h.kk (by decide)
theorem tpm_kg (h : PmCode M) : memBytes M TPM_KG 3 = ascii!"sig" := tuf_codeIn_memBytes h.kg (by decide)

end

/-- What `parse_metadata` leaves: memory outside the 532 bytes at `s` and
the 16 bytes at `out` as before, and at `out` either the zero word and the
error byte, or the address and length of `signed` and then of
`signatures`. -/
def PmRes (M M' : Word → BitVec 8) (s out : Word) : Except Nat (Word × Nat × Word × Nat) → Prop
  | .error e => (∀ x, Sep x 1 s 532 → Sep x 1 out 16 → M' x = M x) ∧ memLoad32 M' out = 0 ∧
      M' (out + 4) = BitVec.ofNat 8 e
  | .ok (q1, l1, q2, l2) => (∀ x, Sep x 1 s 532 → Sep x 1 out 16 → M' x = M x) ∧ memLoad32 M' out = q1 ∧
      memLoad32 M' (out + 4) = BitVec.ofNat 32 l1 ∧ memLoad32 M' (out + 8) = q2 ∧
      memLoad32 M' (out + 0xC) = BitVec.ofNat 32 l2

/-- The word-level result of `parse_metadata` on the document at `p`. -/
def pmRes (p : Word) (r : Except Nat (Nat × Nat × Nat × Nat)) : Except Nat (Word × Nat × Word × Nat) :=
  r.map fun x => (p + BitVec.ofNat 32 x.1, x.2.1, p + BitVec.ofNat 32 x.2.2.1, x.2.2.2)

/-- The registers `parse_metadata` changes before its epilogue restores the
saved ones. -/
abbrev pmE : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- The saved registers in the frame at `F`. -/
def PmSaved (F : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (F + BitVec.ofNat 32 0x7C) = g0 ra ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x78) = g0 8 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x74) = g0 9 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x70) = g0 18 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x6C) = g0 19 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x68) = g0 20 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x64) = g0 21 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x60) = g0 22 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x5C) = g0 23 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x58) = g0 24 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x54) = g0 25 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x50) = g0 26

/-- Memory after the prologue. -/
def pmM1 (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (F + 0x7C) (g0 ra))
    (F + 0x78) (g0 8))
    (F + 0x74) (g0 9))
    (F + 0x70) (g0 18))
    (F + 0x6C) (g0 19))
    (F + 0x68) (g0 20))
    (F + 0x64) (g0 21))
    (F + 0x60) (g0 22))
    (F + 0x5C) (g0 23))
    (F + 0x58) (g0 24))
    (F + 0x54) (g0 25))
    (F + 0x50) (g0 26)

theorem tpm_pro (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) :
    Out M (pmM1 M F g0) F 128 ∧ PmSaved F g0 (pmM1 M F g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((((((((((out_store32 _ _ _).widen (d := 0x7C) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x78) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x74) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x70) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x6C) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x68) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x64) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x60) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x5C) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x58) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x54) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x50) (by decide))
  · exact pa_ld 0x7C (by decide) [0x78, 0x74, 0x70, 0x6C, 0x68, 0x64, 0x60, 0x5C, 0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 8, g0 9, g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26]
  · exact pa_ld 0x78 (by decide) [0x74, 0x70, 0x6C, 0x68, 0x64, 0x60, 0x5C, 0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 9, g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26]
  · exact pa_ld 0x74 (by decide) [0x70, 0x6C, 0x68, 0x64, 0x60, 0x5C, 0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 18, g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26]
  · exact pa_ld 0x70 (by decide) [0x6C, 0x68, 0x64, 0x60, 0x5C, 0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 19, g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26]
  · exact pa_ld 0x6C (by decide) [0x68, 0x64, 0x60, 0x5C, 0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 20, g0 21, g0 22, g0 23, g0 24, g0 25, g0 26]
  · exact pa_ld 0x68 (by decide) [0x64, 0x60, 0x5C, 0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 21, g0 22, g0 23, g0 24, g0 25, g0 26]
  · exact pa_ld 0x64 (by decide) [0x60, 0x5C, 0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 22, g0 23, g0 24, g0 25, g0 26]
  · exact pa_ld 0x60 (by decide) [0x5C, 0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 23, g0 24, g0 25, g0 26]
  · exact pa_ld 0x5C (by decide) [0x58, 0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 24, g0 25, g0 26]
  · exact pa_ld 0x58 (by decide) [0x54, 0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 25, g0 26]
  · exact pa_ld 0x54 (by decide) [0x50] (by decide) (by decide)
      (memLoad32_store32_same _ _ _) [g0 26]
  · exact memLoad32_store32_same _ _ _

/-- What the function's body may assume after the prologue: the frame at
`F = s + 404`, the saved registers in `M1`, and the bounds on the stack and
`out`. -/
structure PmEnv (M0 M1 : Word → BitVec 8) (s out F : Word) (g0 : Fin 32 → Word) : Prop where
  hF : s + BitVec.ofNat 32 404 = F
  hal : s.toNat % 4 = 0
  hsw : s.toNat + 532 ≤ 0x40000000
  halo : out.toNat % 4 = 0
  how : out.toNat + 16 ≤ 0x40000000
  hso : Sep out 16 s 532
  hro : Sep s 532 (BitVec.ofNat 32 roWindowAddress) roWindowSize
  hc : PmCode M0
  hO1 : Out M0 M1 s 532
  hv : PmSaved F g0 M1
  hsp0 : g0 sp = F + BitVec.ofNat 32 0x80
  hret : g0 ra &&& ~~~1 = g0 ra
  hz0 : g0 0 = 0

section
variable {M0 M1 Mk : Word → BitVec 8} {s out F : Word} {g0 : Fin 32 → Word}

theorem PmEnv.Fc (E : PmEnv M0 M1 s out F g0) (c : Nat) :
    F + BitVec.ofNat 32 c = s + BitVec.ofNat 32 (404 + c) := by
  rw [← E.hF, add_ofNat_assoc]

theorem PmEnv.FN (E : PmEnv M0 M1 s out F g0) {c : Nat} (hc : c ≤ 128) :
    (F + BitVec.ofNat 32 c).toNat = s.toNat + 404 + c := by
  rw [E.Fc, tex_toNat (by have := E.hsw; omega)]; omega

theorem PmEnv.halF (E : PmEnv M0 M1 s out F g0) : F.toNat % 4 = 0 := by
  have := E.FN (c := 0) (by decide); rw [add_ofNat_zero] at this; have := E.hal; omega

/-- A word of the frame at or above the saved registers is apart from the
484 bytes below them. -/
theorem PmEnv.sepHi (E : PmEnv M0 M1 s out F g0) {c : Nat} (hc : 80 ≤ c) (hc' : c + 4 ≤ 128) :
    Sep s 484 (F + BitVec.ofNat 32 c) 4 := by
  rw [E.Fc]; exact tex_sepS (by omega) (by have := E.hsw; omega)

theorem PmEnv.code (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mk s 484) : PmCode Mk :=
  E.hc.of_out (E.hO1.trans (hO.mono (by decide))) E.hsw E.hro

theorem PmEnv.saved (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mk s 484) : PmSaved F g0 Mk := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := E.hv
  exact ⟨(hO.load32 (E.sepHi (by decide) (by decide))).trans v0, (hO.load32 (E.sepHi (by decide) (by decide))).trans v1,
    (hO.load32 (E.sepHi (by decide) (by decide))).trans v2, (hO.load32 (E.sepHi (by decide) (by decide))).trans v3,
    (hO.load32 (E.sepHi (by decide) (by decide))).trans v4, (hO.load32 (E.sepHi (by decide) (by decide))).trans v5,
    (hO.load32 (E.sepHi (by decide) (by decide))).trans v6, (hO.load32 (E.sepHi (by decide) (by decide))).trans v7,
    (hO.load32 (E.sepHi (by decide) (by decide))).trans v8, (hO.load32 (E.sepHi (by decide) (by decide))).trans v9,
    (hO.load32 (E.sepHi (by decide) (by decide))).trans v10, (hO.load32 (E.sepHi (by decide) (by decide))).trans v11⟩

/-- `out` is apart from each saved register. -/
theorem PmEnv.outHi (E : PmEnv M0 M1 s out F g0) {c : Nat} (hc' : c + 4 ≤ 128) :
    Sep out 16 (F + BitVec.ofNat 32 c) 4 := by
  rw [E.Fc]; exact E.hso.subR (by omega)

theorem PmEnv.outT (E : PmEnv M0 M1 s out F g0) : Sep out 16 TPM tufParseMetadataCode.length :=
  lowSep E.how (by decide) (by decide)

theorem PmEnv.savedOut {Mf Mf' : Word → BitVec 8} (E : PmEnv M0 M1 s out F g0) (hv : PmSaved F g0 Mf)
    (hO : Out Mf Mf' out 16) : PmSaved F g0 Mf' := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11⟩ := hv
  exact ⟨(hO.load32 (E.outHi (by decide))).trans v0, (hO.load32 (E.outHi (by decide))).trans v1,
    (hO.load32 (E.outHi (by decide))).trans v2, (hO.load32 (E.outHi (by decide))).trans v3,
    (hO.load32 (E.outHi (by decide))).trans v4, (hO.load32 (E.outHi (by decide))).trans v5,
    (hO.load32 (E.outHi (by decide))).trans v6, (hO.load32 (E.outHi (by decide))).trans v7,
    (hO.load32 (E.outHi (by decide))).trans v8, (hO.load32 (E.outHi (by decide))).trans v9,
    (hO.load32 (E.outHi (by decide))).trans v10, (hO.load32 (E.outHi (by decide))).trans v11⟩

/-- Memory that agrees with `M1` outside the 484 bytes at `s` agrees with
`M0` outside the 532. -/
theorem PmEnv.agree (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mk s 484) : ∀ x, Sep x 1 s 532 → Mk x = M0 x :=
  fun x hx => (hO x (by have := hx.subR (c := 0) (l := 484) (by decide); rwa [add_ofNat_zero] at this)).trans
    (E.hO1 x hx)

end

section
variable {M0 M1 Mf : Word → BitVec 8} {s out F : Word} {g g0 : Fin 32 → Word}

theorem pm_epi {R : (Word → BitVec 8) → Prop} (hsp : g sp = F) (hv : PmSaved F g0 Mf)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x80) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ pmE → g x = g0 x) (hR : R Mf) :
    WP tufParseMetadataCode TPM (RPost (g0 ra) R g0) Mf 0x27A g := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hv
  refine WP.lw pm_at_27a (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x7C) (by decide)) ?_; wn
  refine WP.lw pm_at_27c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x78) (by decide)) ?_; wn
  refine WP.lw pm_at_27e (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x74) (by decide)) ?_; wn
  refine WP.lw pm_at_280 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x70) (by decide)) ?_; wn
  refine WP.lw pm_at_282 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x6C) (by decide)) ?_; wn
  refine WP.lw pm_at_284 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x68) (by decide)) ?_; wn
  refine WP.lw pm_at_286 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x64) (by decide)) ?_; wn
  refine WP.lw pm_at_288 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x60) (by decide)) ?_; wn
  refine WP.lw pm_at_28a (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x5C) (by decide)) ?_; wn
  refine WP.lw pm_at_28c (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x58) (by decide)) ?_; wn
  refine WP.lw pm_at_28e (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x54) (by decide)) ?_; wn
  refine WP.lw pm_at_290 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x50) (by decide)) ?_; wn
  refine WP.aluImm pm_at_292 ?_; wn
  refine WP.ret pm_at_294 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp]; erw [e0]; rw [add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp <;>
    rw [hsp]
  · exact e0
  · rw [hsp0]; rfl
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6
  · exact e7
  · exact e8
  · exact e9
  · exact e10
  · exact e11

end

/-- The postcondition of the walk: return to the caller with `r` at `out`. -/
abbrev pmQ (M0 : Word → BitVec 8) (s out : Word) (g0 : Fin 32 → Word) (r : Except Nat (Word × Nat × Word × Nat)) :
    Post :=
  RPost (g0 ra) (fun M' => PmRes M0 M' s out r) g0

theorem pm_st4 (M : Word → BitVec 8) (o a b c d : Word) :
    Out M (memStore32 (memStore32 (memStore32 (memStore32 M o a) (o + 4) b) (o + 8) c) (o + 0xC) d) o 16 ∧
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M o a) (o + 4) b) (o + 8) c) (o + 0xC) d) o = a ∧
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M o a) (o + 4) b) (o + 8) c) (o + 0xC) d)
      (o + 4) = b ∧
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M o a) (o + 4) b) (o + 8) c) (o + 0xC) d)
      (o + 8) = c ∧
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M o a) (o + 4) b) (o + 8) c) (o + 0xC) d)
      (o + 0xC) = d := by
  refine ⟨(((out_store32 _ _ _).mono (by decide)).trans (Out.widen (d := 4) (out_store32 _ _ _) (by decide))).trans
      (Out.widen (d := 8) (out_store32 _ _ _) (by decide)) |>.trans (Out.widen (d := 0xC) (out_store32 _ _ _)
      (by decide)), ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩
  · have := ld_skip (s := o) (v := d) 0 0xC (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip (v := c) 0 8 (Or.inl (by decide)) (by decide) (by decide)
        (ld_skip (v := b) 0 4 (Or.inl (by decide)) (by decide) (by decide)
          (show memLoad32 (memStore32 M o a) (o + BitVec.ofNat 32 0) = a by
            rw [add_ofNat_zero]; exact memLoad32_store32_same _ _ _)))
    rwa [add_ofNat_zero] at this
  · exact ld_skip 4 0xC (Or.inl (by decide)) (by decide) (by decide)
      (ld_skip 4 8 (Or.inl (by decide)) (by decide) (by decide) (memLoad32_store32_same _ _ _))
  · exact ld_skip 8 0xC (Or.inl (by decide)) (by decide) (by decide) (memLoad32_store32_same _ _ _)

section
variable {M0 M1 Mf : Word → BitVec 8} {s out F : Word} {g g0 : Fin 32 → Word} {e : Nat}

/-- The error tail at 0x268: the zero word at `out`, the error byte from
`a0` at `out + 4`, and the epilogue. -/
theorem pm_268 (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    (ha0 : (g a0).extractLsb' 0 8 = BitVec.ofNat 8 e) (hz : g 0 = 0) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.error e)) Mf 0x268 g := by
  refine WP.sw pm_at_268 (by (try rsimp); rw [h26, add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [h26, add_lit_zero]; exact tex_sepL E.outT (by decide)) ?_; wn
  refine WP.sb pm_at_26c (by (try rsimp); rw [h26]; exact E.outT.sub (c := 4) (l := 1) (by decide)) ?_; wn
  refine WP.jal pm_at_270 (by decide) ?_; wn
  (try rsimp)
  rw [h26, add_lit_zero, hz, ha0]
  have hR := pa_err_res Mf out _ e rfl
  exact pm_epi hsp (E.savedOut (E.saved hO) (hR.out.mono (by decide))) E.hsp0 E.hret E.halF E.hz0 hfr
    ⟨fun x hx ho => (hR.1 x (ho.subR (c := 0) (l := 8) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)).trans
      (E.agree hO x hx), hR.2.1, hR.2.2⟩

/-- The error tail at 0x272, with the error byte in `s1`. -/
theorem pm_272 (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    (h9 : (g 9).extractLsb' 0 8 = BitVec.ofNat 8 e) (hz : g 0 = 0) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.error e)) Mf 0x272 g := by
  refine WP.sw pm_at_272 (by (try rsimp); rw [h26, add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [h26, add_lit_zero]; exact tex_sepL E.outT (by decide)) ?_; wn
  refine WP.sb pm_at_276 (by (try rsimp); rw [h26]; exact E.outT.sub (c := 4) (l := 1) (by decide)) ?_; wn
  (try rsimp)
  rw [h26, add_lit_zero, hz, h9]
  have hR := pa_err_res Mf out _ e rfl
  exact pm_epi hsp (E.savedOut (E.saved hO) (hR.out.mono (by decide))) E.hsp0 E.hret E.halF E.hz0 hfr
    ⟨fun x hx ho => (hR.1 x (ho.subR (c := 0) (l := 8) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)).trans
      (E.agree hO x hx), hR.2.1, hR.2.2⟩

/-- The error tail at 0x264, with the error byte at `F + 0x20`. -/
theorem pm_264 (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    (hb : Mf (F + 0x20) = BitVec.ofNat 8 e) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.error e)) Mf 0x264 g := by
  refine WP.lbu pm_at_264 ?_; wn
  exact pm_268 E hO (by (try rsimp); exact h26) (by (try rsimp); exact hsp) (by (try rsimp); rw [hsp, hb, ri_ze]) (by rsimp)
    (by keepz E.hz0)

/-- The error tail at 0x8E, with the error byte at `F + 0x1D`. -/
theorem pm_8e (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    (hb : Mf (F + 0x1D) = BitVec.ofNat 8 e) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.error e)) Mf 0x8E g := by
  refine WP.lbu pm_at_8e ?_; wn
  refine WP.jal pm_at_92 (by decide) ?_; wn
  exact pm_268 E hO (by (try rsimp); exact h26) (by (try rsimp); exact hsp) (by (try rsimp); rw [hsp, hb, ri_ze]) (by rsimp)
    (by keepz E.hz0)

/-- The error tail at 0x296, with the error byte at `F + 0x40`. -/
theorem pm_296 (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    (hb : Mf (F + 0x40) = BitVec.ofNat 8 e) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.error e)) Mf 0x296 g := by
  refine WP.lbu pm_at_296 ?_; wn
  refine WP.jal pm_at_29a (by decide) ?_; wn
  exact pm_268 E hO (by (try rsimp); exact h26) (by (try rsimp); exact hsp) (by (try rsimp); rw [hsp, hb, ri_ze]) (by rsimp)
    (by keepz E.hz0)

/-- The error tail at 0x29C, with the error byte at `F + 0x4C`. -/
theorem pm_29c (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    (hb : Mf (F + 0x4C) = BitVec.ofNat 8 e) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.error e)) Mf 0x29C g := by
  refine WP.lbu pm_at_29c ?_; wn
  refine WP.jal pm_at_2a0 (by decide) ?_; wn
  exact pm_268 E hO (by (try rsimp); exact h26) (by (try rsimp); exact hsp) (by (try rsimp); rw [hsp, hb, ri_ze]) (by rsimp)
    (by keepz E.hz0)

/-- The error tail at 0x116, for metadata of the wrong shape. -/
theorem pm_116 (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    (hz : g 0 = 0) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.error 0x21)) Mf 0x116 g := by
  refine WP.aluImm pm_at_116 ?_; wn
  refine WP.jal pm_at_11a (by decide) ?_; wn
  exact pm_268 E hO (by (try rsimp); exact h26) (by (try rsimp); exact hsp) (by (try rsimp); rw [hz]; decide) (by (try rsimp); (try exact hz))
    (by keepz E.hz0)

/-- The success tail at 0x2A2: `signed` and then `signatures` at `out`, and
the epilogue. -/
theorem pm_ok (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    {l1 l2 : Nat} (h20 : g 20 = BitVec.ofNat 32 l1) (h18 : g 18 = BitVec.ofNat 32 l2) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.ok (g 19, l1, g 21, l2))) Mf 0x2A2 g := by
  have hoT := E.outT
  refine WP.sw pm_at_2a2 (by (try rsimp); rw [h26, add_lit_zero]; exact E.halo)
    (by (try rsimp); rw [h26, add_lit_zero]; exact tex_sepL hoT (by decide)) ?_; wn
  refine WP.sw pm_at_2a6 (by (try rsimp); rw [h26]; exact aligned_add E.halo (k := 4) (by decide))
    (by (try rsimp); rw [h26]; exact hoT.sub (c := 4) (l := 4) (by decide)) ?_; wn
  refine WP.sw pm_at_2aa (by (try rsimp); rw [h26]; exact aligned_add E.halo (k := 8) (by decide))
    (by (try rsimp); rw [h26]; exact hoT.sub (c := 8) (l := 4) (by decide)) ?_; wn
  refine WP.sw pm_at_2ae (by (try rsimp); rw [h26]; exact aligned_add E.halo (k := 0xC) (by decide))
    (by (try rsimp); rw [h26]; exact hoT.sub (c := 0xC) (l := 4) (by decide)) ?_; wn
  refine WP.jal pm_at_2b2 (by decide) ?_; wn
  (try rsimp)
  rw [h26, add_lit_zero, h20, h18]
  obtain ⟨hOs, r0, r1, r2, r3⟩ := pm_st4 Mf out (g 19) (BitVec.ofNat 32 l1) (g 21) (BitVec.ofNat 32 l2)
  exact pm_epi hsp (E.savedOut (E.saved hO) hOs) E.hsp0 E.hret E.halF E.hz0 hfr
    ⟨fun x hx ho => (hOs x ho).trans (E.agree hO x hx), r0, r1, r2, r3⟩

end

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `memcmp` on `n` bytes at `p` and `q`: `a0` is zero exactly
when the bytes agree, and memory is unchanged. -/
theorem WP.callMemcmpIff {hi lo tb p q : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb memcmpCode) (h0 : f a0 = p) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 n)
    (hn : n < 2 ^ 32)
    (k : ∀ m2 : Machine, (reg m2 a0 = 0 ↔ memBytes M p n = memBytes M q n) → m2.mem = M →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => (reg m2 a0 = 0 ↔ memBytes M p n = memBytes M q n) ∧ m2.mem = M)
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by rw [hP.2]; exact hc) (fun m2 hP => k m2 hP.1 hP.2)
  obtain ⟨m2, c2, pc2, hz, hfr, hmem⟩ := memcmp_correct m1 (base := tb) (p := p) (q := q) (n := n)
    (by rw [hmem1]; exact hct) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) hn (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev))
  refine ⟨m2, c2, pc2, ⟨?_, hmem.trans hmem1⟩, fun x hx => ?_⟩
  · rw [memBytes_eq_iff, ← hmem1]; exact hz
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact hfr x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1

end


section
variable {M0 M1 Mk : Word → BitVec 8} {s out F : Word} {g0 : Fin 32 → Word}

theorem PmEnv.lowS (E : PmEnv M0 M1 s out F g0) {c w : Nat} (h : c + w ≤ 532) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (s + BitVec.ofNat 32 c) w b l :=
  lowSep (by have := E.hsw; rw [tex_toNat (by omega)]; omega) hb hbl

theorem PmEnv.lowF (E : PmEnv M0 M1 s out F g0) {c w : Nat} (h : c + w ≤ 128) {b : Word} {l : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hbl : b.toNat + l ≤ 2 ^ 32) : Sep (F + BitVec.ofNat 32 c) w b l := by
  rw [E.Fc]; exact E.lowS (by omega) hb hbl

theorem pm_ss (s : Word) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 532)
    (hd : d + k ≤ 532) : Sep (s + BitVec.ofNat 32 c) n (s + BitVec.ofNat 32 d) k :=
  sep_offsets s h (by omega) (by omega)

theorem PmEnv.fs (E : PmEnv M0 M1 s out F g0) {c n d k : Nat} (h : 404 + c + n ≤ d ∨ d + k ≤ 404 + c)
    (hc : c + n ≤ 128) (hd : d + k ≤ 532) : Sep (F + BitVec.ofNat 32 c) n (s + BitVec.ofNat 32 d) k := by
  rw [E.Fc]; exact pm_ss s h (by omega) hd

theorem pm_ff (F : Word) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 128) (hd : d + k ≤ 128) :
    Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 d) k :=
  sep_offsets F h (by omega) (by omega)

/-- Bytes apart from the stack read the same in memory after the prologue
as in the caller's. -/
theorem PmEnv.bytes (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mk s 484) {q : Word} {l : Nat}
    (hS : Sep s 532 q l) : memBytes Mk q l = memBytes M0 q l :=
  memBytes_congr fun _ hi => E.agree hO _ (sep_pt hS hi)

theorem PmEnv.sp (E : PmEnv M0 M1 s out F g0) (d : Nat) (hd : d ≤ 404) :
    s + BitVec.ofNat 32 d + BitVec.ofNat 32 (404 - d) = F := by
  rw [add_ofNat_assoc, ← E.hF]; congr 2; omega

theorem PmEnv.alS (E : PmEnv M0 M1 s out F g0) {d : Nat} (hd : d % 4 = 0) : (s + BitVec.ofNat 32 d).toNat % 4 = 0 :=
  aligned_add E.hal hd

theorem PmEnv.wS (E : PmEnv M0 M1 s out F g0) {d k : Nat} (hd : d + k ≤ 532) :
    (s + BitVec.ofNat 32 d).toNat + k ≤ 0x40000000 := by
  have := E.hsw; rw [tex_toNat (by omega)]; omega

end

/-- The registers that hold the loops' fixed values: `sp`, `out` in `s10`,
the key addresses in `s7` and `s6`, and the two values in `s3`, `s4`, `s5`,
and `s2`. -/
abbrev pmKL : List (Fin 32) := [sp, 26, 23, 22, 19, 20, 21, 18]

theorem pmKeepUpd {f G : Fin 32 → Word} {rd : Fin 32} {v : Word} (hrd : rd ∉ pmKL)
    (h : ∀ x, x ∈ pmKL → f x = G x) : ∀ x, x ∈ pmKL → upd f rd v x = G x := by
  intro x hx
  have hne : x ≠ rd := fun e => hrd (e ▸ hx)
  have hx0 : x.val ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [upd_app, hx0, hne, ↓reduceIte]; exact h x hx

theorem pmKeepClob {f G : Fin 32 → Word} {m : Machine} {cl : List (Fin 32)} (hcl : ∀ x, x ∈ cl → x ∉ pmKL)
    (h : ∀ x, x ∈ pmKL → f x = G x) : ∀ x, x ∈ pmKL → clob f m cl x = G x := by
  intro x hx
  have hn : x ∉ cl := fun h' => hcl x h' hx
  simp only [clob_app, hn, ↓reduceIte]; exact h x hx

/-- Proves `∀ x, x ∈ pmKL → g x = G x` for `g` a chain of `upd`s and
`clob`s over a register file that the hypothesis says it of. -/
syntax "pmkeep" term : tactic

macro_rules
  | `(tactic| pmkeep $h) =>
    `(tactic| ((repeat (first | refine pmKeepUpd (by decide) ?_ | refine pmKeepClob (by decide) ?_)); exact $h))


/-- The two array cursors in the frame: the outer one at `F + 0x30`, which
the inner loop keeps, and the inner one at `F + 0x3C`. -/
def PmCur (Mk : Word → BitVec 8) (F C0 C1 C2 P : Word) (N pos : Nat) : Prop :=
  memLoad32 Mk (F + 0x30) = C0 ∧ memLoad32 Mk (F + 0x34) = C1 ∧ memLoad32 Mk (F + 0x38) = C2 ∧
    memLoad32 Mk (F + 0x3C) = P ∧ memLoad32 Mk (F + 0x40) = BitVec.ofNat 32 N ∧
    memLoad32 Mk (F + 0x44) = BitVec.ofNat 32 pos

theorem pm_ld_sub {Mk Mk' : Word → BitVec 8} {r F : Word} {l : Nat} (hO : Out Mk Mk' r l)
    (hs : Sep r l (F + BitVec.ofNat 32 0x30) 24) {i : Nat} (hi : i + 4 ≤ 24) :
    memLoad32 Mk' (F + BitVec.ofNat 32 (0x30 + i)) = memLoad32 Mk (F + BitVec.ofNat 32 (0x30 + i)) := by
  have := hs.subR (c := i) (l := 4) hi
  rw [add_ofNat_assoc] at this
  exact hO.load32 this

theorem PmCur.out {Mk Mk' : Word → BitVec 8} {F C0 C1 C2 P r : Word} {N pos l : Nat}
    (h : PmCur Mk F C0 C1 C2 P N pos) (hO : Out Mk Mk' r l) (hs : Sep r l (F + BitVec.ofNat 32 0x30) 24) :
    PmCur Mk' F C0 C1 C2 P N pos :=
  ⟨(pm_ld_sub hO hs (i := 0) (by decide)).trans h.1, (pm_ld_sub hO hs (i := 4) (by decide)).trans h.2.1,
    (pm_ld_sub hO hs (i := 8) (by decide)).trans h.2.2.1, (pm_ld_sub hO hs (i := 12) (by decide)).trans h.2.2.2.1,
    (pm_ld_sub hO hs (i := 16) (by decide)).trans h.2.2.2.2.1,
    (pm_ld_sub hO hs (i := 20) (by decide)).trans h.2.2.2.2.2⟩

theorem pm_ld2 {M M' : Word → BitVec 8} {A B a : Word} (hfa : ∀ x, Sep x 1 A 12 → Sep x 1 B 4 → M' x = M x)
    (h1 : Sep A 12 a 4) (h2 : Sep B 4 a 4) : memLoad32 M' a = memLoad32 M a :=
  memLoad32_congr fun _ hj => hfa _ (sep_pt h1 hj) (sep_pt h2 hj)

/-- The cursors after `next_element` moved the inner one to `nx`. -/
theorem pm_cur_elem {Ma M2 : Word → BitVec 8} {F C0 C1 C2 P : Word} {N pos nx : Nat}
    (hC : PmCur Ma F C0 C1 C2 P N pos)
    (hfa : ∀ x, Sep x 1 (F + 0x1C) 12 → Sep x 1 (F + 0x3C + 8) 4 → M2 x = Ma x)
    (t4 : memLoad32 M2 (F + 0x3C + 8) = BitVec.ofNat 32 nx) : PmCur M2 F C0 C1 C2 P N nx := by
  have e : F + 0x3C + 8 = F + BitVec.ofNat 32 0x44 := by rw [BitVec.add_assoc]; rfl
  rw [e] at hfa t4
  have h1 : ∀ {d : Nat}, 0x28 ≤ d → d + 4 ≤ 0x44 → Sep (F + 0x1C) 12 (F + BitVec.ofNat 32 d) 4 := fun h h' =>
    pm_ff F (c := 0x1C) (n := 12) (Or.inl (by omega)) (by decide) (by omega)
  have h2 : ∀ {d : Nat}, d + 4 ≤ 0x44 → Sep (F + BitVec.ofNat 32 0x44) 4 (F + BitVec.ofNat 32 d) 4 := fun h =>
    pm_ff F (c := 0x44) (n := 4) (Or.inr (by omega)) (by decide) (by omega)
  exact ⟨(pm_ld2 hfa (h1 (d := 0x30) (by decide) (by decide)) (h2 (by decide))).trans hC.1,
    (pm_ld2 hfa (h1 (d := 0x34) (by decide) (by decide)) (h2 (by decide))).trans hC.2.1,
    (pm_ld2 hfa (h1 (d := 0x38) (by decide) (by decide)) (h2 (by decide))).trans hC.2.2.1,
    (pm_ld2 hfa (h1 (d := 0x3C) (by decide) (by decide)) (h2 (by decide))).trans hC.2.2.2.1,
    (pm_ld2 hfa (h1 (d := 0x40) (by decide) (by decide)) (h2 (by decide))).trans hC.2.2.2.2.1, t4⟩

section
variable {M0 M1 Mk Ma M2 : Word → BitVec 8} {s out F : Word} {g0 : Fin 32 → Word}

/-- What `next_element` with its result at `F + 0x1C` and its cursor at
`F + d` changes lies in the 484 bytes at `s`. -/
theorem pm_elemOut (E : PmEnv M0 M1 s out F g0) {d : Nat} (hd : 0x28 ≤ d) (hd' : d + 12 ≤ 80)
    {r : Option (Option (Word × Nat × Nat))}
    (h : ElemRes Ma M2 (F + 0x1C) (F + BitVec.ofNat 32 d) r) : Out Ma M2 s 484 := by
  intro x hx
  refine h.out ?_ ?_
  · show Sep x 1 (F + BitVec.ofNat 32 0x1C) 12
    rw [E.Fc]; exact sep_in hx (by decide)
  · show Sep x 1 (F + BitVec.ofNat 32 d + BitVec.ofNat 32 8) 4
    rw [add_ofNat_assoc, E.Fc]; exact sep_in hx (by omega)

end


/-- The outer array cursor at `F + 0x30`. -/
def PmOc (Mk : Word → BitVec 8) (F P : Word) (N pos : Nat) : Prop :=
  memLoad32 Mk (F + 0x30) = P ∧ memLoad32 Mk (F + 0x34) = BitVec.ofNat 32 N ∧
    memLoad32 Mk (F + 0x38) = BitVec.ofNat 32 pos

theorem PmOc.out {Mk Mk' : Word → BitVec 8} {F P r : Word} {N pos l : Nat} (h : PmOc Mk F P N pos)
    (hO : Out Mk Mk' r l) (hs : Sep r l (F + BitVec.ofNat 32 0x30) 12) : PmOc Mk' F P N pos := by
  have e : ∀ {i : Nat}, i + 4 ≤ 12 →
      memLoad32 Mk' (F + BitVec.ofNat 32 (0x30 + i)) = memLoad32 Mk (F + BitVec.ofNat 32 (0x30 + i)) := by
    intro i hi
    have := hs.subR (c := i) (l := 4) hi
    rw [add_ofNat_assoc] at this
    exact hO.load32 this
  exact ⟨(e (i := 0) (by decide)).trans h.1, (e (i := 4) (by decide)).trans h.2.1, (e (i := 8) (by decide)).trans h.2.2⟩

/-- The outer cursor after `next_element` moved it to `nx`. -/
theorem pm_oc_elem {Ma M2 : Word → BitVec 8} {F P : Word} {N pos nx : Nat} (hC : PmOc Ma F P N pos)
    (hfa : ∀ x, Sep x 1 (F + 0x1C) 12 → Sep x 1 (F + 0x30 + 8) 4 → M2 x = Ma x)
    (t4 : memLoad32 M2 (F + 0x30 + 8) = BitVec.ofNat 32 nx) : PmOc M2 F P N nx := by
  have e : F + 0x30 + 8 = F + BitVec.ofNat 32 0x38 := by rw [BitVec.add_assoc]; rfl
  rw [e] at hfa t4
  have h1 : ∀ {d : Nat}, 0x28 ≤ d → d + 4 ≤ 0x38 → Sep (F + 0x1C) 12 (F + BitVec.ofNat 32 d) 4 := fun h h' =>
    pm_ff F (c := 0x1C) (n := 12) (Or.inl (by omega)) (by decide) (by omega)
  have h2 : ∀ {d : Nat}, d + 4 ≤ 0x38 → Sep (F + BitVec.ofNat 32 0x38) 4 (F + BitVec.ofNat 32 d) 4 := fun h =>
    pm_ff F (c := 0x38) (n := 4) (Or.inr (by omega)) (by decide) (by omega)
  exact ⟨(pm_ld2 hfa (h1 (d := 0x30) (by decide) (by decide)) (h2 (by decide))).trans hC.1,
    (pm_ld2 hfa (h1 (d := 0x34) (by decide) (by decide)) (h2 (by decide))).trans hC.2.1, t4⟩

/-- The copy of the outer cursor into the inner one at 0x208. -/
theorem pm_copy {M : Word → BitVec 8} {F P : Word} {N pos : Nat} (h : PmOc M F P N pos) :
    PmCur (memStore32 (memStore32 (memStore32 M (F + 0x3C) P) (F + 0x40) (BitVec.ofNat 32 N)) (F + 0x44)
      (BitVec.ofNat 32 pos)) F P (BitVec.ofNat 32 N) (BitVec.ofNat 32 pos) P N pos ∧
    Out M (memStore32 (memStore32 (memStore32 M (F + 0x3C) P) (F + 0x40) (BitVec.ofNat 32 N)) (F + 0x44)
      (BitVec.ofNat 32 pos)) (F + 0x3C) 12 := by
  have sp : ∀ {c d : Nat}, c + 4 ≤ d ∨ d + 4 ≤ c → c + 4 ≤ 128 → d + 4 ≤ 128 →
      Sep (F + BitVec.ofNat 32 c) 4 (F + BitVec.ofNat 32 d) 4 := fun h h1 h2 => pm_ff F h h1 h2
  have k : ∀ {d : Nat}, d + 4 ≤ 0x3C → ∀ {v : Word}, memLoad32 M (F + BitVec.ofNat 32 d) = v →
      memLoad32 (memStore32 (memStore32 (memStore32 M (F + 0x3C) P) (F + 0x40) (BitVec.ofNat 32 N)) (F + 0x44)
        (BitVec.ofNat 32 pos)) (F + BitVec.ofNat 32 d) = v := fun hd _ hv =>
    ((memLoad32_store32_sep (sp (c := 0x44) (Or.inr (by omega)) (by decide) (by omega))).trans
      ((memLoad32_store32_sep (sp (c := 0x40) (Or.inr (by omega)) (by decide) (by omega))).trans
        ((memLoad32_store32_sep (sp (c := 0x3C) (Or.inr (by omega)) (by decide) (by omega))).trans hv)))
  refine ⟨⟨k (d := 0x30) (by decide) h.1, k (d := 0x34) (by decide) h.2.1, k (d := 0x38) (by decide) h.2.2,
    ?_, ?_, memLoad32_store32_same _ _ _⟩, ?_⟩
  · exact (memLoad32_store32_sep (sp (c := 0x44) (d := 0x3C) (Or.inr (by decide)) (by decide) (by decide))).trans
      ((memLoad32_store32_sep (sp (c := 0x40) (d := 0x3C) (Or.inr (by decide)) (by decide) (by decide))).trans
        (memLoad32_store32_same _ _ _))
  · exact (memLoad32_store32_sep (sp (c := 0x44) (d := 0x40) (Or.inr (by decide)) (by decide) (by decide))).trans
      (memLoad32_store32_same _ _ _)
  · have o0 : Out M (memStore32 M (F + 0x3C) P) (F + 0x3C) 12 :=
      Out.widen (d := 0) (by rw [add_ofNat_zero]; exact out_store32 _ _ _) (by decide)
    have o1 : Out (memStore32 M (F + 0x3C) P) (memStore32 (memStore32 M (F + 0x3C) P) (F + 0x40) (BitVec.ofNat 32 N))
        (F + 0x3C) 12 :=
      Out.widen (d := 4) (by rw [show F + 0x3C + BitVec.ofNat 32 4 = F + 0x40 by rw [BitVec.add_assoc]; rfl]
                             exact out_store32 _ _ _) (by decide)
    have o2 : Out (memStore32 (memStore32 M (F + 0x3C) P) (F + 0x40) (BitVec.ofNat 32 N))
        (memStore32 (memStore32 (memStore32 M (F + 0x3C) P) (F + 0x40) (BitVec.ofNat 32 N)) (F + 0x44)
          (BitVec.ofNat 32 pos)) (F + 0x3C) 12 :=
      Out.widen (d := 8) (by rw [show F + 0x3C + BitVec.ofNat 32 8 = F + 0x44 by rw [BitVec.add_assoc]; rfl]
                             exact out_store32 _ _ _) (by decide)
    exact (o0.trans o1).trans o2

/-- `pmThen` chains to the right. -/
theorem pmThen_assoc {α : Type} (r k : Except Nat Unit) (R : Except Nat α) :
    pmThen (pmThen r k) R = pmThen r (pmThen k R) := by
  rcases r with _ | ⟨⟩ <;> rfl

section
variable {M0 M1 : Word → BitVec 8} {s out F : Word} {g0 : Fin 32 → Word}

set_option maxHeartbeats 4000000 in
/-- The inner loop at 0x216: the elements of the signatures array after the
current one, from the inner cursor at `F + 0x3C`, have key IDs other than
`kid`, the `KL` bytes at `KQ` that `s1` and `s8` hold. It ends at 0x19C,
the outer loop, with the outer cursor at `F + 0x30` as before. -/
theorem pm_inner (E : PmEnv M0 M1 s out F g0) {gK : Fin 32 → Word} (hKsp : gK sp = F) (hK26 : gK 26 = out)
    (hK23 : gK 23 = TPM_KK) {P KQ C0 C1 C2 : Word} {N KL : Nat} {R : Except Nat (Word × Nat × Word × Nat)}
    (hP0 : P.toNat ≠ 0) (hPN : P.toNat + N < 2 ^ 32) (hSP : Sep s 532 P N) (hSK : Sep s 532 KQ KL)
    (hKL : KL < 2 ^ 32)
    (hcont : ∀ (Mk : Word → BitVec 8) (g : Fin 32 → Word), Out M1 Mk s 484 →
      memLoad32 Mk (F + BitVec.ofNat 32 0x30) = C0 → memLoad32 Mk (F + BitVec.ofNat 32 0x34) = C1 →
      memLoad32 Mk (F + BitVec.ofNat 32 0x38) = C2 → (∀ x, x ∈ pmKL → g x = gK x) → g 0 = 0 →
      (∀ x, x ∉ pmE → g x = g0 x) → WP tufParseMetadataCode TPM (pmQ M0 s out g0 R) Mk 0x19C g) :
    ∀ (k pos : Nat) (Mk : Word → BitVec 8) (g : Fin 32 → Word), Out M1 Mk s 484 →
      PmCur Mk F C0 C1 C2 P N pos → pos ≤ N → N < pos + k → (∀ x, x ∈ pmKL → g x = gK x) → g 9 = KQ →
      g 24 = BitVec.ofNat 32 KL → g 0 = 0 → (∀ x, x ∉ pmE → g x = g0 x) →
      WP tufParseMetadataCode TPM
        (pmQ M0 s out g0 (pmThen (pmLater (memBytes M0 P N) (memBytes M0 KQ KL) k pos) R)) Mk 0x216 g := by
  intro k
  induction k with
  | zero => intro pos _ _ _ _ h1 h2; exfalso; omega
  | succ k ih =>
  intro pos Mk g hO hC hpos hk hK h9 h24 hz hfr
  have hgsp : g sp = F := (hK sp (by decide)).trans hKsp
  have hg26 : g 26 = out := (hK 26 (by decide)).trans hK26
  have hg23 : g 23 = TPM_KK := (hK 23 (by decide)).trans hK23
  have hc := E.code hO
  have hPS := tpm_parseSep E.hsw E.hro
  refine WP.aluImm pm_at_216 ?_; wn
  refine WP.aluImm pm_at_218 ?_; wn
  refine WP.callNextElement (tb := TPM_JNE) (out := F + 0x1C) (c := F + 0x3C)
    (s := s + BitVec.ofNat 32 256) (p := P) (n := N) (pos := pos) pm_at_21a pm_at_21e (by decide) (by decide)
    (by decide) hc.ne hc.ri (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [ev_add, hgsp])
    (by (try rsimp); rw [hgsp]; exact (E.sp 256 (by decide)).symm) (E.alS (by decide))
    (aligned_add E.halF (by decide)) (aligned_add E.halF (by decide)) hC.2.2.2.1
    (by rw [BitVec.add_assoc]; exact hC.2.2.2.2.1) (by rw [BitVec.add_assoc]; exact hC.2.2.2.2.2)
    (by omega) (by omega) hP0 (by omega)
    (by rw [show TPM_JNE + 0xFFFFF7E0 = TPM_JG + 0xFFFFF616 by decide]; exact hPS.2.ri.sub (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (hSP.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
    (pm_ff F (Or.inl (by decide)) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes hO hSP] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hER⟩ := hR
  have hOE := pm_elemOut E (d := 0x3C) (by decide) (by decide) hER
  have hO2 : Out M1 M2 s 484 := hO.trans ((Out.upK rfl hOa (by decide)).trans hOE)
  have hCa := hC.out hOa (E.fs (c := 0x30) (n := 24) (d := 256) (k := 148) (Or.inr (by decide)) (by decide) (by decide)).symm
  refine WP.zero fun hz2 => ?_
  refine WP.lbu pm_at_222 ?_; wn
  simp only [pmLater]
  rcases hne : nextElement (memBytes M0 P N) pos with _ | _ | ⟨ep, el, nx⟩ <;> rw [hne] at hER <;>
    simp only [elemRes, Option.map_none, Option.map_some] at hER
  · -- An error inside the array.
    obtain ⟨-, t1, t2⟩ := hER
    refine WP.branch pm_at_226 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    exact pm_8e E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
      (by rw [show F + 0x1D = F + 0x1C + 1 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
  · -- The end of the array: back to the outer loop.
    obtain ⟨hfa, t1, t2⟩ := hER
    refine WP.branch pm_at_226 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_22a (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    refine WP.branch pm_at_22c (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb)
      rw [hgsp, show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl, t2] at eb; exact absurd eb (by decide)
    have hCb := hCa.out (r := F + 0x1C) (l := 12) (fun x hx => hfa x hx) (pm_ff F (Or.inl (by decide)) (by decide) (by decide))
    exact hcont _ _ hO2 hCb.1 hCb.2.1 hCb.2.2.1 (by pmkeep hK) (by rsimp) (by keepz E.hz0)
  · -- An element at `ep`.
    obtain ⟨hfa, t1, t2, t3, t4⟩ := hER
    obtain ⟨rfl, hpx, hel, hle, hxN⟩ := nextElement_lt hne
    rw [memBytes_length] at hle hxN
    refine WP.branch pm_at_226 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_22a (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    have t2' : memLoad32 M2 (F + 0x20) = P + BitVec.ofNat 32 ep := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    have t3' : memLoad32 M2 (F + 0x24) = BitVec.ofNat 32 el := by
      rw [show F + 0x24 = F + 0x1C + 8 by rw [BitVec.add_assoc]; rfl]; exact t3
    have hq0 := nx_q0 hP0 (n := N) (pos := ep) (by omega) (by omega)
    refine WP.branch pm_at_22c (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t2', hq0] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_22e (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x24) (by decide)) ?_; wn
    refine WP.aluImm pm_at_230 ?_; wn
    refine WP.aluImm pm_at_232 ?_; wn
    refine WP.alu pm_at_234 ?_; wn
    have hc2 := E.code hO2
    have hSe : Sep s 532 (P + BitVec.ofNat 32 ep) el := hSP.subR hle
    refine WP.callField (tb := TPM_JF) (out := F + 0x1C) (s := s + BitVec.ofNat 32 144)
      (p := P + BitVec.ofNat 32 ep) (kq := TPM_KK) (n := el) (kl := 5)
      pm_at_236 pm_at_23a (by decide) (by decide) (by decide) hc2.fieldC
      (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [hgsp, t2']) (by (try rsimp); rw [hgsp, t3'])
      (by (try rsimp); (try simp only [ev0]); exact hg23) (by (try rsimp); (try simp only [ev0]); (try rfl))
      (by (try rsimp); rw [hgsp]; exact (E.sp 144 (by decide)).symm)
      (E.alS (by decide)) (aligned_add E.halF (by decide)) (by have := E.wS (d := 144) (k := 260) (by decide); omega)
      (by decide) (by rw [tex_toNat (by omega)]; omega) (by rw [tex_toNat (by omega)]; omega)
      (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) (hSe.sub (by decide))
      (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) fun m3 hR => ?_
    rw [E.bytes hO2 hSe, tpm_kk hc2] at hR
    generalize m3.mem = M3 at hR
    obtain ⟨Mb, hOb, hFR⟩ := hR
    have hO3 : Out M1 M3 s 484 :=
      hO2.trans ((Out.upK rfl hOb (by decide)).trans (Out.upK (c := 432) (E.Fc 0x1C).symm hFR.out (by decide)))
    have hCc : PmCur M3 F C0 C1 C2 P N nx :=
      ((pm_cur_elem hCa hfa t4).out (r := s + BitVec.ofNat 32 144) (l := 260) hOb
        (E.fs (c := 0x30) (n := 24) (d := 144) (k := 260) (Or.inr (by decide)) (by decide) (by decide)).symm).out
        (r := F + 0x1C) (l := 8) hFR.out (pm_ff F (Or.inl (by decide)) (by decide) (by decide))
    rw [show slice (memBytes M0 P N) ep el = memBytes M0 (P + BitVec.ofNat 32 ep) el from
      tuf_memBytes_drop_take hle]
    refine WP.zero fun hz3 => ?_
    refine WP.lw pm_at_23e (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x1C) (by decide)) ?_; wn
    rcases hof : objField (memBytes M0 (P + BitVec.ofNat 32 ep) el) (ascii!"keyid") with e | ⟨kp, kl⟩ <;>
      rw [hof] at hFR <;> simp only [fieldRes, Except.map] at hFR
    · -- No string `keyid`.
      obtain ⟨-, t1, t2⟩ := hFR
      refine WP.branch pm_at_240 (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
      exact pm_264 E hO3 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
        (by rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
    · -- `keyid` at `kp`.
      obtain ⟨-, t1, t2⟩ := hFR
      have hv := objField_val hof
      rw [memBytes_length] at hv
      have t2' : memLoad32 M3 (F + 0x20) = BitVec.ofNat 32 kl := by
        rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
      have hpk : P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp = P + BitVec.ofNat 32 (ep + kp) := add_ofNat_assoc P ep kp
      have hq1 := nx_q0 hP0 (n := N) (pos := ep + kp) (by omega) (by omega)
      refine WP.branch pm_at_240 (fun eb => ?_) (fun _ => ?_) <;> wn
      · exfalso; (try rsimp at eb); rw [hgsp, t1, hpk, hq1] at eb; exact absurd eb (by decide)
      refine WP.lw pm_at_242 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
      refine WP.aluImm pm_at_244 ?_; wn
      have hc3 := E.code hO3
      refine WP.callStr (tb := TPM_JS) (out := F + 0x48) (p := P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) (n := kl)
        pm_at_246 pm_at_24a (by decide) (by decide) (by decide) hc3.str (by (try rsimp); rw [ev_add, hgsp])
        (by (try rsimp); rw [hgsp, t1]) (by (try rsimp); rw [hgsp, t2']) (by omega)
        (aligned_add E.halF (k := 0x48) (by decide)) (E.lowF (by decide) (by decide) (by decide))
        (E.lowF (by decide) (by decide) (by decide)) fun m4 hS => ?_
      have hSk : Sep s 532 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl := by
        rw [hpk]; exact hSP.subR (by omega)
      rw [E.bytes hO3 hSk, tex_strRes] at hS
      generalize m4.mem = M4 at hS
      have hO4 : Out M1 M4 s 484 := hO3.trans (Out.upK (c := 476) (E.Fc 0x48).symm hS.out (by decide))
      have hCd : PmCur M4 F C0 C1 C2 P N nx :=
        hCc.out (r := F + 0x48) (l := 8) hS.out (pm_ff F (Or.inr (by decide)) (by decide) (by decide))
      refine WP.zero fun hz4 => ?_
      refine WP.lw pm_at_24e (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x48) (by decide)) ?_; wn
      rw [show slice (memBytes M0 (P + BitVec.ofNat 32 ep) el) kp kl =
        memBytes M0 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl from tuf_memBytes_drop_take hv.2]
      rcases hsb : strBody (memBytes M0 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl) with _ | b <;>
        rw [hsb] at hS <;> simp only [Option.map_none, Option.map_some] at hS
      · -- `keyid` is not a string.
        obtain ⟨-, t1, t2⟩ := hS
        refine WP.branch pm_at_250 (fun _ => ?_) (fun eb => ?_) <;> wn
        rotate_left
        · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
        exact pm_29c E hO4 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
          (by rw [show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
      · -- The key ID `b`: compare it with `kid`.
        obtain ⟨-, t1, t2⟩ := hS
        obtain ⟨hb2, hbe⟩ := tex_body hsb
        rw [memBytes_length] at hb2 hbe
        rw [tuf_memBytes_drop_take (by omega), add_ofNat_assoc, add_ofNat_assoc, ← Nat.add_assoc] at hbe
        have hbl : b.length = kl - 2 := by rw [hbe, memBytes_length]
        have hpb : P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp + 1 = P + BitVec.ofNat 32 (ep + kp + 1) := by
          rw [hpk]; exact add_ofNat_assoc P (ep + kp) 1
        have t1' : memLoad32 M4 (F + 0x48) = P + BitVec.ofNat 32 (ep + kp + 1) := t1.trans hpb
        have t2' : memLoad32 M4 (F + 0x4C) = BitVec.ofNat 32 b.length := by
          rw [show F + 0x4C = F + 0x48 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
        have hq2 := nx_q0 hP0 (n := N) (pos := ep + kp + 1) (by omega) (by omega)
        refine WP.branch pm_at_250 (fun eb => ?_) (fun _ => ?_) <;> wn
        · exfalso; (try rsimp at eb); rw [hgsp, t1', hq2] at eb; exact absurd eb (by decide)
        refine WP.lw pm_at_252 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x4C) (by decide)) ?_; wn
        refine WP.alu pm_at_254 ?_; wn
        refine WP.alu pm_at_256 ?_; wn
        have hc4 := E.code hO4
        have hFm : F + 0xFFFFFFFC = s + BitVec.ofNat 32 400 := by rw [← E.hF, BitVec.add_assoc]; rfl
        have hSb : Sep s 532 (P + BitVec.ofNat 32 (ep + kp + 1)) b.length := hSP.subR (by omega)
        refine WP.callSliceEq (tb := TPM_JG + 0xFFFFFFEA) (p := P + BitVec.ofNat 32 (ep + kp + 1)) (q := KQ)
          (pl := b.length) (ql := KL) pm_at_258 pm_at_25c (by decide) (by decide) (by decide) hc4.get.eq
          (by rw [show TPM_JG + 0xFFFFFFEA + 0xFFFFEBAA = TPM_JG + 0xFFFFF616 + 0xFFFFF57E by decide]
              exact hc4.get.ri.es)
          (by rw [show TPM_JG + 0xFFFFFFEA + 0xBF68 = TPM_JG + 0xFFFFF616 + 0xC93C by decide]
              exact hc4.get.ri.mc)
          (by (try rsimp); rw [hgsp, t1']) (by (try rsimp); rw [hgsp, t2'])
          (by (try rsimp); (try simp only [ev0]); exact h9)
          (by (try rsimp); (try simp only [ev0]); exact h24) (by omega) hKL
          (by (try rsimp); rw [hgsp]; exact E.halF)
          (by (try rsimp); rw [hgsp, hFm,
                show TPM_JG + 0xFFFFFFEA + 0xFFFFEBAA = TPM_JG + 0xFFFFF616 + 0xFFFFF57E by decide]
              exact hPS.2.ri.es.sub (by decide))
          (by (try rsimp); rw [hgsp, hFm, show TPM_JG + 0xFFFFFFEA + 0xBF68 = TPM_JG + 0xFFFFF616 + 0xC93C by decide]
              exact hPS.2.ri.mc.sub (by decide))
          (by (try rsimp); rw [hgsp, hFm]; exact hSb.sub (by decide))
          (by (try rsimp); rw [hgsp, hFm]; exact hSK.sub (by decide))
          (by (try rsimp); rw [hgsp, hFm]; exact E.lowS (by decide) (by decide) (by decide)) fun m5 ha0 hO5 => ?_
        have hO5' : Out M4 m5.mem (s + BitVec.ofNat 32 400) 4 := by
          (try rsimp at hO5); rw [hgsp, hFm] at hO5; exact hO5
        have hkb : memBytes M4 (P + BitVec.ofNat 32 (ep + kp + 1)) b.length = b := by
          rw [E.bytes hO4 hSb, hbl, ← hbe]
        rw [hkb, E.bytes hO4 hSK] at ha0
        generalize m5.mem = M5 at hO5'
        have hO6 : Out M1 M5 s 484 := hO4.trans (Out.upK rfl hO5' (by decide))
        have hCe : PmCur M5 F C0 C1 C2 P N nx :=
          hCd.out hO5' (E.fs (c := 0x30) (n := 24) (d := 400) (k := 4) (Or.inr (by decide)) (by decide)
            (by decide)).symm
        refine WP.zero fun hz5 => ?_
        by_cases hbk : b = memBytes M0 KQ KL
        · -- A repeated key ID.
          simp only [hbk, ↓reduceIte] at ha0 ⊢
          refine WP.branch pm_at_260 (fun eb => ?_) (fun _ => ?_) <;> wn
          · exfalso; (try rsimp at eb); rw [ha0] at eb; exact absurd eb (by decide)
          refine WP.jal pm_at_262 (by decide) ?_; wn
          exact pm_116 E hO6 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp) (by (try rsimp))
            (by keepz E.hz0)
        · -- A different key ID: the next element.
          simp only [hbk, ↓reduceIte] at ha0 ⊢
          refine WP.branch pm_at_260 (fun _ => ?_) (fun eb => ?_) <;> wn
          rotate_left
          · exfalso; (try rsimp at eb); rw [ha0] at eb; exact absurd eb (by decide)
          exact ih nx M5 _ hO6 hCe hxN (by omega) (by pmkeep hK) (by (try rsimp); exact h9)
            (by (try rsimp); exact h24) (by (try rsimp)) (by keepz E.hz0)

end


section
variable {M0 M1 Mf : Word → BitVec 8} {s out F : Word} {g g0 : Fin 32 → Word}

/-- `pm_ok` with the two addresses named. -/
theorem pm_ok2 (E : PmEnv M0 M1 s out F g0) (hO : Out M1 Mf s 484) (h26 : g 26 = out) (hsp : g sp = F)
    {A B : Word} {l1 l2 : Nat} (h19 : g 19 = A) (h21 : g 21 = B) (h20 : g 20 = BitVec.ofNat 32 l1)
    (h18 : g 18 = BitVec.ofNat 32 l2) (hfr : ∀ x, x ∉ pmE → g x = g0 x) :
    WP tufParseMetadataCode TPM (pmQ M0 s out g0 (.ok (A, l1, B, l2))) Mf 0x2A2 g := by
  rw [← h19, ← h21]; exact pm_ok E hO h26 hsp h20 h18 hfr

end

section
variable {M0 M1 : Word → BitVec 8} {s out F : Word} {g0 : Fin 32 → Word}

set_option maxHeartbeats 8000000 in
/-- The outer loop at 0x19C: each element of the signatures array from the
outer cursor at `F + 0x30` has string `keyid` and `sig` members, and no
later element repeats its key ID. It ends with `signed` and `signatures`
at `out`, from `s3` and `s4` and from `s5` and `s2`. -/
theorem pm_outer (E : PmEnv M0 M1 s out F g0) {gK : Fin 32 → Word} (hKsp : gK sp = F) (hK26 : gK 26 = out)
    (hK23 : gK 23 = TPM_KK) (hK22 : gK 22 = TPM_KG) {L1 L2 : Nat} (hK20 : gK 20 = BitVec.ofNat 32 L1)
    (hK18 : gK 18 = BitVec.ofNat 32 L2) {P : Word} {N : Nat} (hP0 : P.toNat ≠ 0) (hPN : P.toNat + N < 2 ^ 32)
    (hSP : Sep s 532 P N) :
    ∀ (k pos : Nat) (Mk : Word → BitVec 8) (g : Fin 32 → Word), Out M1 Mk s 484 → PmOc Mk F P N pos →
      pos ≤ N → N < pos + k → (∀ x, x ∈ pmKL → g x = gK x) → g 0 = 0 → (∀ x, x ∉ pmE → g x = g0 x) →
      WP tufParseMetadataCode TPM
        (pmQ M0 s out g0 (pmThen (pmSigs (memBytes M0 P N) k pos) (.ok (gK 19, L1, gK 21, L2)))) Mk 0x19C g := by
  intro k
  induction k with
  | zero => intro pos _ _ _ _ h1 h2; exfalso; omega
  | succ k ih =>
  intro pos Mk g hO hC hpos hk hK hz hfr
  have hgsp : g sp = F := (hK sp (by decide)).trans hKsp
  have hg26 : g 26 = out := (hK 26 (by decide)).trans hK26
  have hg23 : g 23 = TPM_KK := (hK 23 (by decide)).trans hK23
  have hg22 : g 22 = TPM_KG := (hK 22 (by decide)).trans hK22
  have hc := E.code hO
  have hPS := tpm_parseSep E.hsw E.hro
  refine WP.aluImm pm_at_19c ?_; wn
  refine WP.aluImm pm_at_19e ?_; wn
  refine WP.callNextElement (tb := TPM_JNE) (out := F + 0x1C) (c := F + 0x30)
    (s := s + BitVec.ofNat 32 256) (p := P) (n := N) (pos := pos) pm_at_1a0 pm_at_1a4 (by decide) (by decide)
    (by decide) hc.ne hc.ri (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [ev_add, hgsp])
    (by (try rsimp); rw [hgsp]; exact (E.sp 256 (by decide)).symm) (E.alS (by decide))
    (aligned_add E.halF (by decide)) (aligned_add E.halF (by decide)) hC.1
    (by rw [BitVec.add_assoc]; exact hC.2.1) (by rw [BitVec.add_assoc]; exact hC.2.2)
    (by omega) (by omega) hP0 (by omega)
    (by rw [show TPM_JNE + 0xFFFFF7E0 = TPM_JG + 0xFFFFF616 by decide]; exact hPS.2.ri.sub (by decide))
    (E.lowS (by decide) (by decide) (by decide)) (hSP.sub (by decide))
    (E.fs (Or.inr (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
    (pm_ff F (Or.inl (by decide)) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.lowF (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide)) fun m2 hR => ?_
  rw [E.bytes hO hSP] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨Ma, hOa, hER⟩ := hR
  have hOE := pm_elemOut E (d := 0x30) (by decide) (by decide) hER
  have hO2 : Out M1 M2 s 484 := hO.trans ((Out.upK rfl hOa (by decide)).trans hOE)
  have hCa := hC.out hOa (E.fs (c := 0x30) (n := 12) (d := 256) (k := 148) (Or.inr (by decide)) (by decide)
    (by decide)).symm
  refine WP.zero fun hz2 => ?_
  refine WP.lbu pm_at_1a8 ?_; wn
  simp only [pmSigs]
  rcases hne : nextElement (memBytes M0 P N) pos with _ | _ | ⟨ep, el, nx⟩ <;> rw [hne] at hER <;>
    simp only [elemRes, Option.map_none, Option.map_some] at hER
  · -- An error inside the array.
    obtain ⟨-, t1, t2⟩ := hER
    refine WP.branch pm_at_1ac (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    exact pm_8e E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
      (by rw [show F + 0x1D = F + 0x1C + 1 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
  · -- The end of the array: success.
    obtain ⟨hfa, t1, t2⟩ := hER
    refine WP.branch pm_at_1ac (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_1b0 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    refine WP.branch pm_at_1b2 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb)
      rw [hgsp, show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl, t2] at eb; exact absurd eb (by decide)
    exact pm_ok2 E hO2 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
      (by (try rsimp); exact hK 19 (by decide)) (by (try rsimp); exact hK 21 (by decide))
      (by (try rsimp); exact (hK 20 (by decide)).trans hK20) (by (try rsimp); exact (hK 18 (by decide)).trans hK18)
      (by keepz E.hz0)
  · -- An element at `ep`.
    obtain ⟨hfa, t1, t2, t3, t4⟩ := hER
    obtain ⟨rfl, hpx, hel, hle, hxN⟩ := nextElement_lt hne
    rw [memBytes_length] at hle hxN
    have hCb := pm_oc_elem hCa hfa t4
    refine WP.branch pm_at_1ac (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_1b0 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
    have t2' : memLoad32 M2 (F + 0x20) = P + BitVec.ofNat 32 ep := by
      rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
    have t3' : memLoad32 M2 (F + 0x24) = BitVec.ofNat 32 el := by
      rw [show F + 0x24 = F + 0x1C + 8 by rw [BitVec.add_assoc]; rfl]; exact t3
    have hq0 := nx_q0 hP0 (n := N) (pos := ep) (by omega) (by omega)
    refine WP.branch pm_at_1b2 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hgsp, t2', hq0] at eb; exact absurd eb (by decide)
    refine WP.lw pm_at_1b4 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x24) (by decide)) ?_; wn
    refine WP.aluImm pm_at_1b6 ?_; wn
    refine WP.aluImm pm_at_1b8 ?_; wn
    refine WP.alu pm_at_1ba ?_; wn
    refine WP.alu pm_at_1bc ?_; wn
    refine WP.alu pm_at_1be ?_; wn
    have hc2 := E.code hO2
    have hSe : Sep s 532 (P + BitVec.ofNat 32 ep) el := hSP.subR hle
    refine WP.callField (tb := TPM_JF) (out := F + 0x1C) (s := s + BitVec.ofNat 32 144)
      (p := P + BitVec.ofNat 32 ep) (kq := TPM_KK) (n := el) (kl := 5)
      pm_at_1c0 pm_at_1c4 (by decide) (by decide) (by decide) hc2.fieldC
      (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); (try simp only [ev0]); rw [hgsp, t2'])
      (by (try rsimp); (try simp only [ev0]); rw [hgsp, t3'])
      (by (try rsimp); (try simp only [ev0]); exact hg23) (by (try rsimp); (try simp only [ev0]); (try rfl))
      (by (try rsimp); rw [hgsp]; exact (E.sp 144 (by decide)).symm)
      (E.alS (by decide)) (aligned_add E.halF (by decide)) (by have := E.wS (d := 144) (k := 260) (by decide); omega)
      (by decide) (by rw [tex_toNat (by omega)]; omega) (by rw [tex_toNat (by omega)]; omega)
      (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) (hSe.sub (by decide))
      (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
      (E.lowF (by decide) (by decide) (by decide)) fun m3 hR => ?_
    rw [E.bytes hO2 hSe, tpm_kk hc2] at hR
    generalize m3.mem = M3 at hR
    obtain ⟨Mb, hOb, hFR⟩ := hR
    have hO3 : Out M1 M3 s 484 :=
      hO2.trans ((Out.upK rfl hOb (by decide)).trans (Out.upK (c := 432) (E.Fc 0x1C).symm hFR.out (by decide)))
    have hC3 : PmOc M3 F P N nx :=
      (hCb.out (r := s + BitVec.ofNat 32 144) (l := 260) hOb
        (E.fs (c := 0x30) (n := 12) (d := 144) (k := 260) (Or.inr (by decide)) (by decide) (by decide)).symm).out
        (r := F + 0x1C) (l := 8) hFR.out (pm_ff F (Or.inl (by decide)) (by decide) (by decide))
    rw [show slice (memBytes M0 P N) ep el = memBytes M0 (P + BitVec.ofNat 32 ep) el from
      tuf_memBytes_drop_take hle]
    refine WP.zero fun hz3 => ?_
    refine WP.lw pm_at_1c8 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x1C) (by decide)) ?_; wn
    rcases hof : objField (memBytes M0 (P + BitVec.ofNat 32 ep) el) (ascii!"keyid") with e | ⟨kp, kl⟩ <;>
      rw [hof] at hFR <;> simp only [fieldRes, Except.map] at hFR
    · -- No `keyid`.
      obtain ⟨-, t1, t2⟩ := hFR
      refine WP.branch pm_at_1ca (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
      exact pm_264 E hO3 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
        (by rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
    · -- `keyid` at `kp`.
      obtain ⟨-, t1, t2⟩ := hFR
      have hv := objField_val hof
      rw [memBytes_length] at hv
      have t2' : memLoad32 M3 (F + 0x20) = BitVec.ofNat 32 kl := by
        rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
      have hpk : P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp = P + BitVec.ofNat 32 (ep + kp) := add_ofNat_assoc P ep kp
      have hq1 := nx_q0 hP0 (n := N) (pos := ep + kp) (by omega) (by omega)
      refine WP.branch pm_at_1ca (fun eb => ?_) (fun _ => ?_) <;> wn
      · exfalso; (try rsimp at eb); rw [hgsp, t1, hpk, hq1] at eb; exact absurd eb (by decide)
      refine WP.sw pm_at_1cc (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0xC) (by decide))
        (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
      rw [hgsp, t3']
      have o3a := out_store32 M3 (F + 0xC) (BitVec.ofNat 32 el)
      have v0C := memLoad32_store32_same M3 (F + 0xC) (BitVec.ofNat 32 el)
      generalize memStore32 M3 (F + 0xC) (BitVec.ofNat 32 el) = M3a at o3a v0C
      have hO3a : Out M1 M3a s 484 := hO3.trans (Out.upK (c := 416) (E.Fc 0xC).symm o3a (by decide))
      have hC3a : PmOc M3a F P N nx :=
        hC3.out o3a (pm_ff F (Or.inl (by decide)) (by decide) (by decide))
      refine WP.lw pm_at_1ce (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
      refine WP.aluImm pm_at_1d0 ?_; wn
      have hc3 := E.code hO3a
      have t2a : memLoad32 M3a (F + 0x20) = BitVec.ofNat 32 kl :=
        (o3a.load32 (pm_ff F (c := 0xC) (n := 4) (d := 0x20) (k := 4) (Or.inl (by decide)) (by decide)
          (by decide))).trans t2'
      refine WP.callStr (tb := TPM_JS) (out := F + 0x3C) (p := P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) (n := kl)
        pm_at_1d2 pm_at_1d6 (by decide) (by decide) (by decide) hc3.str (by (try rsimp); rw [ev_add, hgsp])
        (by (try rsimp); rw [t1]) (by (try rsimp); rw [hgsp, t2a]) (by omega)
        (aligned_add E.halF (k := 0x3C) (by decide)) (E.lowF (by decide) (by decide) (by decide))
        (E.lowF (by decide) (by decide) (by decide)) fun m4 hS => ?_
      have hSk : Sep s 532 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl := by
        rw [hpk]; exact hSP.subR (by omega)
      rw [E.bytes hO3a hSk, tex_strRes] at hS
      generalize m4.mem = M4 at hS
      have hO4 : Out M1 M4 s 484 := hO3a.trans (Out.upK (c := 464) (E.Fc 0x3C).symm hS.out (by decide))
      have hC4 : PmOc M4 F P N nx :=
        hC3a.out (r := F + 0x3C) (l := 8) hS.out (pm_ff F (Or.inr (by decide)) (by decide) (by decide))
      have v0C4 : memLoad32 M4 (F + 0xC) = BitVec.ofNat 32 el :=
        (hS.out.load32 (pm_ff F (c := 0x3C) (n := 8) (d := 0xC) (k := 4) (Or.inr (by decide)) (by decide)
          (by decide))).trans v0C
      refine WP.zero fun hz4 => ?_
      refine WP.lw pm_at_1da (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x3C) (by decide)) ?_; wn
      refine WP.sw pm_at_1dc (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 8) (by decide))
        (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
      rw [show slice (memBytes M0 (P + BitVec.ofNat 32 ep) el) kp kl =
        memBytes M0 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl from tuf_memBytes_drop_take hv.2]
      have o4a := fun v => out_store32 M4 (F + 8) v
      have hO4a : ∀ v, Out M1 (memStore32 M4 (F + 8) v) s 484 := fun v =>
        hO4.trans (Out.upK (c := 412) (E.Fc 8).symm (o4a v) (by decide))
      rcases hsb : strBody (memBytes M0 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp) kl) with _ | b <;>
        rw [hsb] at hS <;> simp only [Option.map_none, Option.map_some] at hS
      · -- `keyid` is not a string.
        obtain ⟨-, t1, t2⟩ := hS
        rw [hgsp]
        refine WP.branch pm_at_1de (fun _ => ?_) (fun eb => ?_) <;> wn
        rotate_left
        · exfalso; (try rsimp at eb); rw [t1] at eb; exact absurd eb (by decide)
        exact pm_296 E (hO4a _) (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
          (by rw [memStore32_get_sep (a := F + 8) (x := F + 0x40) (pm_ff F (c := 8) (n := 4) (d := 0x40) (k := 1)
                (Or.inl (by decide)) (by decide) (by decide)),
              show F + 0x40 = F + 0x3C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
      · -- The key ID `b` at `KQ`.
        obtain ⟨-, t1, t2⟩ := hS
        obtain ⟨hb2, hbe⟩ := tex_body hsb
        rw [memBytes_length] at hb2 hbe
        rw [tuf_memBytes_drop_take (by omega), add_ofNat_assoc, add_ofNat_assoc, ← Nat.add_assoc] at hbe
        have hbl : b.length = kl - 2 := by rw [hbe, memBytes_length]
        have hpb : P + BitVec.ofNat 32 ep + BitVec.ofNat 32 kp + 1 = P + BitVec.ofNat 32 (ep + kp + 1) := by
          rw [hpk]; exact add_ofNat_assoc P (ep + kp) 1
        have t1' : memLoad32 M4 (F + 0x3C) = P + BitVec.ofNat 32 (ep + kp + 1) := t1.trans hpb
        have t2b : memLoad32 M4 (F + 0x40) = BitVec.ofNat 32 b.length := by
          rw [show F + 0x40 = F + 0x3C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
        have hq2 := nx_q0 hP0 (n := N) (pos := ep + kp + 1) (by omega) (by omega)
        have hSK : Sep s 532 (P + BitVec.ofNat 32 (ep + kp + 1)) b.length := hSP.subR (by omega)
        have hkb : memBytes M0 (P + BitVec.ofNat 32 (ep + kp + 1)) b.length = b := by
          rw [hbl, ← hbe]
        rw [hgsp, t1']
        refine WP.branch pm_at_1de (fun eb => ?_) (fun _ => ?_) <;> wn
        · exfalso; (try rsimp at eb); rw [hq2] at eb; exact absurd eb (by decide)
        have o5 := o4a (P + BitVec.ofNat 32 (ep + kp + 1))
        have hO5 := hO4a (P + BitVec.ofNat 32 (ep + kp + 1))
        have v08 := memLoad32_store32_same M4 (F + 8) (P + BitVec.ofNat 32 (ep + kp + 1))
        generalize memStore32 M4 (F + 8) (P + BitVec.ofNat 32 (ep + kp + 1)) = M5 at o5 hO5 v08
        have hC5 : PmOc M5 F P N nx := hC4.out o5 (pm_ff F (Or.inl (by decide)) (by decide) (by decide))
        have v0C5 : memLoad32 M5 (F + 0xC) = BitVec.ofNat 32 el :=
          (o5.load32 (pm_ff F (c := 8) (n := 4) (d := 0xC) (k := 4) (Or.inl (by decide)) (by decide)
            (by decide))).trans v0C4
        have t2c : memLoad32 M5 (F + 0x40) = BitVec.ofNat 32 b.length :=
          (o5.load32 (pm_ff F (c := 8) (n := 4) (d := 0x40) (k := 4) (Or.inl (by decide)) (by decide)
            (by decide))).trans t2b
        refine WP.lw pm_at_1e0 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x40) (by decide)) ?_; wn
        refine WP.aluImm pm_at_1e2 ?_; wn
        refine WP.aluImm pm_at_1e4 ?_; wn
        refine WP.alu pm_at_1e6 ?_; wn
        refine WP.lw pm_at_1e8 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0xC) (by decide)) ?_; wn
        refine WP.alu pm_at_1ea ?_; wn
        have hc5 := E.code hO5
        refine WP.callField (tb := TPM_JF) (out := F + 0x1C) (s := s + BitVec.ofNat 32 144)
          (p := P + BitVec.ofNat 32 ep) (kq := TPM_KG) (n := el) (kl := 3)
          pm_at_1ec pm_at_1f0 (by decide) (by decide) (by decide) hc5.fieldC
          (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); (try simp only [ev0]); assumption)
          (by (try rsimp); (try simp only [ev0]); rw [hgsp, v0C5])
          (by (try rsimp); (try simp only [ev0]); exact hg22) (by (try rsimp); (try simp only [ev0]); (try rfl))
          (by (try rsimp); rw [hgsp]; exact (E.sp 144 (by decide)).symm)
          (E.alS (by decide)) (aligned_add E.halF (by decide)) (by have := E.wS (d := 144) (k := 260) (by decide); omega)
          (by decide) (by rw [tex_toNat (by omega)]; omega) (by rw [tex_toNat (by omega)]; omega)
          (tuf_fieldSep (E.wS (by decide)) (E.hro.sub (by decide))) (hSe.sub (by decide))
          (tuf_sep_ro (E.hro.sub (by decide)) (by decide) (by decide)) (E.fs (Or.inr (by decide)) (by decide) (by decide))
          (E.lowF (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
          (E.lowF (by decide) (by decide) (by decide)) fun m6 hR => ?_
        rw [E.bytes hO5 hSe, tpm_kg hc5] at hR
        generalize m6.mem = M6 at hR
        obtain ⟨Mc, hOc, hFR⟩ := hR
        have hO6 : Out M1 M6 s 484 :=
          hO5.trans ((Out.upK rfl hOc (by decide)).trans (Out.upK (c := 432) (E.Fc 0x1C).symm hFR.out (by decide)))
        have hC6 : PmOc M6 F P N nx :=
          (hC5.out (r := s + BitVec.ofNat 32 144) (l := 260) hOc
            (E.fs (c := 0x30) (n := 12) (d := 144) (k := 260) (Or.inr (by decide)) (by decide) (by decide)).symm).out
            (r := F + 0x1C) (l := 8) hFR.out (pm_ff F (Or.inl (by decide)) (by decide) (by decide))
        have v086 : memLoad32 M6 (F + 8) = P + BitVec.ofNat 32 (ep + kp + 1) :=
          (hFR.out.load32 (pm_ff F (c := 0x1C) (n := 8) (d := 8) (k := 4) (Or.inr (by decide)) (by decide)
            (by decide))).trans ((hOc.load32 (E.fs (c := 8) (n := 4) (d := 144) (k := 260) (Or.inr (by decide))
              (by decide) (by decide)).symm).trans v08)
        refine WP.zero fun hz6 => ?_
        refine WP.lw pm_at_1f4 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x1C) (by decide)) ?_; wn
        rcases hog : objField (memBytes M0 (P + BitVec.ofNat 32 ep) el) (ascii!"sig") with e | ⟨sq, sl⟩ <;>
          rw [hog] at hFR <;> simp only [fieldRes, Except.map] at hFR
        · -- No `sig`.
          obtain ⟨-, t1, t2⟩ := hFR
          refine WP.branch pm_at_1f6 (fun _ => ?_) (fun eb => ?_) <;> wn
          rotate_left
          · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
          exact pm_264 E hO6 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
            (by rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
        · -- `sig` at `sq`.
          obtain ⟨-, t1, t2⟩ := hFR
          have hw := objField_val hog
          rw [memBytes_length] at hw
          have t2s : memLoad32 M6 (F + 0x20) = BitVec.ofNat 32 sl := by
            rw [show F + 0x20 = F + 0x1C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
          have hps : P + BitVec.ofNat 32 ep + BitVec.ofNat 32 sq = P + BitVec.ofNat 32 (ep + sq) :=
            add_ofNat_assoc P ep sq
          have hq3 := nx_q0 hP0 (n := N) (pos := ep + sq) (by omega) (by omega)
          refine WP.branch pm_at_1f6 (fun eb => ?_) (fun _ => ?_) <;> wn
          · exfalso; (try rsimp at eb); rw [hgsp, t1, hps, hq3] at eb; exact absurd eb (by decide)
          refine WP.lw pm_at_1f8 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x20) (by decide)) ?_; wn
          refine WP.aluImm pm_at_1fa ?_; wn
          have hc6 := E.code hO6
          refine WP.callStr (tb := TPM_JS) (out := F + 0x3C) (p := P + BitVec.ofNat 32 ep + BitVec.ofNat 32 sq)
            (n := sl) pm_at_1fc pm_at_200 (by decide) (by decide) (by decide) hc6.str
            (by (try rsimp); rw [ev_add, hgsp]) (by (try rsimp); rw [hgsp, t1]) (by (try rsimp); rw [hgsp, t2s])
            (by omega) (aligned_add E.halF (k := 0x3C) (by decide)) (E.lowF (by decide) (by decide) (by decide))
            (E.lowF (by decide) (by decide) (by decide)) fun m7 hS => ?_
          have hSs : Sep s 532 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 sq) sl := by
            rw [hps]; exact hSP.subR (by omega)
          rw [E.bytes hO6 hSs, tex_strRes] at hS
          generalize m7.mem = M7 at hS
          have hO7 : Out M1 M7 s 484 := hO6.trans (Out.upK (c := 464) (E.Fc 0x3C).symm hS.out (by decide))
          have hC7 : PmOc M7 F P N nx :=
            hC6.out (r := F + 0x3C) (l := 8) hS.out (pm_ff F (Or.inr (by decide)) (by decide) (by decide))
          have v087 : memLoad32 M7 (F + 8) = P + BitVec.ofNat 32 (ep + kp + 1) :=
            (hS.out.load32 (pm_ff F (c := 0x3C) (n := 8) (d := 8) (k := 4) (Or.inr (by decide)) (by decide)
              (by decide))).trans v086
          refine WP.zero fun hz7 => ?_
          refine WP.lw pm_at_204 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x3C) (by decide)) ?_; wn
          rw [show slice (memBytes M0 (P + BitVec.ofNat 32 ep) el) sq sl =
            memBytes M0 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 sq) sl from tuf_memBytes_drop_take hw.2]
          rcases hsc : strBody (memBytes M0 (P + BitVec.ofNat 32 ep + BitVec.ofNat 32 sq) sl) with _ | c <;>
            rw [hsc] at hS <;> simp only [Option.map_none, Option.map_some] at hS
          · -- `sig` is not a string.
            obtain ⟨-, t1, t2⟩ := hS
            refine WP.branch pm_at_206 (fun _ => ?_) (fun eb => ?_) <;> wn
            rotate_left
            · exfalso; (try rsimp at eb); rw [hgsp, t1] at eb; exact absurd eb (by decide)
            exact pm_296 E hO7 (by (try rsimp); exact hg26) (by (try rsimp); exact hgsp)
              (by rw [show F + 0x40 = F + 0x3C + 4 by rw [BitVec.add_assoc]; rfl]; exact t2) (by keepz E.hz0)
          · -- Both strings: look for `b` in the later elements.
            obtain ⟨-, t1, -⟩ := hS
            obtain ⟨hc2, -⟩ := tex_body hsc
            rw [memBytes_length] at hc2
            have hq4 := nx_q0 hP0 (n := N) (pos := ep + sq + 1) (by omega) (by omega)
            have t1s : memLoad32 M7 (F + 0x3C) = P + BitVec.ofNat 32 (ep + sq + 1) := by
              rw [t1, hps]; exact add_ofNat_assoc P (ep + sq) 1
            refine WP.branch pm_at_206 (fun eb => ?_) (fun _ => ?_) <;> wn
            · exfalso; (try rsimp at eb); rw [hgsp, t1s, hq4] at eb; exact absurd eb (by decide)
            refine WP.lw pm_at_208 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x30) (by decide)) ?_
            wn
            refine WP.lw pm_at_20a (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x34) (by decide)) ?_
            wn
            refine WP.lw pm_at_20c (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x38) (by decide)) ?_
            wn
            refine WP.sw pm_at_20e (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x3C) (by decide))
              (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
            refine WP.sw pm_at_210 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x40) (by decide))
              (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
            refine WP.sw pm_at_212 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 0x44) (by decide))
              (by (try rsimp); rw [hgsp]; exact E.lowF (by decide) (by decide) (by decide)) ?_; wn
            rw [hgsp, hC7.1, hC7.2.1, hC7.2.2]
            obtain ⟨hCur, o8⟩ := pm_copy hC7
            generalize memStore32 (memStore32 (memStore32 M7 (F + 0x3C) P) (F + 0x40) (BitVec.ofNat 32 N)) (F + 0x44)
              (BitVec.ofNat 32 nx) = M8 at hCur o8
            have hO8 : Out M1 M8 s 484 := hO7.trans (Out.upK (c := 464) (E.Fc 0x3C).symm o8 (by decide))
            have v088 : memLoad32 M8 (F + 8) = P + BitVec.ofNat 32 (ep + kp + 1) :=
              (o8.load32 (pm_ff F (c := 0x3C) (n := 12) (d := 8) (k := 4) (Or.inr (by decide)) (by decide)
                (by decide))).trans v087
            refine WP.lw pm_at_214 (by (try rsimp); rw [hgsp]; exact aligned_add E.halF (k := 8) (by decide)) ?_; wn
            rw [pmThen_assoc, memBytes_length, ← hkb]
            exact pm_inner E hKsp hK26 hK23 hP0 hPN hSP hSK (by omega)
              (fun Mk g hO c0 c1 c2 hK' hz hfr => ih nx Mk g hO ⟨c0, c1, c2⟩ hxN (by omega) hK' hz hfr)
              (N + 1) nx M8 _ hO8 hCur hxN (by omega) (by pmkeep hK) (by (try rsimp); rw [hgsp, v088])
              (by (try rsimp); rw [t2c]) (by (try rsimp)) (by keepz E.hz0)

end

/-- The inline comparison of six key bytes with `signed`. -/
theorem pm_signed (b0 b1 b2 b3 b4 b5 : BitVec 8) :
    aluEval .or (aluEval .xor (aluEval .or (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))
      (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))) 0x6E676973)
      (aluEval .xor 0x6465 (aluEval .or (aluEval .sll (b5.zeroExtend 32) 8) (b4.zeroExtend 32))) = 0 ↔
    [b0.toNat, b1.toNat, b2.toNat, b3.toNat, b4.toNat, b5.toNat] = ascii!"signed" := by
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt; have h4 := b4.isLt
  have h5 := b5.isLt
  have s1 : (aluEval .sll (b1.zeroExtend 32) 8).toNat = b1.toNat * 256 := sll_byte b1 (by decide)
  have s2 : (aluEval .sll (b2.zeroExtend 32) 0x10).toNat = b2.toNat * 65536 := sll_byte b2 (by decide)
  have s3 : (aluEval .sll (b3.zeroExtend 32) 0x18).toNat = b3.toNat * 16777216 := sll_byte b3 (by decide)
  have s5 : (aluEval .sll (b5.zeroExtend 32) 8).toNat = b5.toNat * 256 := sll_byte b5 (by decide)
  have eA : (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32)).toNat =
      b1.toNat * 256 + b0.toNat := by
    rw [or_nat (i := 8) _ _ (by rw [s1]; omega) (by rw [zext_tn]; omega), s1, zext_tn]
  have eB : (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18)).toNat =
      b2.toNat * 65536 + b3.toNat * 16777216 := by
    rw [or_nat' (i := 24) _ _ (by rw [s2]; omega) (by rw [s3]; omega), s2, s3]
  have e1 : (aluEval .or (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))
      (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))).toNat =
      b1.toNat * 256 + b0.toNat + (b2.toNat * 65536 + b3.toNat * 16777216) := by
    rw [or_nat' (i := 16) _ _ (by rw [eA]; omega) (by rw [eB]; omega), eA, eB]
  have e2 : (aluEval .or (aluEval .sll (b5.zeroExtend 32) 8) (b4.zeroExtend 32)).toNat = b5.toNat * 256 + b4.toNat := by
    rw [or_nat (i := 8) _ _ (by rw [s5]; omega) (by rw [zext_tn]; omega), s5, zext_tn]
  have hL : [b0.toNat, b1.toNat, b2.toNat, b3.toNat, b4.toNat, b5.toNat] = ascii!"signed" ↔
      b0.toNat = 0x73 ∧ b1.toNat = 0x69 ∧ b2.toNat = 0x67 ∧ b3.toNat = 0x6E ∧ b4.toNat = 0x65 ∧
        b5.toNat = 0x64 := by
    simp only [List.cons.injEq, and_true]; (try decide)
  rw [hL]
  have key : ∀ x y : Word, aluEval .or x y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
  have kx : ∀ x y : Word, aluEval .xor x y = 0 ↔ x = y := fun _ _ => BitVec.xor_eq_zero_iff
  refine (key _ _).trans ((and_congr (kx _ _) (kx _ _)).trans ?_)
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, e1, e2]
  rw [show (0x6E676973 : Word).toNat = 0x6E676973 from rfl, show (0x6465 : Word).toNat = 0x6465 from rfl]
  constructor
  · intro ⟨ha, hb⟩
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro ⟨c0, c1, c2, c3, c4, c5⟩
    exact ⟨by omega, by omega⟩



end C3.RV32
