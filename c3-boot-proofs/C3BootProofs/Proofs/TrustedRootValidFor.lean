import C3BootProofs.Proofs.TrustedRootDecode
import C3BootProofs.Proofs.JsonField
import C3BootProofs.Proofs.TimeRfc3339
import C3BootProofs.Proofs.DerOid
import C3BootProofs.Image.BootloaderData3

/-!
# `trusted_root::valid_for`

`valid_for(v)` reads a `validFor` object: the RFC 3339 time in its `start`
member, and the one in its `end` member, or `u64::MAX` when it has none.
It returns a `Window` or the first error. The compiled function calls
`Value::field`, `Value::get`, `Value::str`, and `time::rfc3339`, whose
theorems `jsonField_correct`, `jsonGet_correct`, `jsonStr_correct`, and
`timeRfc3339_correct` are.

`validForPos` is the result on the bytes of the object, in the
position-level models of `JsonGet.lean` and `JsonField.lean`, and
`trustedRootValidFor_correct` proves the function from its entry to its
return against it.

The keys `start` and `end` are string literals in `.rodata` that the
extractor doesn't name. They sit right after `svOidEcPublicKey`'s 7 bytes,
at `svOidEcPublicKeyAddress + 7` and `+ 0xC`, where the function's
`lui`/`addi` pairs point, and the theorem takes their bytes as
hypotheses.
-/

namespace C3.RV32

open C3.Image C3.Json

/-- Where `valid_for` is in the image. -/
abbrev TVF : Word := BitVec.ofNat 32 trustedRootValidForAddress

/-- Where `Value::field` is in the image. -/
abbrev TJF : Word := BitVec.ofNat 32 jsonFieldAddress

/-- Where `Value::str` is in the image. -/
abbrev TJS : Word := BitVec.ofNat 32 jsonStrAddress

/-- The start of the read-only window, which holds the literals that
`read_item` and `valid_for` read. -/
abbrev TVF_RO : Word := BitVec.ofNat 32 roWindowAddress

/-- The address of the key `start`. -/
abbrev tvfStartKey : Word := BitVec.ofNat 32 (img% svOidEcPublicKeyAddress + 0x7)

/-- The address of the key `end`. -/
abbrev tvfEndKey : Word := BitVec.ofNat 32 (img% svOidEcPublicKeyAddress + 0xC)

set_option maxRecDepth 20000

theorem tvf_at_0 : fetchRel trustedRootValidForCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem tvf_at_2 : fetchRel trustedRootValidForCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem tvf_at_4 : fetchRel trustedRootValidForCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem tvf_at_6 : fetchRel trustedRootValidForCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem tvf_at_8 : fetchRel trustedRootValidForCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem tvf_at_a : fetchRel trustedRootValidForCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem tvf_at_c : fetchRel trustedRootValidForCode 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem tvf_at_e : fetchRel trustedRootValidForCode 0xE = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem tvf_at_10 : fetchRel trustedRootValidForCode 0x10 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem tvf_at_12 : fetchRel trustedRootValidForCode 0x12 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem tvf_at_14 : fetchRel trustedRootValidForCode 0x14 = some (.lui a3 (img% hi20 (svOidEcPublicKeyAddress + 0x7)), 4) := by decide
theorem tvf_at_18 : fetchRel trustedRootValidForCode 0x18 = some (.aluImm .add a3 a3 (img% lo12 (svOidEcPublicKeyAddress + 0x7)), 4) := by decide
theorem tvf_at_1c : fetchRel trustedRootValidForCode 0x1C = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem tvf_at_1e : fetchRel trustedRootValidForCode 0x1E = some (.aluImm .add a4 x0 0x5, 2) := by decide
theorem tvf_at_20 : fetchRel trustedRootValidForCode 0x20 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem tvf_at_24 : fetchRel trustedRootValidForCode 0x24 = some (.jalr ra ra 0xFFFFF904, 4) := by decide
theorem tvf_at_28 : fetchRel trustedRootValidForCode 0x28 = some (.load .lw a1 sp 0x20, 2) := by decide
theorem tvf_at_2a : fetchRel trustedRootValidForCode 0x2A = some (.branch .beq a1 x0 0x7E, 2) := by decide
theorem tvf_at_2c : fetchRel trustedRootValidForCode 0x2C = some (.load .lw a2 sp 0x24, 2) := by decide
theorem tvf_at_2e : fetchRel trustedRootValidForCode 0x2E = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem tvf_at_30 : fetchRel trustedRootValidForCode 0x30 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem tvf_at_34 : fetchRel trustedRootValidForCode 0x34 = some (.jalr ra ra 0xFFFFF930, 4) := by decide
theorem tvf_at_38 : fetchRel trustedRootValidForCode 0x38 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem tvf_at_3a : fetchRel trustedRootValidForCode 0x3A = some (.branch .beq a1 x0 0x3C, 2) := by decide
theorem tvf_at_3c : fetchRel trustedRootValidForCode 0x3C = some (.load .lw a2 sp 0xC, 2) := by decide
theorem tvf_at_3e : fetchRel trustedRootValidForCode 0x3E = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem tvf_at_40 : fetchRel trustedRootValidForCode 0x40 = some (.auipc ra 0x0, 4) := by decide
theorem tvf_at_44 : fetchRel trustedRootValidForCode 0x44 = some (.jalr ra ra 0x110, 4) := by decide
theorem tvf_at_48 : fetchRel trustedRootValidForCode 0x48 = some (.load .lbu a0 sp 0x10, 4) := by decide
theorem tvf_at_4c : fetchRel trustedRootValidForCode 0x4C = some (.branch .bne a0 x0 0x24, 2) := by decide
theorem tvf_at_4e : fetchRel trustedRootValidForCode 0x4E = some (.load .lw (19 : Fin 32) sp 0x18, 2) := by decide
theorem tvf_at_50 : fetchRel trustedRootValidForCode 0x50 = some (.load .lw (20 : Fin 32) sp 0x1C, 2) := by decide
theorem tvf_at_52 : fetchRel trustedRootValidForCode 0x52 = some (.lui a3 (img% hi20 (svOidEcPublicKeyAddress + 0xC)), 4) := by decide
theorem tvf_at_56 : fetchRel trustedRootValidForCode 0x56 = some (.aluImm .add a3 a3 (img% lo12 (svOidEcPublicKeyAddress + 0xC)), 4) := by decide
theorem tvf_at_5a : fetchRel trustedRootValidForCode 0x5A = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem tvf_at_5c : fetchRel trustedRootValidForCode 0x5C = some (.aluImm .add a4 x0 0x3, 2) := by decide
theorem tvf_at_5e : fetchRel trustedRootValidForCode 0x5E = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem tvf_at_60 : fetchRel trustedRootValidForCode 0x60 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem tvf_at_62 : fetchRel trustedRootValidForCode 0x62 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem tvf_at_66 : fetchRel trustedRootValidForCode 0x66 = some (.jalr ra ra 0xFFFFFA2E, 4) := by decide
theorem tvf_at_6a : fetchRel trustedRootValidForCode 0x6A = some (.load .lbu a0 sp 0x10, 4) := by decide
theorem tvf_at_6e : fetchRel trustedRootValidForCode 0x6E = some (.branch .beq a0 x0 0xE, 2) := by decide
theorem tvf_at_70 : fetchRel trustedRootValidForCode 0x70 = some (.load .lbu a0 sp 0x11, 4) := by decide
theorem tvf_at_74 : fetchRel trustedRootValidForCode 0x74 = some (.jal x0 0x38, 2) := by decide
theorem tvf_at_76 : fetchRel trustedRootValidForCode 0x76 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem tvf_at_7a : fetchRel trustedRootValidForCode 0x7A = some (.jal x0 0x32, 2) := by decide
theorem tvf_at_7c : fetchRel trustedRootValidForCode 0x7C = some (.load .lw a1 sp 0x14, 2) := by decide
theorem tvf_at_7e : fetchRel trustedRootValidForCode 0x7E = some (.branch .beq a1 x0 0x48, 2) := by decide
theorem tvf_at_80 : fetchRel trustedRootValidForCode 0x80 = some (.load .lw a2 sp 0x18, 2) := by decide
theorem tvf_at_82 : fetchRel trustedRootValidForCode 0x82 = some (.aluImm .add a0 sp 0x20, 2) := by decide
theorem tvf_at_84 : fetchRel trustedRootValidForCode 0x84 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem tvf_at_88 : fetchRel trustedRootValidForCode 0x88 = some (.jalr ra ra 0xFFFFF8DC, 4) := by decide
theorem tvf_at_8c : fetchRel trustedRootValidForCode 0x8C = some (.load .lw a1 sp 0x20, 2) := by decide
theorem tvf_at_8e : fetchRel trustedRootValidForCode 0x8E = some (.branch .beq a1 x0 0x1A, 2) := by decide
theorem tvf_at_90 : fetchRel trustedRootValidForCode 0x90 = some (.load .lw a2 sp 0x24, 2) := by decide
theorem tvf_at_92 : fetchRel trustedRootValidForCode 0x92 = some (.aluImm .add a0 sp 0x10, 2) := by decide
theorem tvf_at_94 : fetchRel trustedRootValidForCode 0x94 = some (.auipc ra 0x0, 4) := by decide
theorem tvf_at_98 : fetchRel trustedRootValidForCode 0x98 = some (.jalr ra ra 0xBC, 4) := by decide
theorem tvf_at_9c : fetchRel trustedRootValidForCode 0x9C = some (.load .lbu a0 sp 0x10, 4) := by decide
theorem tvf_at_a0 : fetchRel trustedRootValidForCode 0xA0 = some (.branch .bne a0 x0 0xFFFFFFD0, 2) := by decide
theorem tvf_at_a2 : fetchRel trustedRootValidForCode 0xA2 = some (.load .lw a0 sp 0x18, 2) := by decide
theorem tvf_at_a4 : fetchRel trustedRootValidForCode 0xA4 = some (.load .lw a1 sp 0x1C, 2) := by decide
theorem tvf_at_a6 : fetchRel trustedRootValidForCode 0xA6 = some (.jal x0 0x24, 2) := by decide
theorem tvf_at_a8 : fetchRel trustedRootValidForCode 0xA8 = some (.load .lbu a0 sp 0x24, 4) := by decide
theorem tvf_at_ac : fetchRel trustedRootValidForCode 0xAC = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem tvf_at_ae : fetchRel trustedRootValidForCode 0xAE = some (.store .sb (18 : Fin 32) a1 0x0, 4) := by decide
theorem tvf_at_b2 : fetchRel trustedRootValidForCode 0xB2 = some (.store .sb (18 : Fin 32) a0 0x1, 4) := by decide
theorem tvf_at_b6 : fetchRel trustedRootValidForCode 0xB6 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem tvf_at_b8 : fetchRel trustedRootValidForCode 0xB8 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem tvf_at_ba : fetchRel trustedRootValidForCode 0xBA = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem tvf_at_bc : fetchRel trustedRootValidForCode 0xBC = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem tvf_at_be : fetchRel trustedRootValidForCode 0xBE = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem tvf_at_c0 : fetchRel trustedRootValidForCode 0xC0 = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem tvf_at_c2 : fetchRel trustedRootValidForCode 0xC2 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem tvf_at_c4 : fetchRel trustedRootValidForCode 0xC4 = some (.jalr x0 ra 0x0, 2) := by decide
theorem tvf_at_c6 : fetchRel trustedRootValidForCode 0xC6 = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem tvf_at_c8 : fetchRel trustedRootValidForCode 0xC8 = some (.aluImm .add a1 x0 0xFFFFFFFF, 2) := by decide
theorem tvf_at_ca : fetchRel trustedRootValidForCode 0xCA = some (.store .sb (18 : Fin 32) x0 0x0, 4) := by decide
theorem tvf_at_ce : fetchRel trustedRootValidForCode 0xCE = some (.store .sw (18 : Fin 32) (19 : Fin 32) 0x8, 4) := by decide
theorem tvf_at_d2 : fetchRel trustedRootValidForCode 0xD2 = some (.store .sw (18 : Fin 32) (20 : Fin 32) 0xC, 4) := by decide
theorem tvf_at_d6 : fetchRel trustedRootValidForCode 0xD6 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem tvf_at_d8 : fetchRel trustedRootValidForCode 0xD8 = some (.store .sw a2 a0 0x10, 2) := by decide
theorem tvf_at_da : fetchRel trustedRootValidForCode 0xDA = some (.store .sw a2 a1 0x14, 2) := by decide
theorem tvf_at_dc : fetchRel trustedRootValidForCode 0xDC = some (.jal x0 0xFFFFFFDA, 2) := by decide

/-- The contents of the JSON string whose source is `v`, as `Value::str`
reads them: without the quotes, and with escapes left as they are. -/
def tvfStr (v : Bytes) : Option Bytes :=
  if v.length < 2 then none
  else if v.getD 0 0 ≠ 34 then none
  else if v.getD (v.length - 1) 0 ≠ 34 then none
  else some ((v.drop 1).take (v.length - 2))

/-- The time in the JSON string whose source is `v`, or the error byte:
`0x21` (`Schema`) for a value that isn't a string, and `0x19` for a string
that isn't an RFC 3339 time. -/
def tvfTime (v : Bytes) : Except Nat Nat :=
  match tvfStr v with
  | none => .error 0x21
  | some s => match rfc3339 s with
    | none => .error 0x19
    | some t => .ok t

/-- The `x.2` bytes at offset `x.1` of `d`. -/
def tvfSlice (d : Bytes) (x : Nat × Nat) : Bytes := (d.drop x.1).take x.2

/-- The rest of `valid_for` after it reads `not_before = t`: the `end`
member, if any. -/
def tvfRest (d : Bytes) (t : Nat) : Except Nat (Nat × Nat) :=
  match objGet d (ascii!"end") with
  | .error e => .error e
  | .ok none => .ok (t, 2 ^ 64 - 1)
  | .ok (some y) => match tvfTime (tvfSlice d y) with
    | .error e => .error e
    | .ok u => .ok (t, u)

/-- `valid_for` on the object whose bytes are `d`: the window's
`not_before` and `not_after`, or the error byte. -/
def validForPos (d : Bytes) : Except Nat (Nat × Nat) :=
  match objField d (ascii!"start") with
  | .error e => .error e
  | .ok x => match tvfTime (tvfSlice d x) with
    | .error e => .error e
    | .ok t => tvfRest d t

/-- `Result<Window, TufError>` at `out`: the tag byte 0 and the two `u64`s
at `out + 8` and `out + 0x10`, or the tag byte 1 and the error byte. -/
def TvfOut (M : Word → BitVec 8) (out : Word) : Except Nat (Nat × Nat) → Prop
  | .error e => M out = 1 ∧ M (out + 1) = BitVec.ofNat 8 e
  | .ok (t, u) => M out = 0 ∧ memLoad32 M (out + 8) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
      memLoad32 M (out + 0xC) = BitVec.ofNat 32 (t / 2 ^ 32) ∧
      memLoad32 M (out + 0x10) = BitVec.ofNat 32 (u % 2 ^ 32) ∧
      memLoad32 M (out + 0x14) = BitVec.ofNat 32 (u / 2 ^ 32)

/-- The memory part of `valid_for`'s postcondition: `r` at `out`, and no
change outside the stack region `[G, G + 0x144)` and the 0x18 bytes at
`out`. -/
def tvfMem (M0 : Word → BitVec 8) (G out : Word) (r : Except Nat (Nat × Nat)) (M : Word → BitVec 8) : Prop :=
  TvfOut M out r ∧ ∀ x, Sep G 0x144 x 1 → Sep out 0x18 x 1 → M x = M0 x

/-- `valid_for` and the functions it calls. `Value::get` is at
`TJF + 0x16C`, in `FieldCode`. -/
structure TvfCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M TVF trustedRootValidForCode
  field : FieldCode M TJF
  str : CodeIn M TJS jsonStrCode
  rfc : CodeIn M RFC timeRfc3339Code
  dt : CodeIn M DT dateTimeCode
  td : CodeIn M TD timeDigits2Code
  td4 : CodeIn M TD4 timeDigits4Code
  aad : CodeIn M AAD allAsciiDigitCode

set_option maxRecDepth 20000 in
/-- A region below `0x40000000` and apart from the read-only window is
apart from `Value::get` and its callees. -/
theorem tvf_getSep {G : Word} {k : Nat} (hw : G.toNat + k ≤ 0x40000000) (hro : Sep G k TVF_RO 0x1400) :
    GetSep G k (TJF + 0x16C) :=
  ⟨lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
    lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
    lowSep hw (by decide) (by decide),
    ⟨lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
      lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
      lowSep hw (by decide) (by decide), hro.subR (c := 0x766) (l := 8) (by decide),
      hro.subR (c := 0x8F2) (l := 5) (by decide)⟩⟩

theorem tvf_fieldSep {G : Word} {k : Nat} (hw : G.toNat + k ≤ 0x40000000) (hro : Sep G k TVF_RO 0x1400) :
    FieldSep G k TJF :=
  ⟨lowSep hw (by decide) (by decide), tvf_getSep hw hro⟩

set_option maxRecDepth 20000 in
theorem TvfCode.out {M M' : Word → BitVec 8} {G : Word} {k : Nat} (C : TvfCode M) (hO : Out M M' G k)
    (hw : G.toNat + k ≤ 0x40000000) (hro : Sep G k TVF_RO 0x1400) : TvfCode M' :=
  ⟨hO.codeIn C.self (lowSep hw (by decide) (by decide)),
    ⟨hO.codeIn C.field.field (lowSep hw (by decide) (by decide)), C.field.get.out hO (tvf_getSep hw hro)⟩,
    hO.codeIn C.str (lowSep hw (by decide) (by decide)), hO.codeIn C.rfc (lowSep hw (by decide) (by decide)),
    hO.codeIn C.dt (lowSep hw (by decide) (by decide)), hO.codeIn C.td (lowSep hw (by decide) (by decide)),
    hO.codeIn C.td4 (lowSep hw (by decide) (by decide)), hO.codeIn C.aad (lowSep hw (by decide) (by decide))⟩

theorem tvf_saved_cases : ∀ q : Fin 32, q.val ∈ trSaved →
    q = ra ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] := by decide

theorem tvf_rest_cases : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] →
    q = 3 ∨ q = 4 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨ q = 25 ∨ q = 26 ∨ q = 27 := by decide

section
variable {F : Word} {f g0 : Fin 32 → Word}

/-- The epilogue at 0xB6: restores `ra`, `s0`–`s4` from the frame at `F`
and returns. -/
theorem tvf_epi {R : (Word → BitVec 8) → Prop} {Mf : Word → BitVec 8} (hsp : f sp = F)
    (e1 : memLoad32 Mf (F + 0x3C) = g0 ra) (e2 : memLoad32 Mf (F + 0x38) = g0 8)
    (e3 : memLoad32 Mf (F + 0x34) = g0 9) (e4 : memLoad32 Mf (F + 0x30) = g0 18)
    (e5 : memLoad32 Mf (F + 0x2C) = g0 19) (e6 : memLoad32 Mf (F + 0x28) = g0 20)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (hfr : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → f q = g0 q) (hR : R Mf) :
    WP trustedRootValidForCode TVF (trPost R g0) Mf 0xB6 f := by
  refine WP.lw tvf_at_b6 (by rw [hsp]; exact aligned_add hal (k := 0x3C) (by decide)) ?_; wn
  refine WP.lw tvf_at_b8 (by trsimp; rw [hsp]; exact aligned_add hal (k := 0x38) (by decide)) ?_; wn
  refine WP.lw tvf_at_ba (by trsimp; rw [hsp]; exact aligned_add hal (k := 0x34) (by decide)) ?_; wn
  refine WP.lw tvf_at_bc (by trsimp; rw [hsp]; exact aligned_add hal (k := 0x30) (by decide)) ?_; wn
  refine WP.lw tvf_at_be (by trsimp; rw [hsp]; exact aligned_add hal (k := 0x2C) (by decide)) ?_; wn
  refine WP.lw tvf_at_c0 (by trsimp; rw [hsp]; exact aligned_add hal (k := 0x28) (by decide)) ?_; wn
  refine WP.aluImm tvf_at_c2 ?_; wn
  refine WP.ret tvf_at_c4 ⟨?_, ?_, fun q hq => ?_, hR⟩
  · trsimp; rw [hsp, e1, add_lit_zero, hret]
  · trsimp; rw [hsp, hsp0]; rfl
  · rcases tvf_saved_cases q hq with rfl | rfl | rfl | rfl | rfl | rfl | h
    · trsimp; rw [hsp, e1]
    · trsimp; rw [hsp, e2]
    · trsimp; rw [hsp, e3]
    · trsimp; rw [hsp, e4]
    · trsimp; rw [hsp, e5]
    · trsimp; rw [hsp, e6]
    · have hn : q ≠ ra ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 18 ∧ q ≠ 19 ∧ q ≠ 20 ∧ q ≠ sp ∧ q.val ≠ 0 := by
        revert q; decide
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := hn
      simp only [upd_app, n1, n2, n3, n4, n5, n6, n7, n8, ↓reduceIte]
      exact hfr q h

end

/-- The two bytes of an `Err` at `out`. -/
theorem tvf_errMem (M : Word → BitVec 8) (out : Word) (b : BitVec 8) :
    Out M (memStore8 (memStore8 M out 1) (out + 1) b) out 0x18 ∧
      memStore8 (memStore8 M out 1) (out + 1) b out = 1 ∧
      memStore8 (memStore8 M out 1) (out + 1) b (out + 1) = b := by
  have h01 : Sep out 1 (out + 1) 1 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 1) (k := 1) (Or.inl (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨((out_store8 _ _ _).mono (by decide)).trans (Out.upK (c := 1) rfl (out_store8 _ _ _) (by decide)),
    ?_, memStore8_same _ _ _⟩
  rw [out_store8 _ _ _ out h01, memStore8_same]

/-- The 0x18 bytes of an `Ok` at `out`. -/
theorem tvf_okMem (M : Word → BitVec 8) (out a b c d : Word) :
    Out M (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 M out 0) (out + 8) a) (out + 0xC) b)
      (out + 0x10) c) (out + 0x14) d) out 0x18 ∧
    memStore32 (memStore32 (memStore32 (memStore32 (memStore8 M out 0) (out + 8) a) (out + 0xC) b)
      (out + 0x10) c) (out + 0x14) d out = 0 ∧
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 M out 0) (out + 8) a) (out + 0xC) b)
      (out + 0x10) c) (out + 0x14) d) (out + 8) = a ∧
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 M out 0) (out + 8) a) (out + 0xC) b)
      (out + 0x10) c) (out + 0x14) d) (out + 0xC) = b ∧
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 M out 0) (out + 8) a) (out + 0xC) b)
      (out + 0x10) c) (out + 0x14) d) (out + 0x10) = c ∧
    memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore8 M out 0) (out + 8) a) (out + 0xC) b)
      (out + 0x10) c) (out + 0x14) d) (out + 0x14) = d := by
  have s0 : ∀ d : Nat, 1 ≤ d → d + 4 ≤ 0x18 → Sep out 1 (out + BitVec.ofNat 32 d) 4 := fun d h1 h2 => by
    have := sep_offsets out (c := 0) (n := 1) (d := d) (k := 4) (Or.inl (by omega)) (by decide) (by omega)
    rwa [add_ofNat_zero] at this
  have sw : ∀ c d : Nat, c + 4 ≤ d → d + 4 ≤ 0x18 →
      Sep (out + BitVec.ofNat 32 d) 4 (out + BitVec.ofNat 32 c) 4 := fun c d h1 h2 =>
    sep_offsets out (Or.inr h1) (by omega) (by omega)
  have a8 : Sep out 1 (out + 8) 4 := s0 8 (by decide) (by decide)
  have aC : Sep out 1 (out + 0xC) 4 := s0 0xC (by decide) (by decide)
  have a10 : Sep out 1 (out + 0x10) 4 := s0 0x10 (by decide) (by decide)
  have a14 : Sep out 1 (out + 0x14) 4 := s0 0x14 (by decide) (by decide)
  have w8C : Sep (out + 0xC) 4 (out + 8) 4 := sw 8 0xC (by decide) (by decide)
  have w810 : Sep (out + 0x10) 4 (out + 8) 4 := sw 8 0x10 (by decide) (by decide)
  have w814 : Sep (out + 0x14) 4 (out + 8) 4 := sw 8 0x14 (by decide) (by decide)
  have wC10 : Sep (out + 0x10) 4 (out + 0xC) 4 := sw 0xC 0x10 (by decide) (by decide)
  have wC14 : Sep (out + 0x14) 4 (out + 0xC) 4 := sw 0xC 0x14 (by decide) (by decide)
  have w1014 : Sep (out + 0x14) 4 (out + 0x10) 4 := sw 0x10 0x14 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩
  · exact (((((out_store8 _ _ _).mono (by decide)).trans (Out.upK (c := 8) rfl (out_store32 _ _ _) (by decide))).trans
      (Out.upK (c := 0xC) rfl (out_store32 _ _ _) (by decide))).trans
      (Out.upK (c := 0x10) rfl (out_store32 _ _ _) (by decide))).trans
      (Out.upK (c := 0x14) rfl (out_store32 _ _ _) (by decide))
  · rw [out_store32 _ _ _ out a14, out_store32 _ _ _ out a10, out_store32 _ _ _ out aC, out_store32 _ _ _ out a8,
      memStore8_same]
  · rw [memLoad32_store32_sep w814, memLoad32_store32_sep w810, memLoad32_store32_sep w8C, memLoad32_store32_same]
  · rw [memLoad32_store32_sep wC14, memLoad32_store32_sep wC10, memLoad32_store32_same]
  · rw [memLoad32_store32_sep w1014, memLoad32_store32_same]

/-- The facts about `valid_for`'s entry that every block of its proof uses.
`G` is the bottom of the stack that it and its callees use, `F` its frame,
`p` and `n` the object's bytes, and `g0` the registers at entry. -/
structure TvfCtx (M0 : Word → BitVec 8) (G F out p : Word) (n : Nat) (g0 : Fin 32 → Word) : Prop where
  code : TvfCode M0
  fg : G + BitVec.ofNat 32 0x104 = F
  ga : G.toNat % 4 = 0
  gw : G.toNat + 0x144 ≤ 0x40000000
  oa : out.toNat % 4 = 0
  ow : out.toNat + 0x18 ≤ 0x40000000
  og : Sep out 0x18 G 0x144
  pw : p.toNat + n + 4 ≤ 0x40000000
  p0 : p.toNat ≠ 0
  pg : Sep p (n + 4) G 0x144
  ro : Sep G 0x144 TVF_RO 0x1400
  ks : memBytes M0 tvfStartKey 5 = ascii!"start"
  ke : memBytes M0 tvfEndKey 3 = ascii!"end"
  sp0 : g0 sp = F + BitVec.ofNat 32 0x40
  ret : g0 ra &&& ~~~1 = g0 ra

/-- The registers that `valid_for` keeps from its prologue to its
epilogue. -/
def TvfRegs (F out p : Word) (n : Nat) (g0 f : Fin 32 → Word) : Prop :=
  f 0 = 0 ∧ f sp = F ∧ f 8 = p ∧ f 9 = BitVec.ofNat 32 n ∧ f 18 = out ∧
    ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → f q = g0 q

/-- The memory between the prologue and the epilogue: changed only in
`[G, G + 0x144)`, with the saved registers in the frame. -/
def TvfMemInv (M0 : Word → BitVec 8) (G F : Word) (g0 : Fin 32 → Word) (M : Word → BitVec 8) : Prop :=
  Out M0 M G 0x144 ∧ memLoad32 M (F + 0x3C) = g0 ra ∧ memLoad32 M (F + 0x38) = g0 8 ∧
    memLoad32 M (F + 0x34) = g0 9 ∧ memLoad32 M (F + 0x30) = g0 18 ∧ memLoad32 M (F + 0x2C) = g0 19 ∧
    memLoad32 M (F + 0x28) = g0 20

theorem tvf_rest_ne : ∀ q rd : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] →
    rd.val ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 28, 29, 30, 31] → q.val ≠ 0 ∧ q ≠ rd := by decide

theorem tvf_rest_nc : ∀ q : Fin 32, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → q ∉ jClob := by decide

/-- A write to a register that `valid_for` doesn't keep. -/
theorem TvfRegs.set {F out p : Word} {n : Nat} {g0 f : Fin 32 → Word} {rd : Fin 32} {v : Word}
    (h : TvfRegs F out p n g0 f) (hr : rd.val ∈ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 28, 29, 30, 31]) :
    TvfRegs F out p n g0 (upd f rd v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have ne : ∀ q : Fin 32, q.val ∈ [2, 8, 9, 18] → q.val ≠ 0 ∧ q ≠ rd := by
    revert hr; revert rd; decide
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [upd_app, ite_eq_right (ne sp (by decide)).1, ite_eq_right (ne sp (by decide)).2, h1]
  · rw [upd_app, ite_eq_right (ne 8 (by decide)).1, ite_eq_right (ne 8 (by decide)).2, h2]
  · rw [upd_app, ite_eq_right (ne 9 (by decide)).1, ite_eq_right (ne 9 (by decide)).2, h3]
  · rw [upd_app, ite_eq_right (ne 18 (by decide)).1, ite_eq_right (ne 18 (by decide)).2, h4]
  · rw [upd_app, ite_eq_right (tvf_rest_ne q rd hq hr).1, ite_eq_right (tvf_rest_ne q rd hq hr).2, h5 q hq]

/-- The registers after a call that keeps everything outside `jClob`. -/
theorem TvfRegs.clob {F out p : Word} {n : Nat} {g0 f : Fin 32 → Word} {m : Machine} {v : Word}
    (h : TvfRegs F out p n g0 f) : TvfRegs F out p n g0 (clob (upd f ra v) m jClob) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h.set (rd := ra) (v := v) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [clob_app, ite_eq_right (by decide), h0]
  · rw [clob_app, ite_eq_right (by decide), h1]
  · rw [clob_app, ite_eq_right (by decide), h2]
  · rw [clob_app, ite_eq_right (by decide), h3]
  · rw [clob_app, ite_eq_right (by decide), h4]
  · rw [clob_app, ite_eq_right (tvf_rest_nc q hq), h5 q hq]

/-- Proves `TvfRegs` of a register file that `upd` builds from one that
`hR` covers. -/
macro "tvf_regs " h:term : tactic => `(tactic| (
  repeat (refine TvfRegs.set ?_ (by decide))
  first | exact $h | exact TvfRegs.clob $h))

section
variable {M0 : Word → BitVec 8} {G F out p : Word} {n : Nat} {g0 : Fin 32 → Word}

theorem TvfCtx.fG (X : TvfCtx M0 G F out p n g0) (c : Nat) :
    F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x104 + c) := by
  rw [← X.fg, add_ofNat_assoc]

theorem TvfCtx.gc (X : TvfCtx M0 G F out p n g0) {c : Nat} (hc : c ≤ 0x144) :
    (G + BitVec.ofNat 32 c).toNat = G.toNat + c := by
  have := X.gw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem TvfCtx.fn (X : TvfCtx M0 G F out p n g0) : F.toNat = G.toNat + 0x104 := by
  rw [← X.fg]; exact X.gc (by decide)

theorem TvfCtx.fa (X : TvfCtx M0 G F out p n g0) : F.toNat % 4 = 0 := by
  have := X.fn; have := X.ga; omega

theorem TvfCtx.flo (X : TvfCtx M0 G F out p n g0) {c k : Nat} (h : 0x104 + c + k ≤ 0x144) :
    Sep (F + BitVec.ofNat 32 c) k TVF trustedRootValidForCode.length :=
  tr_lowAt (by have := X.fn; have := X.gw; omega) (by decide) (by decide)

theorem TvfCtx.olo (X : TvfCtx M0 G F out p n g0) {c k : Nat} (h : c + k ≤ 0x18) :
    Sep (out + BitVec.ofNat 32 c) k TVF trustedRootValidForCode.length :=
  tr_lowAt (by have := X.ow; omega) (by decide) (by decide)

/-- The frame's word at `F + d` doesn't change when only the `l` bytes at
`G + c` do, for a range below the saved registers. -/
theorem TvfCtx.slot (X : TvfCtx M0 G F out p n g0) {M M' : Word → BitVec 8} {c l : Nat}
    (h : Out M M' (G + BitVec.ofNat 32 c) l) (hc : c + l ≤ 0x12C) (d : Nat) (hd1 : 0x28 ≤ d) (hd2 : d + 4 ≤ 0x40) :
    memLoad32 M' (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d) := by
  rw [X.fG]
  exact Out.load32 h (sep_offsets G (Or.inl (by omega)) (by omega) (by omega))

theorem TvfMemInv.step (X : TvfCtx M0 G F out p n g0) {M M' : Word → BitVec 8} {c l : Nat}
    (I : TvfMemInv M0 G F g0 M) (h : Out M M' (G + BitVec.ofNat 32 c) l) (hc : c + l ≤ 0x12C) :
    TvfMemInv M0 G F g0 M' :=
  ⟨fun x hx => (h x (sep_in hx (by omega))).trans (I.1 x hx),
    (X.slot h hc 0x3C (by decide) (by decide)).trans I.2.1,
    (X.slot h hc 0x38 (by decide) (by decide)).trans I.2.2.1,
    (X.slot h hc 0x34 (by decide) (by decide)).trans I.2.2.2.1,
    (X.slot h hc 0x30 (by decide) (by decide)).trans I.2.2.2.2.1,
    (X.slot h hc 0x2C (by decide) (by decide)).trans I.2.2.2.2.2.1,
    (X.slot h hc 0x28 (by decide) (by decide)).trans I.2.2.2.2.2.2⟩

/-- A write of the 0x18 bytes at `out` leaves the frame's saved words. -/
theorem TvfCtx.slotOut (X : TvfCtx M0 G F out p n g0) {M M' : Word → BitVec 8} (h : Out M M' out 0x18)
    (d : Nat) (hd : d + 4 ≤ 0x40) :
    memLoad32 M' (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d) := by
  rw [X.fG]; exact Out.load32 h (X.og.subR (by omega))

/-- The return through the epilogue, after `out` holds the result. -/
theorem TvfCtx.exit (X : TvfCtx M0 G F out p n g0) {M Mf : Word → BitVec 8} {f : Fin 32 → Word}
    {r : Except Nat (Nat × Nat)} (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (hO : Out M Mf out 0x18) (hr : TvfOut Mf out r) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) Mf 0xB6 f := by
  obtain ⟨-, r1, -, -, -, r5⟩ := hR
  exact tvf_epi r1 ((X.slotOut hO 0x3C (by decide)).trans hI.2.1) ((X.slotOut hO 0x38 (by decide)).trans hI.2.2.1)
    ((X.slotOut hO 0x34 (by decide)).trans hI.2.2.2.1) ((X.slotOut hO 0x30 (by decide)).trans hI.2.2.2.2.1)
    ((X.slotOut hO 0x2C (by decide)).trans hI.2.2.2.2.2.1) ((X.slotOut hO 0x28 (by decide)).trans hI.2.2.2.2.2.2)
    X.sp0 X.ret X.fa r5 ⟨hr, fun x sG sO => (hO x sO.symm).trans (hI.1 x sG.symm)⟩

/-- The `Err` writer at 0xAC, with the error byte in `a0`. -/
theorem TvfCtx.errAC (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {e : Nat}
    {r : Except Nat (Nat × Nat)} (hr : r = .error e) (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (ha0 : f a0 = (BitVec.ofNat 8 e).zeroExtend 32) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) M 0xAC f := by
  have r4 := hR.2.2.2.2.1
  have rz : f x0 = 0 := hR.1
  refine WP.aluImm tvf_at_ac ?_; wn
  refine WP.sb tvf_at_ae (by trsimp; rw [r4]; exact X.olo (c := 0) (by decide)) ?_; wn
  refine WP.sb tvf_at_b2 (by trsimp; rw [r4]; exact X.olo (c := 1) (by decide)) ?_; wn
  simp only [rz, ev0, r4, add_lit_zero, ha0, ri_ze]
  rw [show BitVec.extractLsb' 0 8 (1 : Word) = (1 : BitVec 8) from rfl]
  obtain ⟨hO, h0, h1⟩ := tvf_errMem M out (BitVec.ofNat 8 e)
  refine X.exit (by tvf_regs hR) hI hO ?_
  rw [hr]; exact ⟨h0, h1⟩

/-- The error path at 0x70: the error byte of a result at `F + 0x10`. -/
theorem TvfCtx.err70 (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {e : Nat}
    {r : Except Nat (Nat × Nat)} (hr : r = .error e) (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (hb : M (F + 0x11) = BitVec.ofNat 8 e) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) M 0x70 f := by
  refine WP.lbu tvf_at_70 ?_; wn
  refine WP.jal tvf_at_74 (by decide) ?_; wn
  exact X.errAC hr (by tvf_regs hR) hI (by trsimp; rw [hR.2.1, hb])

/-- The error path at 0xA8: the error byte of a result at `F + 0x20`. -/
theorem TvfCtx.errA8 (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {e : Nat}
    {r : Except Nat (Nat × Nat)} (hr : r = .error e) (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (hb : M (F + 0x24) = BitVec.ofNat 8 e) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) M 0xA8 f := by
  refine WP.lbu tvf_at_a8 ?_; wn
  exact X.errAC hr (by tvf_regs hR) hI (by trsimp; rw [hR.2.1, hb])

/-- The error path at 0x76: the error byte of a result at `F + 8`. -/
theorem TvfCtx.err76 (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {e : Nat}
    {r : Except Nat (Nat × Nat)} (hr : r = .error e) (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (hb : M (F + 0xC) = BitVec.ofNat 8 e) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) M 0x76 f := by
  refine WP.lbu tvf_at_76 ?_; wn
  refine WP.jal tvf_at_7a (by decide) ?_; wn
  exact X.errAC hr (by tvf_regs hR) hI (by trsimp; rw [hR.2.1, hb])

/-- The `Ok` writer at 0xCA, with `not_before` in `s3`/`s4` and `not_after`
in `a0`/`a1`. -/
theorem TvfCtx.okCA (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {t u : Nat}
    {r : Except Nat (Nat × Nat)} (hr : r = .ok (t, u)) (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (h19 : f 19 = BitVec.ofNat 32 (t % 2 ^ 32)) (h20 : f 20 = BitVec.ofNat 32 (t / 2 ^ 32))
    (ha0 : f a0 = BitVec.ofNat 32 (u % 2 ^ 32)) (ha1 : f a1 = BitVec.ofNat 32 (u / 2 ^ 32)) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) M 0xCA f := by
  have r0 : f x0 = 0 := hR.1
  have r4 := hR.2.2.2.2.1
  refine WP.sb tvf_at_ca (by rw [r4]; exact X.olo (c := 0) (by decide)) ?_; wn
  refine WP.sw tvf_at_ce (by rw [r4]; exact aligned_add X.oa (k := 8) (by decide))
    (by rw [r4]; exact X.olo (c := 8) (by decide)) ?_; wn
  refine WP.sw tvf_at_d2 (by rw [r4]; exact aligned_add X.oa (k := 0xC) (by decide))
    (by rw [r4]; exact X.olo (c := 0xC) (by decide)) ?_; wn
  refine WP.alu tvf_at_d6 ?_; wn
  refine WP.sw tvf_at_d8 (by trsimp; rw [r0, ev0, r4]; exact aligned_add X.oa (k := 0x10) (by decide))
    (by trsimp; rw [r0, ev0, r4]; exact X.olo (c := 0x10) (by decide)) ?_; wn
  refine WP.sw tvf_at_da (by trsimp; rw [r0, ev0, r4]; exact aligned_add X.oa (k := 0x14) (by decide))
    (by trsimp; rw [r0, ev0, r4]; exact X.olo (c := 0x14) (by decide)) ?_; wn
  refine WP.jal tvf_at_dc (by decide) ?_; wn
  simp only [r0, ev0, r4, add_lit_zero, h19, h20, ha0, ha1]
  rw [show BitVec.extractLsb' 0 8 (0 : Word) = (0 : BitVec 8) from rfl]
  obtain ⟨hO, e0, e1, e2, e3, e4⟩ := tvf_okMem M out (BitVec.ofNat 32 (t % 2 ^ 32)) (BitVec.ofNat 32 (t / 2 ^ 32))
    (BitVec.ofNat 32 (u % 2 ^ 32)) (BitVec.ofNat 32 (u / 2 ^ 32))
  refine X.exit (by tvf_regs hR) hI hO ?_
  rw [hr]; exact ⟨e0, e1, e2, e3, e4⟩

/-- The path at 0xC6 for an object without `end`: `not_after` is
`u64::MAX`. -/
theorem TvfCtx.noneC6 (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {t : Nat}
    {r : Except Nat (Nat × Nat)} (hr : r = .ok (t, 2 ^ 64 - 1)) (hR : TvfRegs F out p n g0 f)
    (hI : TvfMemInv M0 G F g0 M) (h19 : f 19 = BitVec.ofNat 32 (t % 2 ^ 32))
    (h20 : f 20 = BitVec.ofNat 32 (t / 2 ^ 32)) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) M 0xC6 f := by
  refine WP.aluImm tvf_at_c6 ?_; wn
  refine WP.aluImm tvf_at_c8 ?_; wn
  exact X.okCA hr (by tvf_regs hR) hI (by trsimp; exact h19) (by trsimp; exact h20)
    (by trsimp <;> rw [show f x0 = 0 from hR.1] <;> decide) (by trsimp <;> rw [show f x0 = 0 from hR.1] <;> decide)

end

theorem tvf_saved_nc : ∀ q : Fin 32, q.val ∈ trSaved → q ∉ jClob := by decide

theorem tvf_saved_ns : ∀ q : Fin 32, q.val ∈ trSaved → q ∉ strClob := by decide

/-- A memory that changes only in a range below `0x40000000` keeps the
code. -/
theorem tvf_hiOut {M M' : Word → BitVec 8} {a : Word} {k : Nat} (h : Out M M' a k) (ha : a.toNat + k ≤ 0x40000000) :
    ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x :=
  fun x hx => h x (lowSep ha hx (by have := x.isLt; omega)).symm

section
variable {M0 : Word → BitVec 8} {G F out p : Word} {n : Nat} {g0 : Fin 32 → Word}

theorem TvfCtx.fGc (X : TvfCtx M0 G F out p n g0) (c d : Nat) (h : 0x104 + c = d) :
    F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 d := by
  rw [X.fG, h]

theorem TvfCtx.keyS (X : TvfCtx M0 G F out p n g0) : Sep G 0x144 tvfStartKey 5 :=
  X.ro.subR (c := img% svOidEcPublicKeyAddress + 0x7 - roWindowAddress) (by decide)

theorem TvfCtx.keyE (X : TvfCtx M0 G F out p n g0) : Sep G 0x144 tvfEndKey 3 :=
  X.ro.subR (c := img% svOidEcPublicKeyAddress + 0xC - roWindowAddress) (by decide)

/-- The call of `Value::field` at 0x20, for the key `start`, with the
result at `F + 0x20`. -/
theorem TvfCtx.callField (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {Q : Post}
    (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M) (ha0 : f a0 = F + 0x20) (ha1 : f a1 = p)
    (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = tvfStartKey) (ha4 : f a4 = BitVec.ofNat 32 5)
    (k : ∀ (M1 M' : Word → BitVec 8) (f' : Fin 32 → Word), TvfRegs F out p n g0 f' → TvfMemInv M0 G F g0 M' →
      FieldRes M1 M' (F + 0x20) (fieldRes p (objField (memBytes M0 p n) (ascii!"start"))) → f' 19 = f 19 → f' 20 = f 20 →
      WP trustedRootValidForCode TVF Q M' 0x28 f') :
    WP trustedRootValidForCode TVF Q M 0x20 f := by
  have C := X.code.out hI.1 X.gw X.ro
  have gw := X.gw
  have pw := X.pw
  have e20 : F + 0x20 = G + BitVec.ofNat 32 0x124 := X.fGc 0x20 0x124 rfl
  have hd : memBytes M p n = memBytes M0 p n := hI.1.bytes (trSepR X.pg.symm (by omega))
  have hk : memBytes M tvfStartKey 5 = ascii!"start" := (hI.1.bytes X.keyS).trans X.ks
  refine WP.trCallSaved (tb := TJF)
    (P := fun m2 => FieldResF M m2.mem (F + 0x20) G 260 (fieldRes p (objField (memBytes M0 p n) (ascii!"start"))))
    tvf_at_20 tvf_at_24 (by decide) (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP hc => ?_) (fun m2 hP => ?_)
  · obtain ⟨m2, c2, pc2, R, fr⟩ := jsonField_correct m1 (base := TJF) (s := G) (out := F + 0x20) (p := p)
      (kq := tvfStartKey) (n := n) (kl := 5) (retAddr := TVF + BitVec.ofNat 32 (0x20 + 8)) (by decide)
      (by rw [hmem1]; exact C.field) hpc1 (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1)
      (by rw [hreg1]; trsimp; exact ha2) (by rw [hreg1]; trsimp; exact ha3) (by rw [hreg1]; trsimp; exact ha4)
      (by rw [hreg1]; trsimp; rw [hR.2.1, ← X.fg]) (by rw [hreg1]; trsimp) (by decide) X.ga
      (by rw [e20]; exact aligned_add X.ga (by decide)) (by omega) (by decide) X.p0 (by omega)
      (tvf_fieldSep (by omega) (sep_low X.ro (by decide))) (trSepR (sep_low X.pg.symm (by decide)) (by omega))
      (sep_low X.keyS (by decide))
      (by rw [e20]; have := sep_offsets G (c := 0x124) (n := 8) (d := 0) (k := 260) (Or.inr (by decide)) (by decide)
            (by decide); rwa [add_ofNat_zero] at this)
      (by rw [e20]; exact tr_lowAt (by omega) (by decide) (by decide))
    rw [hmem1, hd, hk] at R
    exact ⟨m2, c2, pc2, R, by rw [fr sp (by decide)], fun q hq => fr q (tvf_saved_nc q hq)⟩
  · obtain ⟨M1, hO1, hFR⟩ := hP
    have h1 := tvf_hiOut hO1 (by omega)
    have h2 := tvf_hiOut hFR.out (by rw [e20, X.gc (by decide)]; omega)
    exact hc.hi (fun x hx => (h2 x hx).trans (h1 x hx)) (by decide) (by decide)
  · obtain ⟨M1, hO1, hFR⟩ := hP
    have hO2 := hFR.out
    rw [e20] at hO2
    exact k M1 m2.mem _ hR.clob ((hI.step X (c := 0) (l := 260) (by rw [add_ofNat_zero]; exact hO1) (by decide)).step
      X hO2 (by decide)) hFR (by trsimp) (by trsimp)

/-- The call of `Value::get` at 0x62, for the key `end`, with the result
at `F + 0x10`. -/
theorem TvfCtx.callGet (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {Q : Post}
    (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M) (ha0 : f a0 = F + 0x10) (ha1 : f a1 = p)
    (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = tvfEndKey) (ha4 : f a4 = BitVec.ofNat 32 3)
    (k : ∀ (M1 M' : Word → BitVec 8) (f' : Fin 32 → Word), TvfRegs F out p n g0 f' → TvfMemInv M0 G F g0 M' →
      GetRes M1 M' (F + 0x10) (getRes p (objGet (memBytes M0 p n) (ascii!"end"))) → f' 19 = f 19 → f' 20 = f 20 →
      WP trustedRootValidForCode TVF Q M' 0x6A f') :
    WP trustedRootValidForCode TVF Q M 0x62 f := by
  have C := X.code.out hI.1 X.gw X.ro
  have gw := X.gw
  have pw := X.pw
  have e10 : F + 0x10 = G + BitVec.ofNat 32 0x114 := X.fGc 0x10 0x114 rfl
  have hg : (G + BitVec.ofNat 32 0x20).toNat = G.toNat + 0x20 := X.gc (by decide)
  have hd : memBytes M p n = memBytes M0 p n := hI.1.bytes (trSepR X.pg.symm (by omega))
  have hk : memBytes M tvfEndKey 3 = ascii!"end" := (hI.1.bytes X.keyE).trans X.ke
  refine WP.trCallSaved (tb := TJF + 0x16C)
    (P := fun m2 => GetResF M m2.mem (F + 0x10) (G + BitVec.ofNat 32 0x20) 228
      (getRes p (objGet (memBytes M0 p n) (ascii!"end"))))
    tvf_at_62 tvf_at_66 (by decide) (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP hc => ?_) (fun m2 hP => ?_)
  · obtain ⟨m2, c2, pc2, R, fr⟩ := jsonGet_correct m1 (base := TJF + 0x16C) (s := G + BitVec.ofNat 32 0x20)
      (out := F + 0x10) (p := p) (kq := tvfEndKey) (n := n) (kl := 3) (retAddr := TVF + BitVec.ofNat 32 (0x62 + 8))
      (by decide) (by rw [hmem1]; exact C.field.get) hpc1 (by rw [hreg1]; trsimp; exact ha0)
      (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2) (by rw [hreg1]; trsimp; exact ha3)
      (by rw [hreg1]; trsimp; exact ha4)
      (by rw [hreg1]; trsimp; rw [hR.2.1, add_ofNat_assoc, ← X.fg]) (by rw [hreg1]; trsimp) (by decide)
      (by rw [hg]; have := X.ga; omega) (by rw [e10]; exact aligned_add X.ga (by decide)) (by omega) (by decide)
      X.p0 (by omega)
      (tvf_getSep (by omega) (X.ro.sub (by decide))) (trSepR (X.pg.symm.sub (by decide)) (by omega))
      (X.keyE.sub (by decide))
      (by rw [e10]; exact sep_offsets G (Or.inr (by decide)) (by decide) (by decide))
      (by rw [e10]; exact tr_lowAt (by omega) (by decide) (by decide))
    rw [hmem1, hd, hk] at R
    exact ⟨m2, c2, pc2, R, by rw [fr sp (by decide)], fun q hq => fr q (tvf_saved_nc q hq)⟩
  · obtain ⟨M1, hO1, hGR⟩ := hP
    have h1 := tvf_hiOut hO1 (by omega)
    have h2 := tvf_hiOut hGR.out (by rw [e10, X.gc (by decide)]; omega)
    exact hc.hi (fun x hx => (h2 x hx).trans (h1 x hx)) (by decide) (by decide)
  · obtain ⟨M1, hO1, hGR⟩ := hP
    have hO2 := hGR.out
    rw [e10] at hO2
    exact k M1 m2.mem _ hR.clob ((hI.step X hO1 (by decide)).step X hO2 (by decide)) hGR (by trsimp)
      (by trsimp)

/-- A call of `Value::str` from `valid_for`, with the result at `F + c`. -/
theorem TvfCtx.callStr (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {Q : Post}
    {off c : Nat} {hi lo q : Word} {l : Nat}
    (h1 : fetchRel trustedRootValidForCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootValidForCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TVF + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = TJS)
    (hev : (TVF + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TVF + BitVec.ofNat 32 (off + 8))
    (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M) (hc : c + 8 ≤ 0x28) (hca : c % 4 = 0)
    (ha0 : f a0 = F + BitVec.ofNat 32 c) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 l) (hl : l < 2 ^ 32)
    (k : ∀ (M' : Word → BitVec 8) (f' : Fin 32 → Word), TvfRegs F out p n g0 f' → TvfMemInv M0 G F g0 M' →
      SliceRes M M' (F + BitVec.ofNat 32 c) 0x21 (strRes q (memBytes M q l)) → f' 19 = f 19 → f' 20 = f 20 →
      WP trustedRootValidForCode TVF Q M' (off + 8) f') :
    WP trustedRootValidForCode TVF Q M off f := by
  have C := X.code.out hI.1 X.gw X.ro
  have gw := X.gw
  have ec := X.fG c
  have hgc : (G + BitVec.ofNat 32 (0x104 + c)).toNat = G.toNat + (0x104 + c) := X.gc (by omega)
  refine WP.trCallSaved (tb := TJS)
    (P := fun m2 => SliceRes M m2.mem (F + BitVec.ofNat 32 c) 0x21 (strRes q (memBytes M q l)))
    h1 h2 htgt (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP hcd => ?_) (fun m2 hP => ?_)
  · obtain ⟨m2, c2, pc2, R, fr⟩ := jsonStr_correct m1 (base := TJS) (out := F + BitVec.ofNat 32 c) (p := q) (n := l)
      (retAddr := TVF + BitVec.ofNat 32 (off + 8)) (by decide) (by rw [hmem1]; exact C.str) hpc1
      (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2) hl
      (by rw [ec, hgc]; have := X.ga; omega) (by rw [ec]; exact tr_lowAt (by omega) (by decide) (by decide))
      (by rw [hreg1]; trsimp) hev
    rw [hmem1] at R
    exact ⟨m2, c2, pc2, R, by rw [fr sp (by decide)], fun q hq => fr q (tvf_saved_ns q hq)⟩
  · exact hcd.hi (tvf_hiOut hP.out (by rw [ec, hgc]; omega)) (by decide) (by decide)
  · have hO2 := hP.out
    rw [ec] at hO2
    exact k m2.mem _ hR.clob (hI.step X hO2 (by omega)) hP (by trsimp) (by trsimp)

/-- A call of `time::rfc3339` from `valid_for`, with the result at
`F + 0x10`. -/
theorem TvfCtx.callRfc (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {Q : Post}
    {off : Nat} {hi lo q : Word} {l : Nat}
    (h1 : fetchRel trustedRootValidForCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel trustedRootValidForCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (TVF + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = RFC)
    (hev : (TVF + BitVec.ofNat 32 (off + 8)) &&& ~~~1 = TVF + BitVec.ofNat 32 (off + 8))
    (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (ha0 : f a0 = F + 0x10) (ha1 : f a1 = q) (ha2 : f a2 = BitVec.ofNat 32 l)
    (hqw : q.toNat + l + 4 ≤ 0x40000000) (hqG : Sep q (l + 4) G 0x144)
    (k : ∀ (M' : Word → BitVec 8) (f' : Fin 32 → Word), TvfRegs F out p n g0 f' → TvfMemInv M0 G F g0 M' →
      (∀ t, rfc3339 (memBytes M q l) = some t → t < 2 ^ 64 ∧ M' (F + 0x10) = 0 ∧
        memLoad32 M' (F + 0x18) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
        memLoad32 M' (F + 0x1C) = BitVec.ofNat 32 (t / 2 ^ 32)) →
      (rfc3339 (memBytes M q l) = none → M' (F + 0x10) = 1 ∧ M' (F + 0x11) = 0x19) → f' 19 = f 19 → f' 20 = f 20 →
      WP trustedRootValidForCode TVF Q M' (off + 8) f') :
    WP trustedRootValidForCode TVF Q M off f := by
  have C := X.code.out hI.1 X.gw X.ro
  have gw := X.gw
  have fn := X.fn
  have e10 : F + 0x10 = G + BitVec.ofNat 32 0x114 := X.fGc 0x10 0x114 rfl
  have eH : F + 0xFFFFFF70 = G + BitVec.ofNat 32 0x74 := by rw [← X.fg, BitVec.add_assoc]; rfl
  have e18 : F + 0x10 + 8 = F + 0x18 := by rw [BitVec.add_assoc]; rfl
  have e1C : F + 0x10 + 0xC = F + 0x1C := by rw [BitVec.add_assoc]; rfl
  have e11 : F + 0x10 + 1 = F + 0x11 := by rw [BitVec.add_assoc]; rfl
  have hg74 : (G + BitVec.ofNat 32 0x74).toNat = G.toNat + 0x74 := X.gc (by decide)
  refine WP.trCallSaved (tb := RFC)
    (P := fun m2 => (∀ t, rfc3339 (memBytes M q l) = some t → t < 2 ^ 64 ∧ m2.mem (F + 0x10) = 0 ∧
        memLoad32 m2.mem (F + 0x18) = BitVec.ofNat 32 (t % 2 ^ 32) ∧
        memLoad32 m2.mem (F + 0x1C) = BitVec.ofNat 32 (t / 2 ^ 32)) ∧
      (rfc3339 (memBytes M q l) = none → m2.mem (F + 0x10) = 1 ∧ m2.mem (F + 0x11) = 0x19) ∧
      ∀ x, Sep (G + BitVec.ofNat 32 0x74) 0x90 x 1 → Sep (F + 0x10) 16 x 1 → m2.mem x = M x)
    h1 h2 htgt (fun m1 hpc1 hmem1 hreg1 _ => ?_) (fun m2 hP hcd => ?_) (fun m2 hP => ?_)
  · obtain ⟨m2, c2, pc2, sp2, keep2, ok2, err2, fr2⟩ := timeRfc3339_correct m1 (sp0 := F) (out := F + 0x10) (p := q)
      (n := l) (retAddr := TVF + BitVec.ofNat 32 (off + 8)) (by rw [hmem1]; exact C.rfc) (by rw [hmem1]; exact C.dt)
      (by rw [hmem1]; exact C.td) (by rw [hmem1]; exact C.td4) (by rw [hmem1]; exact C.aad) hpc1
      (by rw [hreg1]; trsimp; exact ha0) (by rw [hreg1]; trsimp; exact ha1) (by rw [hreg1]; trsimp; exact ha2)
      (by rw [hreg1]; trsimp) hev (by rw [hreg1]; trsimp; exact hR.2.1) X.fa (by omega) (by omega)
      (by rw [e10, X.gc (by decide)]; omega) (by rw [e10]; exact aligned_add X.ga (by decide)) hqw
      (by rw [e10, eH]; exact sep_offsets G (Or.inr (by decide)) (by decide) (by decide))
      (by rw [eH]; exact hqG.subR (by decide))
    rw [hmem1, e18, e1C] at ok2
    rw [hmem1, e11] at err2
    rw [hmem1, eH] at fr2
    refine ⟨m2, c2, pc2, ⟨ok2, err2, fr2⟩, ?_, fun q hq => keep2 q hq⟩
    rw [sp2, hreg1]; trsimp; exact hR.2.1.symm
  · exact hcd.hi (fun x hx => hP.2.2 x (lowSep (by omega) hx (by have := x.isLt; omega))
      (lowSep (by rw [e10, X.gc (by decide)]; omega) hx (by have := x.isLt; omega))) (by decide) (by decide)
  · have hO : Out M m2.mem (G + BitVec.ofNat 32 0x74) 0xB0 := fun x hx => by
      refine hP.2.2 x (trSepR hx (by decide)).symm ?_
      have e : G + BitVec.ofNat 32 0x74 + BitVec.ofNat 32 0xA0 = F + 0x10 := by rw [add_ofNat_assoc, e10]
      have := sep_in hx (d := 0xA0) (l := 16) (by decide)
      rw [e] at this; exact this.symm
    exact k m2.mem _ hR.clob (hI.step X hO (by decide)) hP.1 hP.2.1 (by trsimp) (by trsimp)

end

theorem tvf_beqF {x : Word} (h : x ≠ 0) : branchTaken .beq x 0 = false := by
  simp only [branchTaken, beq_eq_false_iff_ne]; exact h

theorem tvf_ne0 {x : Word} (h : x.toNat ≠ 0) : x ≠ 0 := fun e => h (by rw [e]; rfl)

/-- `Value::str`'s result and `tvfStr` on the same bytes. -/
theorem tvf_strCase (M : Word → BitVec 8) (q : Word) (l : Nat) :
    (tvfStr (memBytes M q l) = none ∧ strRes q (memBytes M q l) = none) ∨
    (2 ≤ l ∧ tvfStr (memBytes M q l) = some (memBytes M (q + 1) (l - 2)) ∧
      strRes q (memBytes M q l) = some (q + 1, l - 2)) := by
  unfold tvfStr strRes
  rw [memBytes_length]
  by_cases h1 : l < 2
  · exact Or.inl ⟨ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1)⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h1)]
  by_cases h2 : (memBytes M q l).getD 0 0 ≠ 34
  · exact Or.inl ⟨ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2)]
  by_cases h3 : (memBytes M q l).getD (l - 1) 0 ≠ 34
  · exact Or.inl ⟨ite_eq_left_of_eq_true _ _ (eq_true h3), ite_eq_left_of_eq_true _ _ (eq_true h3)⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_right_of_eq_false _ _ (eq_false h3)]
  exact Or.inr ⟨by omega, congrArg some (memBytes_drop_take (h := 1) (l := l - 2) (n := l) (by omega)), rfl⟩

theorem tvf_field_val {d key : Bytes} {a l : Nat} (h : objField d key = .ok (a, l)) :
    a < d.length ∧ a + l ≤ d.length := by
  unfold objField at h
  rcases hg : objGet d key with e | _ | ⟨a', l'⟩ <;> rw [hg] at h
  · cases h
  · cases h
  · cases h; exact objGet_val hg

section
variable {M0 : Word → BitVec 8} {G F out p : Word} {n : Nat} {g0 : Fin 32 → Word}

theorem TvfCtx.dlen (_ : TvfCtx M0 G F out p n g0) : (memBytes M0 p n).length = n := memBytes_length _ _ _

theorem TvfCtx.pa (X : TvfCtx M0 G F out p n g0) {a : Nat} (ha : a ≤ n + 4) :
    (p + BitVec.ofNat 32 a).toNat = p.toNat + a := by
  have := X.pw; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The bytes of a member of the object, as `tvfSlice` and as memory. -/
theorem TvfCtx.slice (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} (hO : Out M0 M G 0x144) {a l : Nat}
    (h : a + l ≤ n) :
    tvfSlice (memBytes M0 p n) (a, l) = memBytes M0 (p + BitVec.ofNat 32 a) l ∧
      memBytes M (p + BitVec.ofNat 32 a) l = memBytes M0 (p + BitVec.ofNat 32 a) l :=
  ⟨memBytes_drop_take h, hO.bytes (X.pg.sub (c := a) (l := l) (by omega)).symm⟩

/-- From 0x7C: `end`'s value is at `F + 0x14`, and `not_before = t` is in
`s3`/`s4`. Reads the value's time and writes the window or the error. -/
theorem TvfCtx.part3 (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {t a l : Nat}
    {r : Except Nat (Nat × Nat)} (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (h19 : f 19 = BitVec.ofNat 32 (t % 2 ^ 32)) (h20 : f 20 = BitVec.ofNat 32 (t / 2 ^ 32))
    (hq : memLoad32 M (F + 0x14) = p + BitVec.ofNat 32 a) (hl : memLoad32 M (F + 0x18) = BitVec.ofNat 32 l)
    (hal : a + l ≤ n)
    (hr : r = match tvfTime (tvfSlice (memBytes M0 p n) (a, l)) with
      | .error e => .error e
      | .ok u => .ok (t, u)) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) M 0x7C f := by
  have pw := X.pw
  have p0 := X.p0
  have hqn := X.pa (a := a) (by omega)
  have hq1 : (p + BitVec.ofNat 32 a + 1).toNat = p.toNat + a + 1 := by
    rw [BitVec.toNat_add, hqn, show (1 : Word).toNat = 1 from rfl]; omega
  obtain ⟨hv, hvM⟩ := X.slice hI.1 hal
  refine WP.lw tvf_at_7c (by rw [hR.2.1]; exact aligned_add X.fa (k := 0x14) (by decide)) ?_; wn
  refine WP.branch tvf_at_7e (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, hq, tvf_beqF (tvf_ne0 (by omega))]; decide)) (fun _ => ?_); wn
  refine WP.lw tvf_at_80 (by trsimp; rw [hR.2.1]; exact aligned_add X.fa (k := 0x18) (by decide)) ?_; wn
  refine WP.aluImm tvf_at_82 ?_; wn
  refine X.callStr (off := 0x84) (c := 0x20) (q := p + BitVec.ofNat 32 a) (l := l) tvf_at_84 tvf_at_88 (by decide)
    (by decide) (by tvf_regs hR) hI (by decide) (by decide) (by trsimp; rw [ev_add, hR.2.1] <;> rfl)
    (by trsimp; rw [hR.2.1, hq]) (by trsimp; rw [hR.2.1, hl]) (by omega)
    (fun M5 f5 hR5 hI5 hS5 g19 g20 => ?_)
  rw [hvM] at hS5
  rcases tvf_strCase M0 (p + BitVec.ofNat 32 a) l with ⟨hs, hsr⟩ | ⟨hl2, hs, hsr⟩
  · rw [hsr] at hS5
    have s0 : memLoad32 M5 (F + 0x20) = 0 := hS5.2.1
    have s1 : M5 (F + 0x24) = BitVec.ofNat 8 0x21 := by
      have := hS5.2.2; rw [BitVec.add_assoc] at this; exact this
    have hr' : r = .error 0x21 := by rw [hr, hv]; simp only [tvfTime, hs]
    refine WP.lw tvf_at_8c (by rw [hR5.2.1]; exact aligned_add X.fa (k := 0x20) (by decide)) ?_; wn
    refine WP.branch tvf_at_8e (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR5.2.1, s0]; decide)); wn
    exact X.errA8 hr' (by tvf_regs hR5) hI5 s1
  · rw [hsr] at hS5
    have s0 : memLoad32 M5 (F + 0x20) = p + BitVec.ofNat 32 a + 1 := hS5.2.1
    have s1 : memLoad32 M5 (F + 0x24) = BitVec.ofNat 32 (l - 2) := by
      have := hS5.2.2; rw [BitVec.add_assoc] at this; exact this
    have hs' : memBytes M5 (p + BitVec.ofNat 32 a + 1) (l - 2) = memBytes M0 (p + BitVec.ofNat 32 a + 1) (l - 2) := by
      have e : p + BitVec.ofNat 32 a + 1 = p + BitVec.ofNat 32 (a + 1) := add_ofNat_assoc p a 1
      rw [e]; exact hI5.1.bytes (X.pg.sub (c := a + 1) (l := l - 2) (by omega)).symm
    refine WP.lw tvf_at_8c (by rw [hR5.2.1]; exact aligned_add X.fa (k := 0x20) (by decide)) ?_; wn
    refine WP.branch tvf_at_8e (fun ht => absurd ht (by
      trsimp; rw [hR5.2.1, s0, tvf_beqF (tvf_ne0 (by omega))]; decide)) (fun _ => ?_); wn
    refine WP.lw tvf_at_90 (by trsimp; rw [hR5.2.1]; exact aligned_add X.fa (k := 0x24) (by decide)) ?_; wn
    refine WP.aluImm tvf_at_92 ?_; wn
    refine X.callRfc (off := 0x94) (q := p + BitVec.ofNat 32 a + 1) (l := l - 2) tvf_at_94 tvf_at_98 (by decide)
      (by decide) (by tvf_regs hR5) hI5 (by trsimp; rw [ev_add, hR5.2.1])
      (by trsimp; rw [hR5.2.1, s0]) (by trsimp; rw [hR5.2.1, s1]) (by omega)
      (by
        have e : p + BitVec.ofNat 32 a + 1 = p + BitVec.ofNat 32 (a + 1) := add_ofNat_assoc p a 1
        rw [e]; exact X.pg.sub (by omega))
      (fun M6 f6 hR6 hI6 ok6 err6 k19 k20 => ?_)
    rw [hs'] at ok6 err6
    rcases hrf : rfc3339 (memBytes M0 (p + BitVec.ofNat 32 a + 1) (l - 2)) with _ | u
    · obtain ⟨e0, e1⟩ := err6 hrf
      have hr' : r = .error 0x19 := by rw [hr, hv]; simp only [tvfTime, hs, hrf]
      refine WP.lbu tvf_at_9c ?_; wn
      refine WP.branch tvf_at_a0 (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR6.2.1, e0]; decide)); wn
      exact X.err70 hr' (by tvf_regs hR6) hI6 e1
    · obtain ⟨-, e0, e1, e2⟩ := ok6 u hrf
      have hr' : r = .ok (t, u) := by rw [hr, hv]; simp only [tvfTime, hs, hrf]
      refine WP.lbu tvf_at_9c ?_; wn
      refine WP.branch tvf_at_a0 (fun ht => absurd ht (by trsimp; rw [hR6.2.1, e0]; decide)) (fun _ => ?_); wn
      refine WP.lw tvf_at_a2 (by trsimp; rw [hR6.2.1]; exact aligned_add X.fa (k := 0x18) (by decide)) ?_; wn
      refine WP.lw tvf_at_a4 (by trsimp; rw [hR6.2.1]; exact aligned_add X.fa (k := 0x1C) (by decide)) ?_; wn
      refine WP.jal tvf_at_a6 (by decide) ?_; wn
      exact X.okCA hr' (by tvf_regs hR6) hI6 (by trsimp; rw [k19]; trsimp; rw [g19]; trsimp; exact h19)
        (by trsimp; rw [k20]; trsimp; rw [g20]; trsimp; exact h20) (by trsimp; rw [hR6.2.1, e1]) (by trsimp; rw [hR6.2.1, e2])


/-- From 0x4E: `start`'s time `t` is at `F + 0x18`. Moves it into `s3`/`s4`,
looks up `end`, and finishes. -/
theorem TvfCtx.part2 (X : TvfCtx M0 G F out p n g0) {M : Word → BitVec 8} {f : Fin 32 → Word} {t : Nat}
    {r : Except Nat (Nat × Nat)} (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (h18 : memLoad32 M (F + 0x18) = BitVec.ofNat 32 (t % 2 ^ 32))
    (h1c : memLoad32 M (F + 0x1C) = BitVec.ofNat 32 (t / 2 ^ 32))
    (hr : r = tvfRest (memBytes M0 p n) t) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out r) g0) M 0x4E f := by
  refine WP.lw tvf_at_4e (by rw [hR.2.1]; exact aligned_add X.fa (k := 0x18) (by decide)) ?_; wn
  refine WP.lw tvf_at_50 (by trsimp; rw [hR.2.1]; exact aligned_add X.fa (k := 0x1C) (by decide)) ?_; wn
  refine WP.lui tvf_at_52 ?_; wn
  refine WP.aluImm tvf_at_56 ?_; wn
  refine WP.aluImm tvf_at_5a ?_; wn
  refine WP.aluImm tvf_at_5c ?_; wn
  refine WP.alu tvf_at_5e ?_; wn
  refine WP.alu tvf_at_60 ?_; wn
  refine X.callGet (by tvf_regs hR) hI (by trsimp; rw [ev_add, hR.2.1]) (by trsimp; exact hR.2.2.1)
    (by trsimp; exact hR.2.2.2.1) (by trsimp <;> decide) (by trsimp)
    (fun M1 M5 f5 hR5 hI5 g g19 g20 => ?_)
  have k19 : f5 19 = BitVec.ofNat 32 (t % 2 ^ 32) := by rw [g19]; trsimp; rw [hR.2.1]; exact h18
  have k20 : f5 20 = BitVec.ofNat 32 (t / 2 ^ 32) := by rw [g20]; trsimp; rw [hR.2.1]; exact h1c
  rcases hg : objGet (memBytes M0 p n) (ascii!"end") with e | _ | ⟨a, l⟩ <;> rw [hg] at g
  · obtain ⟨-, e0, e1⟩ := g
    have e1' : M5 (F + 0x11) = BitVec.ofNat 8 e := by rw [BitVec.add_assoc] at e1; exact e1
    have hr' : r = .error e := by rw [hr]; unfold tvfRest; rw [hg]
    refine WP.lbu tvf_at_6a ?_; wn
    refine WP.branch tvf_at_6e (fun ht => absurd ht (by trsimp; rw [hR5.2.1, e0]; decide)) (fun _ => ?_); wn
    exact X.err70 hr' (by tvf_regs hR5) hI5 e1'
  · obtain ⟨-, e0, e1⟩ := g
    have e1' : memLoad32 M5 (F + 0x14) = 0 := by rw [BitVec.add_assoc] at e1; exact e1
    have hr' : r = .ok (t, 2 ^ 64 - 1) := by rw [hr]; unfold tvfRest; rw [hg]
    refine WP.lbu tvf_at_6a ?_; wn
    refine WP.branch tvf_at_6e (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR5.2.1, e0]; decide)); wn
    refine WP.lw tvf_at_7c (by trsimp; rw [hR5.2.1]; exact aligned_add X.fa (k := 0x14) (by decide)) ?_; wn
    refine WP.branch tvf_at_7e (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR5.2.1, e1']; decide)); wn
    exact X.noneC6 hr' (by tvf_regs hR5) hI5 (by trsimp; exact k19) (by trsimp; exact k20)
  · obtain ⟨-, e0, e1, e2⟩ := g
    have e1' : memLoad32 M5 (F + 0x14) = p + BitVec.ofNat 32 a := by rw [BitVec.add_assoc] at e1; exact e1
    have e2' : memLoad32 M5 (F + 0x18) = BitVec.ofNat 32 l := by rw [BitVec.add_assoc] at e2; exact e2
    have hv := objGet_val hg
    rw [X.dlen] at hv
    refine WP.lbu tvf_at_6a ?_; wn
    refine WP.branch tvf_at_6e (fun _ => ?_) (fun hf => absurd hf (by trsimp; rw [hR5.2.1, e0]; decide)); wn
    exact X.part3 (by tvf_regs hR5) hI5 (by trsimp; exact k19) (by trsimp; exact k20) e1' e2' hv.2
      (by rw [hr]; unfold tvfRest; rw [hg])


/-- From 0x28: `field(.., "start")`'s result is at `F + 0x20`. -/
theorem TvfCtx.part1 (X : TvfCtx M0 G F out p n g0) {M1 M : Word → BitVec 8} {f : Fin 32 → Word}
    (hR : TvfRegs F out p n g0 f) (hI : TvfMemInv M0 G F g0 M)
    (hF : FieldRes M1 M (F + 0x20) (fieldRes p (objField (memBytes M0 p n) (ascii!"start")))) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out (validForPos (memBytes M0 p n))) g0) M 0x28 f := by
  have pw := X.pw
  have p0 := X.p0
  rcases hf : objField (memBytes M0 p n) (ascii!"start") with e | ⟨a, l⟩ <;> rw [hf] at hF
  · obtain ⟨-, e0, e1⟩ := hF
    have e1' : M (F + 0x24) = BitVec.ofNat 8 e := by rw [BitVec.add_assoc] at e1; exact e1
    have hr : validForPos (memBytes M0 p n) = .error e := by unfold validForPos; rw [hf]
    refine WP.lw tvf_at_28 (by rw [hR.2.1]; exact aligned_add X.fa (k := 0x20) (by decide)) ?_; wn
    refine WP.branch tvf_at_2a (fun _ => ?_) (fun hb => absurd hb (by trsimp; rw [hR.2.1, e0]; decide)); wn
    exact X.errA8 hr (by tvf_regs hR) hI e1'
  obtain ⟨-, e0, e1⟩ := hF
  have e1' : memLoad32 M (F + 0x24) = BitVec.ofNat 32 l := by rw [BitVec.add_assoc] at e1; exact e1
  have hv := tvf_field_val hf
  rw [X.dlen] at hv
  have hqn := X.pa (a := a) (by omega)
  have hq1 : (p + BitVec.ofNat 32 a + 1).toNat = p.toNat + a + 1 := by
    rw [BitVec.toNat_add, hqn, show (1 : Word).toNat = 1 from rfl]; omega
  obtain ⟨hv', hvM⟩ := X.slice hI.1 hv.2
  refine WP.lw tvf_at_28 (by rw [hR.2.1]; exact aligned_add X.fa (k := 0x20) (by decide)) ?_; wn
  refine WP.branch tvf_at_2a (fun ht => absurd ht (by
    trsimp; rw [hR.2.1, e0, tvf_beqF (x := p + BitVec.ofNat 32 a) (tvf_ne0 (by omega))]; decide)) (fun _ => ?_); wn
  refine WP.lw tvf_at_2c (by trsimp; rw [hR.2.1]; exact aligned_add X.fa (k := 0x24) (by decide)) ?_; wn
  refine WP.aluImm tvf_at_2e ?_; wn
  refine X.callStr (off := 0x30) (c := 8) (q := p + BitVec.ofNat 32 a) (l := l) tvf_at_30 tvf_at_34 (by decide)
    (by decide) (by tvf_regs hR) hI (by decide) (by decide) (by trsimp; rw [ev_add, hR.2.1] <;> rfl)
    (by trsimp; rw [hR.2.1, e0]) (by trsimp; rw [hR.2.1, e1']) (by omega)
    (fun M5 f5 hR5 hI5 hS5 _ _ => ?_)
  rw [hvM] at hS5
  rcases tvf_strCase M0 (p + BitVec.ofNat 32 a) l with ⟨hs, hsr⟩ | ⟨hl2, hs, hsr⟩
  · rw [hsr] at hS5
    have s0 : memLoad32 M5 (F + 8) = 0 := hS5.2.1
    have s1 : M5 (F + 0xC) = BitVec.ofNat 8 0x21 := by
      have := hS5.2.2; rw [BitVec.add_assoc] at this; exact this
    have hr : validForPos (memBytes M0 p n) = .error 0x21 := by
      unfold validForPos; rw [hf]; simp only [hv', tvfTime, hs]
    refine WP.lw tvf_at_38 (by rw [hR5.2.1]; exact aligned_add X.fa (k := 8) (by decide)) ?_; wn
    refine WP.branch tvf_at_3a (fun _ => ?_) (fun hb => absurd hb (by trsimp; rw [hR5.2.1, s0]; decide)); wn
    exact X.err76 hr (by tvf_regs hR5) hI5 s1
  rw [hsr] at hS5
  have s0 : memLoad32 M5 (F + 8) = p + BitVec.ofNat 32 a + 1 := hS5.2.1
  have s1 : memLoad32 M5 (F + 0xC) = BitVec.ofNat 32 (l - 2) := by
    have := hS5.2.2; rw [BitVec.add_assoc] at this; exact this
  have hs' : memBytes M5 (p + BitVec.ofNat 32 a + 1) (l - 2) = memBytes M0 (p + BitVec.ofNat 32 a + 1) (l - 2) := by
    have e : p + BitVec.ofNat 32 a + 1 = p + BitVec.ofNat 32 (a + 1) := add_ofNat_assoc p a 1
    rw [e]; exact hI5.1.bytes (X.pg.sub (c := a + 1) (l := l - 2) (by omega)).symm
  refine WP.lw tvf_at_38 (by rw [hR5.2.1]; exact aligned_add X.fa (k := 8) (by decide)) ?_; wn
  refine WP.branch tvf_at_3a (fun ht => absurd ht (by
    trsimp; rw [hR5.2.1, s0, tvf_beqF (tvf_ne0 (by omega))]; decide)) (fun _ => ?_); wn
  refine WP.lw tvf_at_3c (by trsimp; rw [hR5.2.1]; exact aligned_add X.fa (k := 0xC) (by decide)) ?_; wn
  refine WP.aluImm tvf_at_3e ?_; wn
  refine X.callRfc (off := 0x40) (q := p + BitVec.ofNat 32 a + 1) (l := l - 2) tvf_at_40 tvf_at_44 (by decide)
    (by decide) (by tvf_regs hR5) hI5 (by trsimp; rw [ev_add, hR5.2.1])
    (by trsimp; rw [hR5.2.1, s0]) (by trsimp; rw [hR5.2.1, s1]) (by omega)
    (by
      have e : p + BitVec.ofNat 32 a + 1 = p + BitVec.ofNat 32 (a + 1) := add_ofNat_assoc p a 1
      rw [e]; exact X.pg.sub (by omega))
    (fun M6 f6 hR6 hI6 ok6 err6 _ _ => ?_)
  rw [hs'] at ok6 err6
  rcases hrf : rfc3339 (memBytes M0 (p + BitVec.ofNat 32 a + 1) (l - 2)) with _ | t
  · obtain ⟨e0, e1⟩ := err6 hrf
    have hr : validForPos (memBytes M0 p n) = .error 0x19 := by
      unfold validForPos; rw [hf]; simp only [hv', tvfTime, hs, hrf]
    refine WP.lbu tvf_at_48 ?_; wn
    refine WP.branch tvf_at_4c (fun _ => ?_) (fun hb => absurd hb (by trsimp; rw [hR6.2.1, e0]; decide)); wn
    exact X.err70 hr (by tvf_regs hR6) hI6 e1
  obtain ⟨-, e0, e1, e2⟩ := ok6 t hrf
  have hr : validForPos (memBytes M0 p n) = tvfRest (memBytes M0 p n) t := by
    unfold validForPos; rw [hf]; simp only [hv', tvfTime, hs, hrf]
  refine WP.lbu tvf_at_48 ?_; wn
  refine WP.branch tvf_at_4c (fun ht => absurd ht (by trsimp; rw [hR6.2.1, e0]; decide)) (fun _ => ?_); wn
  exact X.part2 (by tvf_regs hR6) hI6 e1 e2 hr


/-- The six saves of the prologue, into the frame at `F`. -/
def tvfSave (M : Word → BitVec 8) (F r1 r8 r9 r18 r19 r20 : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (F + BitVec.ofNat 32 0x3C) r1)
    (F + BitVec.ofNat 32 0x38) r8) (F + BitVec.ofNat 32 0x34) r9) (F + BitVec.ofNat 32 0x30) r18)
    (F + BitVec.ofNat 32 0x2C) r19) (F + BitVec.ofNat 32 0x28) r20

theorem tvfSave_spec (M : Word → BitVec 8) (F r1 r8 r9 r18 r19 r20 : Word) :
    Out M (tvfSave M F r1 r8 r9 r18 r19 r20) F 0x40 ∧
      memLoad32 (tvfSave M F r1 r8 r9 r18 r19 r20) (F + BitVec.ofNat 32 0x3C) = r1 ∧
      memLoad32 (tvfSave M F r1 r8 r9 r18 r19 r20) (F + BitVec.ofNat 32 0x38) = r8 ∧
      memLoad32 (tvfSave M F r1 r8 r9 r18 r19 r20) (F + BitVec.ofNat 32 0x34) = r9 ∧
      memLoad32 (tvfSave M F r1 r8 r9 r18 r19 r20) (F + BitVec.ofNat 32 0x30) = r18 ∧
      memLoad32 (tvfSave M F r1 r8 r9 r18 r19 r20) (F + BitVec.ofNat 32 0x2C) = r19 ∧
      memLoad32 (tvfSave M F r1 r8 r9 r18 r19 r20) (F + BitVec.ofNat 32 0x28) = r20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((Out.upK rfl (out_store32 _ _ _) (by decide)).trans (Out.upK rfl (out_store32 _ _ _) (by decide))).trans
      (Out.upK rfl (out_store32 _ _ _) (by decide))).trans (Out.upK rfl (out_store32 _ _ _) (by decide))).trans
      (Out.upK rfl (out_store32 _ _ _) (by decide))).trans (Out.upK rfl (out_store32 _ _ _) (by decide))
  · exact trdc_slot 0x3C 0x28 (by decide) (by decide) (by decide) <|
      trdc_slot 0x3C 0x2C (by decide) (by decide) (by decide) <|
      trdc_slot 0x3C 0x30 (by decide) (by decide) (by decide) <|
      trdc_slot 0x3C 0x34 (by decide) (by decide) (by decide) <|
      trdc_slot 0x3C 0x38 (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact trdc_slot 0x38 0x28 (by decide) (by decide) (by decide) <|
      trdc_slot 0x38 0x2C (by decide) (by decide) (by decide) <|
      trdc_slot 0x38 0x30 (by decide) (by decide) (by decide) <|
      trdc_slot 0x38 0x34 (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact trdc_slot 0x34 0x28 (by decide) (by decide) (by decide) <|
      trdc_slot 0x34 0x2C (by decide) (by decide) (by decide) <|
      trdc_slot 0x34 0x30 (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact trdc_slot 0x30 0x28 (by decide) (by decide) (by decide) <|
      trdc_slot 0x30 0x2C (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact trdc_slot 0x2C 0x28 (by decide) (by decide) (by decide) <| memLoad32_store32_same _ _ _
  · exact memLoad32_store32_same _ _ _

/-- The whole function, from its entry with `a0 = out`, `a1 = p`, and
`a2 = n`. -/
theorem TvfCtx.entry (X : TvfCtx M0 G F out p n g0) (h0 : g0 a0 = out) (h1 : g0 a1 = p)
    (h2 : g0 a2 = BitVec.ofNat 32 n) :
    WP trustedRootValidForCode TVF (trPost (tvfMem M0 G out (validForPos (memBytes M0 p n))) g0) M0 0 g0 := by
  refine WP.aluImm tvf_at_0 ?_; wn
  rw [show aluEval .add (g0 sp) 0xFFFFFFC0 = F by rw [X.sp0, ev_add, BitVec.add_assoc]; exact BitVec.add_zero F]
  refine WP.sw tvf_at_2 (by trsimp; exact aligned_add X.fa (k := 0x3C) (by decide))
    (by trsimp; exact X.flo (c := 0x3C) (by decide)) ?_; wn
  refine WP.sw tvf_at_4 (by trsimp; exact aligned_add X.fa (k := 0x38) (by decide))
    (by trsimp; exact X.flo (c := 0x38) (by decide)) ?_; wn
  refine WP.sw tvf_at_6 (by trsimp; exact aligned_add X.fa (k := 0x34) (by decide))
    (by trsimp; exact X.flo (c := 0x34) (by decide)) ?_; wn
  refine WP.sw tvf_at_8 (by trsimp; exact aligned_add X.fa (k := 0x30) (by decide))
    (by trsimp; exact X.flo (c := 0x30) (by decide)) ?_; wn
  refine WP.sw tvf_at_a (by trsimp; exact aligned_add X.fa (k := 0x2C) (by decide))
    (by trsimp; exact X.flo (c := 0x2C) (by decide)) ?_; wn
  refine WP.sw tvf_at_c (by trsimp; exact aligned_add X.fa (k := 0x28) (by decide))
    (by trsimp; exact X.flo (c := 0x28) (by decide)) ?_; wn
  change WP trustedRootValidForCode TVF _ (tvfSave M0 F (g0 ra) (g0 8) (g0 9) (g0 18) (g0 19) (g0 20)) 0xE _
  obtain ⟨hO1, v1, v2, v3, v4, v5, v6⟩ := tvfSave_spec M0 F (g0 ra) (g0 8) (g0 9) (g0 18) (g0 19) (g0 20)
  generalize tvfSave M0 F (g0 ra) (g0 8) (g0 9) (g0 18) (g0 19) (g0 20) = M1 at hO1 v1 v2 v3 v4 v5 v6
  have hI : TvfMemInv M0 G F g0 M1 := ⟨Out.upK X.fg hO1 (by decide), v1, v2, v3, v4, v5, v6⟩
  refine WP.alu tvf_at_e ?_; wn
  refine WP.alu tvf_at_10 ?_; wn
  refine WP.alu tvf_at_12 ?_; wn
  refine WP.lui tvf_at_14 ?_; wn
  refine WP.aluImm tvf_at_18 ?_; wn
  refine WP.aluImm tvf_at_1c ?_; wn
  refine WP.aluImm tvf_at_1e ?_; wn
  refine X.callField ⟨by trsimp, by trsimp, by trsimp; exact h1, by trsimp; exact h2, by trsimp; exact h0,
      fun q hq => by rcases tvf_rest_cases q hq with h | h | h | h | h | h | h | h | h <;> subst h <;> trsimp⟩
    hI (by trsimp <;> rfl) (by trsimp; exact h1) (by trsimp; exact h2) (by trsimp <;> decide) (by trsimp <;> rfl)
    (fun _ _ _ hR' hI' hF _ _ => X.part1 hR' hI' hF)

end

theorem trustedRootValidFor_correct (m : Machine) {sp0 out p retAddr : Word} {n : Nat}
    (hc : TvfCode m.mem) (hpc : m.pc = TVF) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0) (hsl : 0x144 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (hoa : out.toNat % 4 = 0) (how : out.toNat + 0x18 ≤ 0x40000000) (hpw : p.toNat + n + 4 ≤ 0x40000000)
    (hp0 : p.toNat ≠ 0) (sOG : Sep out 0x18 (sp0 + 0xFFFFFEBC) 0x144) (sPG : Sep p (n + 4) (sp0 + 0xFFFFFEBC) 0x144)
    (sRO : Sep (sp0 + 0xFFFFFEBC) 0x144 TVF_RO 0x1400)
    (hks : memBytes m.mem tvfStartKey 5 = ascii!"start") (hke : memBytes m.mem tvfEndKey 3 = ascii!"end") :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q : Fin 32, q.val ∈ trSaved → reg m' q = reg m q) ∧
      tvfMem m.mem (sp0 + 0xFFFFFEBC) out (validForPos (memBytes m.mem p n)) m'.mem := by
  have hG : (sp0 + 0xFFFFFEBC : Word).toNat = sp0.toNat - 0x144 := by
    rw [BitVec.toNat_add, show (0xFFFFFEBC : Word).toNat = 2 ^ 32 - 0x144 from rfl]; omega
  have X : TvfCtx m.mem (sp0 + 0xFFFFFEBC) (sp0 + 0xFFFFFEBC + BitVec.ofNat 32 0x104) out p n (reg m) :=
    { code := hc, fg := rfl, ga := by omega, gw := by omega, oa := hoa, ow := how, og := sOG, pw := hpw,
      p0 := hp0, pg := sPG, ro := sRO, ks := hks, ke := hke,
      sp0 := by rw [hsp, BitVec.add_assoc, BitVec.add_assoc]; exact (BitVec.add_zero sp0).symm
      ret := by rw [hra]; exact hret }
  obtain ⟨m', hs, hpc', hsp', hk, hR⟩ := WP.run (X.entry ha0 ha1 ha2) (by decide) hc.self hpc
  exact ⟨m', hs, hpc'.trans hra, hsp'.trans hsp, hk, hR⟩

end C3.RV32
