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

/-- `valid_for` on the object whose bytes are `d`: the window's
`not_before` and `not_after`, or the error byte. -/
def validForPos (d : Bytes) : Except Nat (Nat × Nat) :=
  match objField d (ascii!"start") with
  | .error e => .error e
  | .ok x => match tvfTime (tvfSlice d x) with
    | .error e => .error e
    | .ok t => match objGet d (ascii!"end") with
      | .error e => .error e
      | .ok none => .ok (t, 2 ^ 64 - 1)
      | .ok (some y) => match tvfTime (tvfSlice d y) with
        | .error e => .error e
        | .ok u => .ok (t, u)

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

end C3.RV32
