import C3BootProofs.Spec.Der

/-!
# Reading DER structures

The `c3_verify::der::Der` helpers that the certificate and timestamp
parsers use, over the element reader in `Spec/Der.lean`. Each returns the
value read and the bytes after it, or `none` where Rust returns an error.
-/

namespace C3

/-- One element: its tag, its contents, and the whole element. -/
structure Elem where
  tag : Nat
  content : Bytes
  raw : Bytes
  deriving DecidableEq, Repr

/-- `Der::tlv`: the element at the front, whatever its tag. -/
def readTlv (rest : Bytes) : Option (Elem × Bytes) :=
  match derTlv rest with
  | .ok t => some (⟨t.tag, t.content rest, rest.take (t.header + t.len)⟩, rest.drop (t.header + t.len))
  | .error _ => none

/-- `Der::element`: the element at the front, which must have tag `tag`. -/
def readElem (tag : Nat) (rest : Bytes) : Option (Elem × Bytes) :=
  if rest.head? == some tag then readTlv rest else none

/-- `Der::optional`: the element at the front if it has tag `tag`. -/
def readOptional (tag : Nat) (rest : Bytes) : Option (Option Elem × Bytes) :=
  if rest.head? == some tag then (readTlv rest).map fun (e, r) => (some e, r) else some (none, rest)

/-- `Der::oid`: an `OBJECT IDENTIFIER`'s contents. -/
def readOid (rest : Bytes) : Option (Bytes × Bytes) := do
  let (e, r) ← readElem 6 rest
  require (derOidOk e.content)
  pure (e.content, r)

/-- `Der::integer`: a minimally encoded `INTEGER`'s contents. -/
def readInteger (rest : Bytes) : Option (Bytes × Bytes) := do
  let (e, r) ← readElem 2 rest
  match e.content with
  | [] => none
  | 0x00 :: next :: _ => if next < 0x80 then none else some (e.content, r)
  | 0xff :: next :: _ => if next ≥ 0x80 then none else some (e.content, r)
  | _ => some (e.content, r)

/-- `Der::positive_integer`: an `INTEGER` above zero, with its leading zero
byte if it has one. -/
def readPositiveInteger (rest : Bytes) : Option (Bytes × Bytes) := do
  let (c, r) ← readInteger rest
  match c with
  | [0x00] => none
  | first :: _ => if first ≥ 0x80 then none else some (c, r)
  | [] => none

/-- `Der::boolean_true`: a `BOOLEAN` that is `TRUE`. -/
def readBooleanTrue (rest : Bytes) : Option Bytes := do
  let (e, r) ← readElem 1 rest
  require (e.content == [0xff])
  pure r

/-- `Der::octet_string`: an `OCTET STRING`'s contents. -/
def readOctetString (rest : Bytes) : Option (Bytes × Bytes) := do
  let (e, r) ← readElem 4 rest
  pure (e.content, r)

/-- `Der::bit_string`: a `BIT STRING` with no unused bits. -/
def readBitString (rest : Bytes) : Option (Bytes × Bytes) := do
  let (e, r) ← readElem 3 rest
  match e.content with
  | 0 :: bits => some (bits, r)
  | _ => none

/-- The trailing zero bits of a byte, 8 for zero. -/
def trailingZeros8 (b : Nat) : Nat :=
  if b % 256 = 0 then 8 else (List.range 8).find? (fun i => b / 2 ^ i % 2 == 1) |>.getD 8

/-- `Der::named_bits`: a named-bit-list `BIT STRING` in its DER form. -/
def readNamedBits (rest : Bytes) : Option (Bytes × Bytes) := do
  let (e, r) ← readElem 3 rest
  match e.content with
  | [] => none
  | unused :: bits =>
    match bits.getLast? with
    | none => if unused == 0 then some (bits, r) else none
    | some last => if trailingZeros8 last == unused then some (bits, r) else none

/-- `Der::algorithm`: an `AlgorithmIdentifier`'s OID and parameters. -/
def readAlgorithm (rest : Bytes) : Option ((Bytes × Option Elem) × Bytes) := do
  let (seq, r) ← readElem 0x30 rest
  let (oid, inner) ← readOid seq.content
  if inner.isEmpty then pure ((oid, none), r)
  else
    let (p, after) ← readTlv inner
    require after.isEmpty
    pure ((oid, some p), r)

/-- `lists_oid`: whether `list`, a run of `SEQUENCE`s that each start with
an OID, holds one that starts with `oid`. `fuel` bounds the elements. -/
def listsOid (oid : Bytes) : Nat → Bytes → Option Bool
  | _, [] => some false
  | 0, _ :: _ => none
  | fuel + 1, list@(_ :: _) => do
    let (seq, r) ← readElem 0x30 list
    let (o, _) ← readOid seq.content
    if o == oid then pure true else listsOid oid fuel r

/-- One `INTEGER` of an `ECDSA-Sig-Value` as an `n`-byte big-endian number. -/
def readSigScalar (n : Nat) (rest : Bytes) : Option (Bytes × Bytes) := do
  let (c, r) ← readPositiveInteger rest
  let mag := match c with
    | 0x00 :: m => m
    | _ => c
  require (mag.length ≤ n)
  pure (List.replicate (n - mag.length) 0 ++ mag, r)

/-- `ecdsa_signature::<n>`: a DER `ECDSA-Sig-Value` and nothing after it,
as `n`-byte `r` and `s`. -/
def ecdsaSignature (n : Nat) (der : Bytes) : Option (Bytes × Bytes) := do
  let (seq, after) ← readElem 0x30 der
  require after.isEmpty
  let (r, rest) ← readSigScalar n seq.content
  let (s, rest) ← readSigScalar n rest
  require rest.isEmpty
  pure (r, s)

end C3
