import C3BootProofs.Spec.DerRead
import C3BootProofs.Spec.Time
import C3BootProofs.Spec.Checkpoint

/-!
# The Fulcio leaf certificate

The leaf certificate profile of `c3-boot/docs/formats.md`, as
`c3_verify::x509::parse_leaf` checks it, and the issuer's signature, as
`verify_leaf` checks it: an X.509 v3 certificate signed with
ECDSA-with-SHA384, a P-256 subject key, `keyUsage` with
`digitalSignature`, `extKeyUsage` with `codeSigning`, not a CA, no
duplicate extensions, only the four standard extensions marked critical,
and the five identity-policy extensions each holding one `UTF8String`.
-/

namespace C3

/-- `ecdsa-with-SHA384`, 1.2.840.10045.4.3.3. -/
def oidEcdsaSha384 : Bytes := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x03]
/-- `id-ecPublicKey`, 1.2.840.10045.2.1. -/
def oidEcPublicKey : Bytes := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]
/-- `prime256v1`, 1.2.840.10045.3.1.7. -/
def oidPrime256v1 : Bytes := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]
/-- `keyUsage`, 2.5.29.15. -/
def oidKeyUsage : Bytes := [0x55, 0x1d, 0x0f]
/-- `subjectAltName`, 2.5.29.17. -/
def oidSubjectAltName : Bytes := [0x55, 0x1d, 0x11]
/-- `basicConstraints`, 2.5.29.19. -/
def oidBasicConstraints : Bytes := [0x55, 0x1d, 0x13]
/-- `extKeyUsage`, 2.5.29.37. -/
def oidExtKeyUsage : Bytes := [0x55, 0x1d, 0x25]
/-- `codeSigning`, 1.3.6.1.5.5.7.3.3. -/
def oidCodeSigning : Bytes := [0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x03]

/-- The Fulcio identity-policy extension 1.3.6.1.4.1.57264.1.`n`. -/
def oidFulcio (n : Nat) : Bytes := [0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xbf, 0x30, 0x01, n]

/-- The identity-policy extensions, in the policy's order: Issuer (V2),
Build Signer URI, Source Repository Identifier, Source Repository Owner
Identifier, and Build Trigger. -/
def policyOids : List Bytes := [oidFulcio 8, oidFulcio 9, oidFulcio 15, oidFulcio 17, oidFulcio 20]

/-- The extensions that may be marked critical. -/
def criticalAllowed : List Bytes := [oidKeyUsage, oidSubjectAltName, oidBasicConstraints, oidExtKeyUsage]

/-- A leaf certificate that fits the profile, before its signature is
checked. -/
structure Leaf where
  /-- The whole `tbsCertificate` element. -/
  tbs : Bytes
  /-- The whole issuer `Name` element. -/
  issuer : Bytes
  notBefore : Nat
  notAfter : Nat
  /-- The subject's P-256 key, uncompressed SEC 1. -/
  publicKey : Bytes
  /-- The issuer's signature, as 48-byte `r` and `s`. -/
  sigR : Bytes
  sigS : Bytes
  /-- The five identity-policy strings, in the policy's order. -/
  identity : List Bytes
  deriving DecidableEq, Repr

/-- A `UTCTime` or `GeneralizedTime`. -/
def readTime (rest : Bytes) : Option (Nat × Bytes) := do
  let (e, r) ← readTlv rest
  if e.tag == 0x17 then pure (← utcTime e.content, r)
  else if e.tag == 0x18 then pure (← generalizedTime e.content, r)
  else none

/-- A `SubjectPublicKeyInfo` holding a P-256 key on the curve. -/
def readP256Spki (rest : Bytes) : Option (Bytes × Bytes) := do
  let (spki, r) ← readElem 0x30 rest
  let ((alg, params), inner) ← readAlgorithm spki.content
  require (alg == oidEcPublicKey && params.any (fun p => p.tag == 6 && p.content == oidPrime256v1))
  let (point, inner) ← readBitString inner
  require (point.length == 65 && inner.isEmpty && (p256.decodePoint point).isSome)
  pure (point, r)

/-- Whether a `KeyUsage` value sets `digitalSignature`. -/
def keyUsageSigns (value : Bytes) : Option Bool := do
  let (bits, after) ← readNamedBits value
  require after.isEmpty
  pure (bits.head?.any (· ≥ 0x80))

/-- Whether an `ExtKeyUsageSyntax` value lists `codeSigning`; every entry
must be an OID. -/
def extKeyUsageCodeSigning (value : Bytes) : Option Bool := do
  let (seq, after) ← readElem 0x30 value
  require after.isEmpty
  let rec go : Nat → Bytes → Bool → Option Bool
    | _, [], found => some found
    | 0, _ :: _, _ => none
    | fuel + 1, rest@(_ :: _), found => do
      let (oid, r) ← readOid rest
      go fuel r (found || oid == oidCodeSigning)
  go seq.content.length seq.content false

/-- Whether a `BasicConstraints` value sets `cA`. -/
def basicConstraintsCa (value : Bytes) : Option Bool := do
  let (seq, after) ← readElem 0x30 value
  require after.isEmpty
  let ca := seq.content.head? == some 1
  let rest ← if ca then readBooleanTrue seq.content else some seq.content
  let rest ← if rest.head? == some 2 then (readInteger rest).map (·.2) else some rest
  require rest.isEmpty
  pure ca

/-- An identity-policy value: one `UTF8String` that fills it. -/
def policyString (value : Bytes) : Option Bytes := do
  let (e, after) ← readTlv value
  require (e.tag == 0x0c && after.isEmpty)
  pure e.content

/-- What the extensions seen so far established. -/
structure ExtState where
  keyUsage : Bool := false
  codeSigning : Bool := false
  policy : List (Option Bytes) := [none, none, none, none, none]

/-- Checks the extensions in `list` after `earlier` (the extensions already
read), and returns what they established. -/
def readExtensionList (earlier : Bytes) : Nat → Bytes → ExtState → Option ExtState
  | _, [], st => some st
  | 0, _ :: _, _ => none
  | fuel + 1, list@(_ :: _), st => do
    let (ext, r) ← readElem 0x30 list
    let (oid, inner) ← readOid ext.content
    let critical := inner.head? == some 1
    let inner ← if critical then readBooleanTrue inner else some inner
    let (value, inner) ← readOctetString inner
    require inner.isEmpty
    let dup ← listsOid oid earlier.length earlier
    require (!dup && !(critical && !criticalAllowed.contains oid))
    let st ←
      if oid == oidKeyUsage then do
        require (← keyUsageSigns value)
        pure { st with keyUsage := true }
      else if oid == oidExtKeyUsage then do
        require (← extKeyUsageCodeSigning value)
        pure { st with codeSigning := true }
      else if oid == oidBasicConstraints then do
        require !(← basicConstraintsCa value)
        pure st
      else
        match policyOids.idxOf? oid with
        | some i => do
          let s ← policyString value
          pure { st with policy := st.policy.set i (some s) }
        | none => pure st
    readExtensionList (earlier ++ ext.raw) fuel r st

/-- The extensions' contents: they must hold `keyUsage`, `extKeyUsage`, and
all five identity-policy extensions. Returns the policy strings. -/
def readExtensions (content : Bytes) : Option (List Bytes) := do
  let (seq, after) ← readElem 0x30 content
  require after.isEmpty
  let st ← readExtensionList [] seq.content.length seq.content {}
  require (st.keyUsage && st.codeSigning)
  st.policy.mapM id

/-- `x509::parse_leaf`. -/
def parseLeaf (der : Bytes) : Option Leaf := do
  let (cert, after) ← readElem 0x30 der
  require after.isEmpty
  let (tbs, c) ← readElem 0x30 cert.content
  let (outerAlg, c) ← readElem 0x30 c
  let (sigValue, c) ← readBitString c
  require c.isEmpty
  let (version, t) ← readOptional 0xa0 tbs.content
  let version ← version
  let (v, vrest) ← readInteger version.content
  require (v == [2] && vrest.isEmpty)
  let (serial, t) ← readPositiveInteger t
  require (serial.length ≤ 20)
  let (alg, t) ← readElem 0x30 t
  let ((algOid, params), _) ← readAlgorithm alg.raw
  require (algOid == oidEcdsaSha384 && params.isNone)
  let (issuer, t) ← readElem 0x30 t
  let (validity, t) ← readElem 0x30 t
  let (notBefore, vr) ← readTime validity.content
  let (notAfter, vr) ← readTime vr
  require vr.isEmpty
  let (_, t) ← readElem 0x30 t
  let (publicKey, t) ← readP256Spki t
  let (exts, t) ← readOptional 0xa3 t
  let exts ← exts
  require t.isEmpty
  let identity ← readExtensions exts.content
  require (outerAlg.raw == alg.raw)
  let (r, s) ← ecdsaSignature 48 sigValue
  pure ⟨tbs.raw, issuer.raw, notBefore, notAfter, publicKey, r, s, identity⟩

/-- `x509::verify_leaf`: `intermediate` issued the leaf, and its key signed
the `tbsCertificate`'s SHA-384 digest. -/
def verifyLeaf (leaf : Leaf) (intermediate : FulcioKey) : Bool :=
  leaf.issuer == intermediate.subject &&
    p384Verify intermediate.publicKey (sha384 leaf.tbs) leaf.sigR leaf.sigS

end C3
