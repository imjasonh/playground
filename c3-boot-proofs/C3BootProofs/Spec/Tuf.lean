import C3BootProofs.Spec.Json
import C3BootProofs.Spec.Base64
import C3BootProofs.Spec.DerRead
import C3BootProofs.Spec.Ed25519
import C3BootProofs.Spec.Time
import C3BootProofs.Hex

/-!
# Sigstore's TUF metadata

The checks of `c3_verify::tuf`:

- Each root after the pinned one has the next version and is signed by a
  threshold of the previous root's root keys and a threshold of its own.
- `targets.json` is signed by a threshold of the last root's targets keys,
  and lists `trusted_root.json` with its length and SHA-256 digest.

A role's threshold counts distinct keys whose signature over the canonical
`signed` value verifies. Keys of types other than ECDSA P-256 and P-384
with SHA-256 and SHA-384, and Ed25519, never count. The result is the last
root's version and the earlier of the two expiry times.
-/

namespace C3

/-- A TUF key of a type the device verifies. -/
inductive TufKey where
  | p256 (point : Bytes)
  | p384 (point : Bytes)
  | ed25519 (key : Bytes)
  deriving DecidableEq, Repr

def p256SpkiPrefix : Bytes :=
  [0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a,
    0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x03, 0x42, 0x00]

def p384SpkiPrefix : Bytes :=
  [0x30, 0x76, 0x30, 0x10, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x05, 0x2b,
    0x81, 0x04, 0x00, 0x22, 0x03, 0x62, 0x00]

/-- The DER key in a PEM `PUBLIC KEY` block: the base64 between the header
and footer lines, without its line feeds. -/
def pemSpki (pem : Bytes) : Option Bytes := do
  let body ← readExpect (ascii!"-----BEGIN PUBLIC KEY-----\n") pem
  let footer := ascii!"-----END PUBLIC KEY-----\n"
  require (footer.isSuffixOf body)
  base64Decode ((body.take (body.length - footer.length)).filter (· != 0x0A))

/-- The point after an SPKI prefix, if it has `len` bytes. -/
def spkiPoint (pfx : Bytes) (len : Nat) (spki : Bytes) : Option Bytes := do
  let point ← readExpect pfx spki
  require (point.length == len)
  pure point

/-- `tuf::decode_key`. -/
def decodeKey (key : Json) : Option TufKey := do
  let keytype ← key.field (ascii!"keytype") >>= Json.asStr
  let scheme ← key.field (ascii!"scheme") >>= Json.asStr
  let pubKey ← key.field (ascii!"keyval") >>= Json.field (ascii!"public") >>= Json.asStr
  let ecdsa := keytype == ascii!"ecdsa"
  if (ecdsa || keytype == ascii!"ecdsa-sha2-nistp256") && scheme == ascii!"ecdsa-sha2-nistp256" then
    .p256 <$> (pemSpki pubKey >>= spkiPoint p256SpkiPrefix 65)
  else if (ecdsa || keytype == ascii!"ecdsa-sha2-nistp384") && scheme == ascii!"ecdsa-sha2-nistp384" then
    .p384 <$> (pemSpki pubKey >>= spkiPoint p384SpkiPrefix 97)
  else if keytype == ascii!"ed25519" && scheme == ascii!"ed25519" then do
    let k ← parseHex pubKey
    require (k.length == 32)
    pure (.ed25519 k)
  else none

/-- `tuf::signature_valid`: `sig` is lowercase hex of a DER ECDSA signature
over the message's SHA-256 or SHA-384 digest, or of an Ed25519 signature
over the message. -/
def sigValid (key : TufKey) (msg sig : Bytes) : Bool :=
  match parseHex sig, key with
  | some s, .p256 point => match ecdsaSignature 32 s with
    | some (r, s) => p256Verify point (sha256 msg) r s
    | none => false
  | some s, .p384 point => match ecdsaSignature 48 s with
    | some (r, s) => p384Verify point (sha384 msg) r s
    | none => false
  | some s, .ed25519 k => s.length == 64 && ed25519Verify k msg s
  | none, _ => false

/-- A metadata document: its `signed` value and its signatures as key ID
and hex signature. -/
structure Meta where
  signed : Json
  sigs : List (Bytes × Bytes)

/-- `tuf::parse_metadata`: a canonical document with exactly the members
`signatures` and `signed`, `signed._type` equal to `kind`, and no key ID
signing twice. -/
def parseMeta (doc kind : Bytes) : Option Meta := do
  match ← parseJson true doc with
  | .obj [(k1, sigs), (k2, signed)] =>
    require (k1 == ascii!"signatures" && k2 == ascii!"signed")
    require ((signed.field (ascii!"_type") >>= Json.asStr) == some kind)
    let pairs ← (← sigs.asArr).mapM fun s => do
      pure (← s.field (ascii!"keyid") >>= Json.asStr, ← s.field (ascii!"sig") >>= Json.asStr)
    require (distinct (pairs.map (·.1)))
    pure ⟨signed, pairs⟩
  | _ => none

/-- `tuf::threshold_met`: whether at least the threshold of distinct keys
that `delegator`, a root's `signed` value, lists for `role` signed `md`, the metadata.
A role lists at most 8 key IDs of at most 64 bytes. -/
def thresholdMet (md : Meta) (delegator : Json) (role : Bytes) : Option Bool := do
  let r ← delegator.field (ascii!"roles") >>= Json.field role
  let threshold ← r.field (ascii!"threshold") >>= Json.asNum
  require (threshold ≥ 1)
  let keys ← delegator.field (ascii!"keys") >>= Json.asObj
  let ids ← (← r.field (ascii!"keyids") >>= Json.asArr).mapM Json.asStr
  require (ids.length ≤ 8 && ids.all (·.length ≤ 64))
  let msg := encode md.signed
  let good := ids.filterMap fun id => do
    let key ← keys.lookup id >>= decodeKey
    let sig ← md.sigs.lookup id
    if sigValid key msg sig then some key else none
  pure (good.eraseDups.length ≥ threshold)

structure TufRoot where
  md : Meta
  version : Nat

def parseTufRoot (doc : Bytes) : Option TufRoot := do
  let md ← parseMeta doc (ascii!"root")
  let version ← md.signed.field (ascii!"version") >>= Json.asNum
  require (version ≥ 1)
  pure ⟨md, version⟩

/-- `time::rfc3339`: `YYYY-MM-DDTHH:MM:SSZ`, optionally with a fraction of
one or more digits before the `Z`, which is dropped. -/
def rfc3339 (text : Bytes) : Option Nat := do
  let (year, rest) ← readDigits 4 text
  match rest with
  | 0x2D :: m1 :: m2 :: 0x2D :: d1 :: d2 :: 0x54 :: h1 :: h2 :: 0x3A :: n1 :: n2 :: 0x3A :: s1 :: s2 ::
      zone =>
    let (t, _) ← readDateTime year [m1, m2, d1, d2, h1, h2, n1, n2, s1, s2]
    match zone with
    | [0x5A] => pure t
    | 0x2E :: fz =>
      match fz.reverse with
      | 0x5A :: frac => do
        require (!frac.isEmpty && frac.all isDigit)
        pure t
      | _ => none
    | _ => none
  | _ => none

def expires (md : Meta) : Option Nat :=
  md.signed.field (ascii!"expires") >>= Json.asStr >>= rfc3339

/-- Lowercase hex digits of bytes. -/
def hexBytes (b : Bytes) : Bytes :=
  b.flatMap fun x => [x / 16, x % 16].map fun d => if d < 10 then 48 + d else 87 + d

/-- The TUF part of a slot. -/
structure TufParts where
  roots : List Bytes
  targets : Bytes
  trustedRoot : Bytes

/-- `tuf::MAX_ROOTS`, `tuf::MAX_DOC_LEN`, and `tuf::MAX_TUF_LEN`. -/
def maxRoots : Nat := 64
def maxDocLen : Nat := 10240
def maxTufLen : Nat := 0x60000

/-- The index: `n` lengths of 4 bytes, each from 1 to `maxDocLen`. -/
def readLengths : Nat → Bytes → Option (List Nat × Bytes)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
    let (len, rest) ← readU32 bytes
    require (1 ≤ len && len ≤ maxDocLen)
    let (lens, rest) ← readLengths n rest
    pure (len :: lens, rest)

/-- Splits documents of the given lengths off the front of `bytes`. -/
def splitDocs : List Nat → Bytes → Option (List Bytes × Bytes)
  | [], bytes => some ([], bytes)
  | len :: lens, bytes => do
    require (len ≤ bytes.length)
    let (docs, rest) ← splitDocs lens (bytes.drop len)
    pure (bytes.take len :: docs, rest)

/-- `tuf::read_index` and the documents it locates: at most `maxTufLen`
bytes, the magic `C3TU`, version 2, at most 64 roots, an index of each
root's, `targets.json`'s, and `trusted_root.json`'s length, then those
documents with nothing after them. -/
def decodeTufParts (bytes : Bytes) : Option TufParts := do
  require (bytes.length ≤ maxTufLen)
  let rest ← readExpect (ascii!"C3TU") bytes
  let (version, rest) ← readU16 rest
  require (version == 2)
  let (count, rest) ← readU16 rest
  require (count ≤ maxRoots)
  let (lens, rest) ← readLengths (count + 2) rest
  let (docs, rest) ← splitDocs lens rest
  require rest.isEmpty
  match docs.reverse with
  | trustedRoot :: targets :: roots => pure ⟨roots.reverse, targets, trustedRoot⟩
  | _ => none

/-- `tuf::verify`: the last root's version and the earlier expiry time. -/
def verifyTuf (pinned : Bytes) (parts : TufParts) : Option (Nat × Nat) := do
  let first ← parseTufRoot pinned
  let root ← parts.roots.foldlM (init := first) fun prev doc => do
    let next ← parseTufRoot doc
    require (next.version == prev.version + 1)
    require (← thresholdMet next.md prev.md.signed (ascii!"root"))
    require (← thresholdMet next.md next.md.signed (ascii!"root"))
    pure next
  let rootExpires ← expires root.md
  let targets ← parseMeta parts.targets (ascii!"targets")
  require (← thresholdMet targets root.md.signed (ascii!"targets"))
  let targetsExpires ← expires targets
  let entry ← targets.signed.field (ascii!"targets") >>= Json.field (ascii!"trusted_root.json")
  let length ← entry.field (ascii!"length") >>= Json.asNum
  let digest ← entry.field (ascii!"hashes") >>= Json.field (ascii!"sha256") >>= Json.asStr
  require (length == parts.trustedRoot.length && digest == hexBytes (sha256 parts.trustedRoot))
  pure (root.version, min rootExpires targetsExpires)

end C3

open C3 in
#guard rfc3339 (ascii!"2027-04-22T19:27:31Z") == some 1808422051
open C3 in
#guard rfc3339 (ascii!"2022-12-31T23:59:59.999Z") == some 1672531199
open C3 in
#guard rfc3339 (ascii!"2022-12-31T23:59:59.Z") == none
open C3 in
#guard hexBytes [0x00, 0xab] == ascii!"00ab"
