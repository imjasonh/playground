import C3BootProofs.Spec.Tuf
import C3BootProofs.Spec.X509

/-!
# The keys in Sigstore's trusted root

The keys `c3_verify::trusted_root::extract` reads from `trusted_root.json`,
in the `SigstoreRoot` form that `sigstoreVerify` takes:

- a certificate authority whose first certificate has a P-384 key gives a
  Fulcio key with that certificate's subject;
- a transparency log with an Ed25519 key gives a log key whose origin is
  its base URL without `https://` and trailing slashes;
- a timestamp authority whose first certificate has a P-384 key gives a TSA
  key whose `SignerIdentifier` is that certificate's issuer and serial
  number.

Each window is the entry's `validFor` intersected with every certificate
in its chain. Entries with other key types are skipped. At most 8 Fulcio
keys, 16 logs, and 8 TSAs, with no subject, origin, `SignerIdentifier`, or
key listed twice.
-/

namespace C3

/-- The fields of a certificate that the trusted root's entries use. -/
structure CertInfo where
  /-- The whole serial number `INTEGER`. -/
  serial : Bytes
  /-- The whole issuer `Name`. -/
  issuer : Bytes
  /-- The whole subject `Name`. -/
  subject : Bytes
  window : Window
  /-- The subject key, if it is a P-384 point on the curve. -/
  p384Key : Option Bytes

/-- `secp384r1`, 1.3.132.0.34. -/
def oidSecp384r1 : Bytes := [0x2b, 0x81, 0x04, 0x00, 0x22]

/-- The P-384 point of a whole `SubjectPublicKeyInfo`, if it holds one. -/
def spkiP384 (spki : Bytes) : Option Bytes := do
  let (seq, after) ← readElem 0x30 spki
  require after.isEmpty
  let ((alg, params), inner) ← readAlgorithm seq.content
  require (alg == oidEcPublicKey && params.any (fun p => p.tag == 6 && p.content == oidSecp384r1))
  let (point, inner) ← readBitString inner
  require (point.length == 97 && inner.isEmpty && (p384.decodePoint point).isSome)
  pure point

/-- A certificate: three elements in a `SEQUENCE`, whose `tbsCertificate`
starts with the optional version, serial number, signature algorithm,
issuer, validity, subject, and key. -/
def parseCert (der : Bytes) : Option CertInfo := do
  let (cert, after) ← readElem 0x30 der
  require after.isEmpty
  let (tbs, rest) ← readElem 0x30 cert.content
  let (_, rest) ← readElem 0x30 rest
  let (_, rest) ← readBitString rest
  require rest.isEmpty
  let (_, t) ← readOptional 0xA0 tbs.content
  let (serial, t) ← readElem 2 t
  let (_, t) ← readElem 0x30 t
  let (issuer, t) ← readElem 0x30 t
  let (validity, t) ← readElem 0x30 t
  let (notBefore, v) ← readTime validity.content
  let (notAfter, v) ← readTime v
  require v.isEmpty
  let (subject, t) ← readElem 0x30 t
  let (spki, _) ← readElem 0x30 t
  pure ⟨serial.raw, issuer.raw, subject.raw, ⟨notBefore, notAfter⟩, spkiP384 spki.raw⟩

def u64Max : Nat := 2 ^ 64 - 1

/-- A `validFor` object; a missing `end` is the last representable second. -/
def validFor (v : Json) : Option Window := do
  let start ← v.field (ascii!"start") >>= Json.asStr >>= rfc3339
  let stop ← match v.field (ascii!"end") with
    | none => pure u64Max
    | some e => e.asStr >>= rfc3339
  pure ⟨start, stop⟩

def Window.intersect (a b : Window) : Window :=
  ⟨max a.notBefore b.notBefore, min a.notAfter b.notAfter⟩

/-- An entry's first certificate, and its `validFor` intersected with every
certificate in its chain of 1 to 4. -/
def readChain (entry : Json) : Option (CertInfo × Window) := do
  let w ← entry.field (ascii!"validFor") >>= validFor
  let certs ← entry.field (ascii!"certChain") >>= Json.field (ascii!"certificates") >>= Json.asArr
  require (1 ≤ certs.length && certs.length ≤ 4)
  let infos ← certs.mapM fun c =>
    c.field (ascii!"rawBytes") >>= Json.asStr >>= base64Decode >>= parseCert
  let first ← infos.head?
  pure (first, infos.foldl (fun w c => w.intersect c.window) w)

/-- A DER length, for contents under 64 KiB. -/
def derLen (n : Nat) : Option Bytes :=
  if n < 0x80 then some [n]
  else if n < 0x100 then some [0x81, n]
  else if n < 0x10000 then some [0x82, n / 256, n % 256]
  else none

def ed25519SpkiPrefix : Bytes := [0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00]

/-- A log entry's key, or `none` inside when its key isn't Ed25519. -/
def logEntry (tlog : Json) : Option (Option LogKey) := do
  let key ← tlog.field (ascii!"publicKey")
  let details ← key.field (ascii!"keyDetails") >>= Json.asStr
  if details != ascii!"PKIX_ED25519" then pure none else
  let pk ← key.field (ascii!"rawBytes") >>= Json.asStr >>= base64Decode >>= readExpect ed25519SpkiPrefix
  require (pk.length == 32 && (Ed25519.decode pk).any (fun q => !Ed25519.smallOrder q))
  let url ← tlog.field (ascii!"baseUrl") >>= Json.asStr
  let origin := ((← readExpect (ascii!"https://") url).reverse.dropWhile (· == 0x2F)).reverse
  require (!origin.isEmpty && origin.all fun b => 0x20 ≤ b && b ≤ 0x7e)
  pure (some ⟨origin, pk, ← key.field (ascii!"validFor") >>= validFor⟩)

/-- `trusted_root::extract`: the keys of a `trusted_root.json`, with
`policy`. -/
def extractTrustedRoot (json : Bytes) (policy : Policy) : Option SigstoreRoot := do
  let root ← parseJson false json
  require ((root.field (ascii!"mediaType") >>= Json.asStr) ==
    some (ascii!"application/vnd.dev.sigstore.trustedroot+json;version=0.1"))
  let cas ← root.field (ascii!"certificateAuthorities") >>= Json.asArr
  let tlogs ← root.field (ascii!"tlogs") >>= Json.asArr
  let tsaEntries ← root.field (ascii!"timestampAuthorities") >>= Json.asArr
  let fulcio ← cas.mapM fun ca => do
    let (c, w) ← readChain ca
    pure (c.p384Key.map fun k => (⟨c.subject, k, w⟩ : FulcioKey))
  let logs ← tlogs.mapM logEntry
  let tsas ← tsaEntries.mapM fun t => do
    let (c, w) ← readChain t
    match c.p384Key with
    | none => pure none
    | some k =>
      let body := c.issuer ++ c.serial
      pure (some (⟨[0x30] ++ (← derLen body.length) ++ body, k, w⟩ : TsaKey))
  let fulcio := fulcio.filterMap id
  let logs := logs.filterMap id
  let tsas := tsas.filterMap id
  require (fulcio.length ≤ 8 && logs.length ≤ 16 && tsas.length ≤ 8)
  require (distinct (fulcio.map (·.subject)) && distinct (fulcio.map (·.publicKey)) &&
    distinct (logs.map (·.origin)) && distinct (logs.map (·.publicKey)) &&
    distinct (tsas.map (·.signerId)) && distinct (tsas.map (·.publicKey)))
  pure ⟨fulcio, logs, tsas, policy⟩

end C3
