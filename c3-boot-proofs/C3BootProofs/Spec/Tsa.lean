import C3BootProofs.Spec.X509

/-!
# The RFC 3161 timestamp

The timestamp profile of `c3-boot/docs/formats.md`, as
`c3_verify::tsa::parse_timestamp` checks a `TimeStampResp`, and the TSA's
signature and digests, as `verify_timestamp` checks them: a granted status,
CMS `SignedData` v3 with SHA-256, one `SignerInfo` v1 naming its signer by
issuer and serial number, signed `contentType` and `messageDigest`
attributes, an ECDSA-with-SHA256 signature, and a `TSTInfo` v1 whose
imprint is SHA-256.
-/

namespace C3

/-- `signedData`, 1.2.840.113549.1.7.2. -/
def oidSignedData : Bytes := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x02]
/-- `id-ct-TSTInfo`, 1.2.840.113549.1.9.16.1.4. -/
def oidTstInfo : Bytes := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x10, 0x01, 0x04]
/-- `contentType`, 1.2.840.113549.1.9.3. -/
def oidContentType : Bytes := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x03]
/-- `messageDigest`, 1.2.840.113549.1.9.4. -/
def oidMessageDigest : Bytes := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x04]
/-- `sha256`, 2.16.840.1.101.3.4.2.1. -/
def oidSha256 : Bytes := [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]
/-- `ecdsa-with-SHA256`, 1.2.840.10045.4.3.2. -/
def oidEcdsaSha256 : Bytes := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02]

/-- A timestamp that fits the profile, before its signature and digests are
checked. -/
structure Timestamp where
  /-- The signed time, in seconds since the Unix epoch. -/
  genTime : Nat
  /-- The `TSTInfo`'s `messageImprint` digest. -/
  messageImprint : Bytes
  /-- The DER `TSTInfo`. -/
  tstInfo : Bytes
  /-- The signed `messageDigest` attribute. -/
  messageDigest : Bytes
  /-- The whole `sid` element. -/
  signerId : Bytes
  /-- The whole `[0]` signed attributes element. -/
  signedAttrs : Bytes
  sigR : Bytes
  sigS : Bytes
  deriving DecidableEq, Repr

/-- An `AlgorithmIdentifier` that is `sha256` with absent or `NULL`
parameters. -/
def readSha256Alg (rest : Bytes) : Option Bytes := do
  let ((oid, params), r) ← readAlgorithm rest
  require (oid == oidSha256 && params.all (fun p => p.tag == 5 && p.content.isEmpty))
  pure r

/-- An `INTEGER` that must equal `v`. -/
def readIntegerIs (v : Nat) (rest : Bytes) : Option Bytes := do
  let (c, r) ← readInteger rest
  require (c == [v])
  pure r

/-- The signed attributes: they must hold `contentType` naming `TSTInfo`
and a 32-byte `messageDigest`, with no attribute twice. Returns the
message digest. -/
def readSignedAttributes (content : Bytes) : Option Bytes :=
  let rec go : Bytes → Nat → Bytes → Bool → Option Bytes → Option (Bool × Option Bytes)
    | _, _, [], ct, md => some (ct, md)
    | _, 0, _ :: _, _, _ => none
    | earlier, fuel + 1, list@(_ :: _), ct, md => do
      let (attr, r) ← readElem 0x30 list
      let (oid, inner) ← readOid attr.content
      let (values, inner) ← readElem 0x31 inner
      require inner.isEmpty
      let dup ← listsOid oid earlier.length earlier
      require !dup
      if oid == oidContentType then do
        let (t, vr) ← readOid values.content
        require (t == oidTstInfo && vr.isEmpty)
        go (earlier ++ attr.raw) fuel r true md
      else if oid == oidMessageDigest then do
        let (d, vr) ← readOctetString values.content
        require (d.length == 32 && vr.isEmpty)
        go (earlier ++ attr.raw) fuel r ct (some d)
      else go (earlier ++ attr.raw) fuel r ct md
  do
    let (ct, md) ← go [] content.length content false none
    require ct
    md

/-- The `TSTInfo`'s signed time and imprint. -/
def readTstInfo (der : Bytes) : Option (Nat × Bytes) := do
  let (info, after) ← readElem 0x30 der
  require after.isEmpty
  let i ← readIntegerIs 1 info.content
  let (_, i) ← readOid i
  let (imprint, i) ← readElem 0x30 i
  let ir ← readSha256Alg imprint.content
  let (msgImprint, ir) ← readOctetString ir
  require (msgImprint.length == 32 && ir.isEmpty)
  let (serial, i) ← readPositiveInteger i
  let mag := match serial with
    | 0x00 :: m => m
    | _ => serial
  require (mag.length ≤ 20)
  let (gt, i) ← readElem 0x18 i
  let genTime ← generalizedTime gt.content
  let (_, i) ← readOptional 0x30 i
  let i ← if i.head? == some 1 then readBooleanTrue i else some i
  let i ← if i.head? == some 2 then (readInteger i).map (·.2) else some i
  let (_, i) ← readOptional 0xa0 i
  let (_, i) ← readOptional 0xa1 i
  require i.isEmpty
  pure (genTime, msgImprint)

/-- `tsa::parse_timestamp`. -/
def parseTimestamp (der : Bytes) : Option Timestamp := do
  let (response, after) ← readElem 0x30 der
  require after.isEmpty
  let (status, resp) ← readElem 0x30 response.content
  let sr ← readIntegerIs 0 status.content
  require sr.isEmpty
  let (contentInfo, resp) ← readElem 0x30 resp
  require resp.isEmpty
  let (ctype, ci) ← readOid contentInfo.content
  require (ctype == oidSignedData)
  let (explicit, ci) ← readElem 0xa0 ci
  require ci.isEmpty
  let (signedData, ex) ← readElem 0x30 explicit.content
  require ex.isEmpty
  let sd ← readIntegerIs 3 signedData.content
  let (digestAlgs, sd) ← readElem 0x31 sd
  let da ← readSha256Alg digestAlgs.content
  require da.isEmpty
  let (encap, sd) ← readElem 0x30 sd
  let (etype, en) ← readOid encap.content
  require (etype == oidTstInfo)
  let (econtent, en) ← readOptional 0xa0 en
  let econtent ← econtent
  require en.isEmpty
  let (tstInfo, ec) ← readOctetString econtent.content
  require ec.isEmpty
  let (_, sd) ← readOptional 0xa0 sd
  require (sd.head? != some 0xa1)
  let (signerInfos, sd) ← readElem 0x31 sd
  require sd.isEmpty
  let (signerInfo, si) ← readElem 0x30 signerInfos.content
  require si.isEmpty
  let s ← readIntegerIs 1 signerInfo.content
  let (sid, s) ← readElem 0x30 s
  let s ← readSha256Alg s
  let (signedAttrs, s) ← readOptional 0xa0 s
  let signedAttrs ← signedAttrs
  let messageDigest ← readSignedAttributes signedAttrs.content
  let ((alg, params), s) ← readAlgorithm s
  require (alg == oidEcdsaSha256 && params.isNone)
  let (sigBytes, s) ← readOctetString s
  let (r, sig) ← ecdsaSignature 48 sigBytes
  require s.isEmpty
  let (genTime, imprint) ← readTstInfo tstInfo
  pure ⟨genTime, imprint, tstInfo, messageDigest, sid.raw, signedAttrs.raw, r, sig⟩

/-- `tsa::verify_timestamp`: `signer` signed the token, and the token covers
`imageSignature`. The signature is over the signed attributes with their
`[0]` tag replaced by the `SET OF` tag. -/
def verifyTimestamp (ts : Timestamp) (signer : TsaKey) (imageSignature : Bytes) : Bool :=
  ts.signerId == signer.signerId && sha256 ts.tstInfo == ts.messageDigest &&
    sha256 imageSignature == ts.messageImprint && !ts.signedAttrs.isEmpty &&
    p384Verify signer.publicKey (sha256 (0x31 :: ts.signedAttrs.drop 1)) ts.sigR ts.sigS

end C3
