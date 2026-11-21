import C3BootProofs

/-!
Reads the lines that `c3-boot/verify/examples/sigstore_vectors.rs` and
`c3-boot/crypto/examples/crypto_vectors.rs`, and
`c3-boot/ota/examples/sigstore_e2e_vectors.rs` print,
runs each input through the Lean specification of the Sigstore check's
parts, and prints the line with the specification's result. CI requires the
output to equal the Rust program's.
-/

open C3

def okOr (r : Option String) : String := r.getD "err"

/-- `NAME.KEY.NOT_BEFORE.NOT_AFTER` entries, `;`-separated. -/
def parseEntries (s : String) : Option (List (Bytes × Bytes × Window)) :=
  if s.isEmpty then some []
  else (s.splitOn ";").mapM fun e =>
    match e.splitOn "." with
    | [n, k, nb, na] => do pure (← parseHexTok n, ← parseHexTok k, ⟨← nb.toNat?, ← na.toNat?⟩)
    | _ => none

/-- A trust root's Sigstore keys and policy, as the vector printers list
them. -/
def parseRoot (s : String) : Option SigstoreRoot :=
  match s.splitOn "/" with
  | [f, l, t, p] => do
    let fulcio ← parseEntries f
    let logs ← parseEntries l
    let tsas ← parseEntries t
    match p.splitOn "." with
    | [a, b, c, d, e] =>
      pure ⟨fulcio.map fun (n, k, w) => ⟨n, k, w⟩, logs.map fun (n, k, w) => ⟨n, k, w⟩,
        tsas.map fun (n, k, w) => ⟨n, k, w⟩,
        ⟨← parseHexTok a, ← parseHexTok b, ← parseHexTok c, ← parseHexTok d, ← parseHexTok e⟩⟩
    | _ => none
  | _ => none

/-- The specification's result for one input, or `none` if the line doesn't
parse. -/
def result (tokens : List String) : Option String :=
  match tokens with
  | ["b64e", h] => do pure (hexStr (base64Encode (← parseHexTok h)))
  | ["b64d", h] => do
    let text ← parseHexTok h
    pure <| okOr ((base64Decode text).map fun b => s!"ok {hexStr b}")
  | ["utc", h] => do pure <| okOr ((utcTime (← parseHexTok h)).map fun t => s!"ok {t}")
  | ["gen", h] => do pure <| okOr ((generalizedTime (← parseHexTok h)).map fun t => s!"ok {t}")
  | ["bundle", h] => do
    pure <| okOr ((decodeBundle (← parseHexTok h)).map fun b =>
      s!"ok {hexStr b.leafCertificate} {hexStr b.imageSignature} {b.logIndex} {hexStr b.inclusionProof} " ++
        s!"{hexStr b.checkpoint} {hexStr b.timestamp}")
  | ["rekor", d, s, c] => do
    pure (hexStr (rekorLeafHash (← parseHexTok d) (← parseHexTok s) (← parseHexTok c)))
  | ["sha384", h] => do pure (hexStr (sha384 (← parseHexTok h)))
  | ["p256", k, d, r, s] => do
    pure (if p256Verify (← parseHexTok k) (← parseHexTok d) (← parseHexTok r) (← parseHexTok s) then "1" else "0")
  | ["p384", k, d, r, s] => do
    pure (if p384Verify (← parseHexTok k) (← parseHexTok d) (← parseHexTok r) (← parseHexTok s) then "1" else "0")
  | ["ed25519", k, m, s] => do
    pure (if ed25519Verify (← parseHexTok k) (← parseHexTok m) (← parseHexTok s) then "1" else "0")
  | ["checkpoint", h, r] => do
    let text ← parseHexTok h
    let root ← parseRoot r
    pure <| okOr ((verifyCheckpoint text root).map fun c =>
      s!"ok {hexStr c.log.origin} {c.size} {hexStr c.root}")
  | ["leaf", h] => do
    pure <| okOr ((parseLeaf (← parseHexTok h)).map fun l =>
      s!"ok {hexStr l.tbs} {hexStr l.issuer} {l.notBefore} {l.notAfter} {hexStr l.publicKey} " ++
        s!"{hexStr l.sigR} {hexStr l.sigS} " ++ " ".intercalate (l.identity.map hexStr))
  | ["leafsig", h, subj, key] => do
    let leaf ← parseLeaf (← parseHexTok h)
    pure (if verifyLeaf leaf ⟨← parseHexTok subj, ← parseHexTok key, ⟨0, 0⟩⟩ then "1" else "0")
  | ["tsr", h] => do
    pure <| okOr ((parseTimestamp (← parseHexTok h)).map fun ts =>
      s!"ok {ts.genTime} {hexStr ts.messageImprint} {hexStr ts.tstInfo} {hexStr ts.messageDigest} " ++
        s!"{hexStr ts.signerId} {hexStr ts.signedAttrs} {hexStr ts.sigR} {hexStr ts.sigS}")
  | ["tsrsig", h, sid, key, sig] => do
    let ts ← parseTimestamp (← parseHexTok h)
    pure (if verifyTimestamp ts ⟨← parseHexTok sid, ← parseHexTok key, ⟨0, 0⟩⟩ (← parseHexTok sig) then "1" else "0")
  | ["verify", c, r, d] => do
    let root ← parseRoot r
    let digest ← parseHexTok d
    pure <| okOr (do
      let b ← decodeBundle (← parseHexTok c)
      let v ← sigstoreVerify b root digest
      pure s!"ok {v.signedTime} {v.logIndex}")
  | _ => none

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let text := line.trimAsciiEnd.toString
  let input := (text.splitOn " | ").headD ""
  match result (input.splitOn " ") with
  | some r =>
    stdout.putStrLn s!"{input} | {r}"
    loop stdin stdout
  | none =>
    IO.eprintln s!"can't parse: {text}"
    return 1

def main : IO UInt32 := do
  loop (← IO.getStdin) (← IO.getStdout)
