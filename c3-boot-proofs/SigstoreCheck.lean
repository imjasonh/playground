import C3BootProofs

/-!
Reads the lines that `c3-boot/verify/examples/sigstore_vectors.rs` and
`c3-boot/crypto/examples/crypto_vectors.rs` print,
runs each input through the Lean specification of the Sigstore check's
parts, and prints the line with the specification's result. CI requires the
output to equal the Rust program's.
-/

open C3

def okOr (r : Option String) : String := r.getD "err"

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
