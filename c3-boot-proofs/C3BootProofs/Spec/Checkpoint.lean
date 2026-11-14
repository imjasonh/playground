import C3BootProofs.Spec.Bundle
import C3BootProofs.Spec.Ed25519

/-!
# The Sigstore keys and the signed checkpoint

The parts of a parsed trust-root blob that the Sigstore check uses, as
`c3_verify::trustroot::TrustRoot` holds them, and the signed checkpoint note
that commits a Rekor log to a tree, as `c3_verify::checkpoint::verify` reads
it (`c3-boot/docs/formats.md`).
-/

namespace C3

/-- An inclusive validity window, in seconds since the Unix epoch. -/
structure Window where
  notBefore : Nat
  notAfter : Nat
  deriving DecidableEq, Repr

def Window.contains (w : Window) (t : Nat) : Bool := w.notBefore ≤ t && t ≤ w.notAfter

/-- A Fulcio intermediate: its subject name (DER) and P-384 key. -/
structure FulcioKey where
  subject : Bytes
  publicKey : Bytes
  window : Window
  deriving DecidableEq, Repr

/-- A transparency log: its origin string and Ed25519 key. -/
structure LogKey where
  origin : Bytes
  publicKey : Bytes
  window : Window
  deriving DecidableEq, Repr

/-- A timestamp authority: the DER `SignerIdentifier` its tokens name, and
its P-384 key. -/
structure TsaKey where
  signerId : Bytes
  publicKey : Bytes
  window : Window
  deriving DecidableEq, Repr

/-- The values the Fulcio leaf's extensions must equal. -/
structure Policy where
  issuer : Bytes
  buildSignerUri : Bytes
  repositoryId : Bytes
  ownerId : Bytes
  trigger : Bytes
  deriving DecidableEq, Repr

/-- The Sigstore keys and identity policy of a trust root. -/
structure SigstoreRoot where
  fulcio : List FulcioKey
  logs : List LogKey
  tsas : List TsaKey
  policy : Policy
  deriving DecidableEq, Repr

/-- A checkpoint whose signature by a listed log key checked. -/
structure Checkpoint where
  log : LogKey
  size : Nat
  root : Bytes
  deriving DecidableEq, Repr

/-- The line up to the first newline, without the newline, and the rest. -/
def splitLine : Bytes → Option (Bytes × Bytes)
  | [] => none
  | 10 :: rest => some ([], rest)
  | b :: rest => do
    let (l, r) ← splitLine rest
    pure (b :: l, r)

/-- A decimal tree size with no sign or leading zeros, at most `2^63 - 1`. -/
def treeSize (text : Bytes) : Option Nat := do
  require (!text.isEmpty && text.length ≤ 19 && !(text.length > 1 && text.head? == some 48) &&
    text.all (fun c => 48 ≤ c && c ≤ 57))
  let n := text.foldl (fun acc c => acc * 10 + (c - 48)) 0
  require (n < 2 ^ 63)
  pure n

/-- The C2SP key ID of an Ed25519 key: the first four bytes of
`SHA-256(name || 0x0A || 0x01 || key)`. -/
def logKeyId (name key : Bytes) : Bytes := (sha256 (name ++ [0x0A, 0x01] ++ key)).take 4

/-- The em dash and space that start every signature line. -/
def sigLinePrefix : Bytes := [0xE2, 0x80, 0x94, 0x20]

/-- The bytes before the first space, and the bytes after it. -/
def splitSpace : Bytes → Option (Bytes × Bytes)
  | [] => none
  | 0x20 :: rest => some ([], rest)
  | b :: rest => do
    let (l, r) ← splitSpace rest
    pure (b :: l, r)

/-- Reads the signature lines, keeping the one signature from `origin`
whose key hint is `id`. Every line must be well formed, and at most one
may match. `fuel` bounds the lines. -/
def checkpointSigs (origin id : Bytes) : Nat → Bytes → Option Bytes → Option (Option Bytes)
  | _, [], matched => some matched
  | 0, _ :: _, _ => none
  | fuel + 1, text@(_ :: _), matched => do
    let (line, rest) ← splitLine text
    let afterDash ← readExpect sigLinePrefix line
    let (name, encoded) ← splitSpace afterDash
    require (!name.isEmpty && (base64Decode encoded).isSome && !encoded.isEmpty)
    if name != origin then checkpointSigs origin id fuel rest matched
    else
      let value ← base64Decode encoded
      require (value.length ≤ 96)
      if value.length < 4 || value.take 4 != id then checkpointSigs origin id fuel rest matched
      else
        let sig := value.drop 4
        require (sig.length == 64 && matched.isNone)
        checkpointSigs origin id fuel rest (some sig)

/-- Parses `text` as a checkpoint signed by a log in `root`, and checks that
log's signature: three body lines (origin, tree size, root hash in base64),
a blank line, and signature lines, exactly one of them from the origin's
log key. -/
def verifyCheckpoint (text : Bytes) (root : SigstoreRoot) : Option Checkpoint := do
  let (origin, rest) ← splitLine text
  let (sizeText, rest) ← splitLine rest
  let (rootText, rest) ← splitLine rest
  let (blank, sigs) ← splitLine rest
  require (blank.isEmpty && !sigs.isEmpty)
  let body := text.take (text.length - sigs.length - 1)
  let size ← treeSize sizeText
  let rootHash ← base64Decode rootText
  require (rootHash.length == 32)
  let log ← root.logs.find? (·.origin == origin)
  let matched ← checkpointSigs origin (logKeyId origin log.publicKey) sigs.length sigs none
  let sig ← matched
  require (ed25519Verify log.publicKey body sig)
  pure ⟨log, size, rootHash⟩

end C3
