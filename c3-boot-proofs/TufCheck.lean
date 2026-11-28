import C3BootProofs.Spec.Accept

/-!
Reads the lines that `c3-boot/ota/examples/tuf_vectors.rs` prints, runs
each input through the Lean specification of the TUF checks, and prints the
line with the specification's result. CI requires the output to equal the
Rust program's.
-/

open C3

/-- The release identity that the accept cases use, `tuf_cases::POLICY`. -/
def policy : Policy :=
  ⟨ascii!"https://token.actions.githubusercontent.com",
    ascii!"https://github.com/imjasonh/playground/.github/workflows/c3-release.yml@refs/heads/main",
    ascii!"1234", ascii!"5678", ascii!"push"⟩

def okOr (r : Option String) : String := r.getD "err"

/-- Entries joined by `,`, or `-` for none. -/
def entries {α : Type} (xs : List α) (f : α → String) : String :=
  if xs.isEmpty then "-" else ",".intercalate (xs.map f)

def entry (name key : Bytes) (w : Window) : String :=
  s!"{hexStr name}/{hexStr key}/{w.notBefore}/{w.notAfter}"

/-- The specification's result for one input, or `none` if the line doesn't
parse. -/
def result : List String → Option String
  | [_, "json", mode, doc] => do
    let canonical ← if mode == "canonical" then some true else if mode == "strict" then some false
      else none
    pure (if (parseJson canonical (← parseHexTok doc)).isSome then "ok" else "err")
  | [_, "tuf", pinned, tuf] => do
    let pinned ← parseHexTok pinned
    let tuf ← parseHexTok tuf
    pure <| okOr ((decodeTufParts tuf >>= verifyTuf pinned).map fun (v, e) => s!"ok {v} {e}")
  | [_, "trusted", json] => do
    let empty : Policy := ⟨[], [], [], [], []⟩
    pure <| okOr ((extractTrustedRoot (← parseHexTok json) empty).map fun r =>
      s!"ok fulcio={entries r.fulcio fun f => entry f.subject f.publicKey f.window} " ++
      s!"logs={entries r.logs fun l => entry l.origin l.publicKey l.window} " ++
      s!"tsas={entries r.tsas fun t => entry t.signerId t.publicKey t.window}")
  | [_, "accept", level, image, bundle, tuf, pinned] => do
    let r := acceptTufSlot (← parseHexTok image) (← parseHexTok bundle) (← parseHexTok tuf)
      (← parseHexTok pinned) policy (← level.toNat?)
    pure <| okOr (r.map fun (sv, t) => s!"ok {sv} {t}")
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
    IO.eprintln s!"can't parse: {text.take 200}"
    return 1

def main : IO UInt32 := do
  loop (← IO.getStdin) (← IO.getStdout)
