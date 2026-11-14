import C3BootProofs

/-!
Reads the lines that `c3-boot/verify/examples/decode_vectors.rs` prints,
decodes each input with the Lean specification, and prints the line with
the specification's result. CI requires the output to equal the Rust
program's.
-/

open C3

def showSlot : Slot → String
  | .a => "A"
  | .b => "B"

def showState (s : State) : String :=
  let t := match s.trial with
    | some t => showSlot t.slot ++ toString t.bootsLeft
    | none => "-"
  s!"g={s.generation} p={showSlot s.preferred} t={t} c={s.confirmed}"

def showPart (p : Part) : String := s!"{p.offset},{p.length}"

def kindDigit : SegmentKind → Nat
  | .flashCode => 1
  | .flashData => 2
  | .ramCode => 3
  | .ramData => 4

def showSegment (s : Segment) : String :=
  s!"{kindDigit s.kind}@{s.address}+{s.offset}:{s.length}"

/-- The specification's result for one input, or `none` if the line doesn't
parse. -/
def result (tokens : List String) : Option String :=
  match tokens with
  | ["record", h] => do
    let bytes ← parseHexTok h
    pure <| match decodeRecord bytes with
      | some s => s!"ok {showState s}"
      | none => "err"
  | ["read", ha, hb] => do
    let a ← parseHexTok ha
    let b ← parseHexTok hb
    let (s, copy) := readRecords a b
    let c := match copy with
      | some slot => showSlot slot
      | none => "-"
    pure s!"{showState s} copy={c}"
  | ["manifest", h] => do
    let bytes ← parseHexTok h
    pure <| match decodeManifest bytes with
      | some m =>
        s!"ok i={showPart m.image} b={showPart m.bundle} c={showPart m.chain} l={showPart m.blob}"
      | none => "err"
  | ["image", len, h] => do
    let n ← len.toNat?
    let bytes ← parseHexTok h
    pure <| match decodeImageHeader bytes n with
      | some hdr =>
        let segs := ",".intercalate (hdr.segments.map showSegment)
        s!"ok sv={hdr.securityVersion} e={hdr.entryPoint} segs={segs}"
      | none => "err"
  | ["sha256", h] => do
    let bytes ← parseHexTok h
    pure (hexStr (sha256 bytes))
  | ["merkle", i, s, l, p] => do
    let index ← i.toNat?
    let size ← s.toNat?
    let leaf ← parseHexTok l
    let proof ← parseHexTok p
    pure <| match rootFromInclusion index size leaf proof with
      | some r => s!"ok {hexStr r}"
      | none => "err"
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
