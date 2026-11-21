import C3BootProofs

/-!
Reads the cases that `c3-boot/ota/examples/trust_vectors.rs` prints, one per
line on standard input, evaluates `acceptContents` on each, and prints the
case with the specification's verdict. CI requires the output to equal the
Rust program's.

A signature in a case names the key that made it, the message it covers,
and whether it was corrupted. `verifyCase` accepts it exactly when it is
uncorrupted and made by that key over that message, which is what Ed25519
gives the Rust code for these cases.
-/

open C3

/-- A signature as a case describes it. -/
structure CaseSig where
  signer : Nat
  msg : Option Nat
  corrupt : Bool

def verifyCase (key : Nat) (msg : Option Nat) (s : CaseSig) : Bool :=
  !s.corrupt && s.signer == key && s.msg == msg

def parseSig (text : String) : Option (SigEntry CaseSig) := do
  let corrupt := text.endsWith "!"
  let body := if corrupt then (text.dropEnd 1).toString else text
  match body.splitOn ":" with
  | [i, k, m] =>
    let msg ← if m == "b" then some none else (m.toNat?).map some
    let index ← i.toNat?
    let signer ← k.toNat?
    pure ⟨index, ⟨signer, msg, corrupt⟩⟩
  | _ => none

def parseSigs (text : String) : Option (List (SigEntry CaseSig)) :=
  if text.isEmpty then some [] else (text.splitOn ",").mapM parseSig

def parseLink (i : Nat) (text : String) : Option (Link Nat (Option Nat) CaseSig) :=
  match text.splitOn "/" with
  | [lvl, keys, sigs] => do
    let level ← lvl.toNat?
    let ks ← (keys.splitOn ".").mapM String.toNat?
    let ss ← parseSigs sigs
    pure ⟨level, ks, some i, ss⟩
  | _ => none

def parseLinks (text : String) : Option (List (Link Nat (Option Nat) CaseSig)) :=
  if text == "-" then some []
  else ((text.splitOn ";").zipIdx).mapM fun (t, i) => parseLink i t

def field (pre : String) (tok : String) : Option String :=
  if tok.startsWith pre then some (tok.drop pre.length).toString else none

/-- The specification's verdict on one case, or `none` if the line doesn't
parse. -/
def verdict (tokens : List String) : Option Bool := do
  let [_, l, b, s, e] := tokens | none
  let links ← parseLinks (← field "links=" l)
  let blobText ← field "blob=" b
  let (blevel, bsigs) ← match blobText.splitOn "/" with
    | [lv, ss] => do pure (← lv.toNat?, ← parseSigs ss)
    | _ => none
  let sv ← (← field "sv=" s).toNat?
  let efuse ← (← field "e=" e).toNat?
  let c : Contents Nat (Option Nat) CaseSig := ⟨links, ⟨blevel, none, bsigs⟩, sv, true⟩
  pure (acceptContents verifyCase [0, 1, 2, 3] efuse c).isSome

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let text := line.trimAsciiEnd.toString
  let case := (text.splitOn " | ").headD ""
  match verdict (case.splitOn " ") with
  | some v =>
    stdout.putStrLn s!"{case} | {if v then 1 else 0}"
    loop stdin stdout
  | none =>
    IO.eprintln s!"can't parse: {text}"
    return 1

def main : IO UInt32 := do
  loop (← IO.getStdin) (← IO.getStdout)
