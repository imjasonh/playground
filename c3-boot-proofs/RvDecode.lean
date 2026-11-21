import C3BootProofs

/-!
Reads one instruction encoding per line, 4 hex digits for a 16-bit
encoding or 8 for a 32-bit one, and prints it with `valid` if the Lean
RV32 decoder accepts it and `invalid` otherwise. `scripts/decode-vs-llvm.py`
compares the result with LLVM's RISC-V disassembler.
-/

open C3.RV32

def hexValue (s : String) : Option Nat :=
  s.toList.foldlM (fun acc c =>
    if '0' ≤ c && c ≤ '9' then some (16 * acc + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * acc + (c.toNat - 'a'.toNat + 10))
    else none) 0

def classify (s : String) : Option String := do
  let v ← hexValue s
  let ok := match s.length with
    | 4 => if v % 4 == 3 then none else some (decode16 v).isSome
    | 8 => if v % 4 == 3 then some (decode32 v).isSome else none
    | _ => none
  pure (if (← ok) then "valid" else "invalid")

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let s := line.trimAscii.toString
  match classify s with
  | some r =>
    stdout.putStrLn s!"{s} {r}"
    loop stdin stdout
  | none =>
    IO.eprintln s!"can't parse: {s}"
    return 1

def main : IO UInt32 := do
  loop (← IO.getStdin) (← IO.getStdout)
