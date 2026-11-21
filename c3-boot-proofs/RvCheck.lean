import C3BootProofs

/-!
Reads lockstep cases, one per line on standard input:

`rv SEQ CODE REGS MEM | OUTREGS OUTMEM`

`SEQ` is the address where QEMU ran the sequence, `CODE` its bytes, `REGS`
the initial `x1` through `x31` (8 hex digits each), and `MEM` the initial
256 bytes of the buffer at `0x3FC80000`. `OUTREGS` and `OUTMEM` are what
QEMU ended with. The Lean model runs the same sequence from the same state
and prints the line with its own results, so CI can compare the two.
-/

open C3.RV32

def bufBase : Nat := 0x3FC80000

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def parseBytes : List Char → Option (List Nat)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexDigit a
    let lo ← hexDigit b
    pure ((16 * hi + lo) :: (← parseBytes rest))
  | [_] => none

partial def parseWords : List Char → Option (List Nat)
  | [] => some []
  | cs => do
    let digits ← (cs.take 8).mapM hexDigit
    if digits.length != 8 then none
    let v := digits.foldl (fun acc d => 16 * acc + d) 0
    pure (v :: (← parseWords (cs.drop 8)))

def hex8 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - s.length) '0') ++ s

def hex2 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  if s.length < 2 then "0" ++ s else s

/-- Runs one case and returns the registers and buffer it ends with, or
`none` if the model traps or runs out of fuel. -/
def runCase (seq : Nat) (code : Array Nat) (regs : Array Nat) (buf : Array Nat) :
    Option String := do
  let start : Word := BitVec.ofNat 32 seq
  let mem : Word → BitVec 8 := fun a =>
    let n := a.toNat
    if seq ≤ n ∧ n < seq + code.size then BitVec.ofNat 8 (code.getD (n - seq) 0)
    else if bufBase ≤ n ∧ n < bufBase + 256 then BitVec.ofNat 8 (buf.getD (n - bufBase) 0)
    else 0
  let m : Machine := {
    regs := fun i => if i.val = 0 then 0 else BitVec.ofNat 32 (regs.getD (i.val - 1) 0)
    pc := start
    mem := mem }
  let final ← runTo (start + BitVec.ofNat 32 code.size) 2000 m
  let rs := (List.range 31).map fun i => hex8 (reg final (regOf (i + 1))).toNat
  let bs := (List.range 256).map fun i => hex2 (load8 final (BitVec.ofNat 32 (bufBase + i))).toNat
  pure s!"{String.join rs} {String.join bs}"

def check (tokens : List String) : Option String := do
  let ["rv", seqHex, codeHex, regsHex, memHex] := tokens | none
  let seq ← (← parseWords seqHex.toList).head?
  let code ← parseBytes codeHex.toList
  let regs ← parseWords regsHex.toList
  let buf ← parseBytes memHex.toList
  if regs.length != 31 || buf.length != 256 then none
  pure ((runCase seq code.toArray regs.toArray buf.toArray).getD "trap")

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let text := line.trimAsciiEnd.toString
  let input := (text.splitOn " | ").headD ""
  match check (input.splitOn " ") with
  | some r =>
    stdout.putStrLn s!"{input} | {r}"
    loop stdin stdout
  | none =>
    IO.eprintln s!"can't parse: {text.take 120}"
    return 1

def main : IO UInt32 := do
  loop (← IO.getStdin) (← IO.getStdout)
