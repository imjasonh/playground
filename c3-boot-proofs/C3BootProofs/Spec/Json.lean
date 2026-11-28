import C3BootProofs.Spec.Formats

/-!
# JSON

The JSON profiles of `c3_verify::json`, as a grammar over a tree of values.

- Strings are raw bytes between quotes, with no backslash. Strict mode also
  rejects control bytes below `0x20`. Canonical mode allows them in string
  values, but object keys never contain them in either mode.
- Numbers are natural numbers of 1 to 19 digits, with no leading zero.
- Containers nest at most 16 deep.
- Canonical mode allows no whitespace and needs each object's keys in
  strictly increasing byte order. Strict mode allows whitespace between
  tokens and needs each object's keys to be distinct.

A canonical document is `encode` of the value it parses to, so the bytes
that a TUF signature covers are `encode` of the `signed` value.
-/

namespace C3

open Lean in
/-- `ascii!"text"`: the bytes of a string literal, as a list of numbers.
The string is read when the term is elaborated, so the term holds only
numerals. -/
macro "ascii!" s:str : term => do
  let lits : Array (TSyntax `term) :=
    s.getString.toUTF8.toList.toArray.map fun b => ⟨Syntax.mkNumLit (toString b.toNat)⟩
  `(([$lits,*] : List Nat))

/-- A JSON value in the profiles. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : Bytes)
  | arr (items : List Json)
  | obj (members : List (Bytes × Json))
  deriving Repr, Inhabited

def isWs (b : Nat) : Bool := b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D

def isDigit (b : Nat) : Bool := 48 ≤ b && b ≤ 57

/-- Skips whitespace, which only strict mode (`canonical = false`) allows. -/
def ws (canonical : Bool) (s : Bytes) : Bytes := if canonical then s else s.dropWhile isWs

/-- A string's bytes up to its closing quote, and the bytes after it. -/
def parseString (canonical : Bool) : Bytes → Option (Bytes × Bytes)
  | [] => none
  | 0x22 :: rest => some ([], rest)
  | b :: rest => do
    require (b != 0x5C && (canonical || b ≥ 0x20))
    let (s, rest) ← parseString canonical rest
    pure (b :: s, rest)

def digitsValue (ds : Bytes) : Nat := ds.foldl (fun n d => 10 * n + (d - 48)) 0

def parseNumber (s : Bytes) : Option (Json × Bytes) := do
  let ds := s.takeWhile isDigit
  require (1 ≤ ds.length && ds.length ≤ 19 && (ds.length == 1 || ds.head? != some 48))
  pure (.num (digitsValue ds), s.drop ds.length)

def parseLiteral (s : Bytes) : Option (Json × Bytes) :=
  match readExpect (ascii!"true") s, readExpect (ascii!"false") s, readExpect (ascii!"null") s with
  | some r, _, _ => some (.bool true, r)
  | _, some r, _ => some (.bool false, r)
  | _, _, some r => some (.null, r)
  | _, _, _ => none

/-- Whether `a` sorts before `b`, byte by byte. -/
def bytesLt : Bytes → Bytes → Bool
  | [], _ :: _ => true
  | a :: as, b :: bs => a < b || (a == b && bytesLt as bs)
  | _, [] => false

def distinct : List Bytes → Bool
  | [] => true
  | k :: ks => !ks.contains k && distinct ks

def keysIncreasing : List Bytes → Bool
  | a :: b :: rest => bytesLt a b && keysIncreasing (b :: rest)
  | _ => true

def keysOk (canonical : Bool) (keys : List Bytes) : Bool :=
  if canonical then keysIncreasing keys else distinct keys

mutual
/-- The value at the front of `s`, where `depth` more containers may open.
Each call reads at least one byte before calling the next, except that
`parseElems` calls `parseValue` at the same position, so `2 * length + 2`
fuel always suffices. -/
def parseValue (c : Bool) : Nat → Nat → Bytes → Option (Json × Bytes)
  | 0, _, _ => none
  | fuel + 1, depth, s =>
    match s with
    | 0x7B :: rest => do
      require (depth ≥ 1)
      match ws c rest with
      | 0x7D :: r => pure (.obj [], r)
      | r => do
        let (ms, r) ← parseMembers c fuel (depth - 1) r
        require (keysOk c (ms.map (·.1)))
        pure (.obj ms, r)
    | 0x5B :: rest => do
      require (depth ≥ 1)
      match ws c rest with
      | 0x5D :: r => pure (.arr [], r)
      | r => do
        let (items, r) ← parseElems c fuel (depth - 1) r
        pure (.arr items, r)
    | 0x22 :: rest => do
      let (str, r) ← parseString c rest
      pure (.str str, r)
    | b :: _ => if isDigit b then parseNumber s else parseLiteral s
    | [] => none

/-- `"key" : value` members up to and including the closing brace. A key is
read as a strict-mode string in both modes. -/
def parseMembers (c : Bool) : Nat → Nat → Bytes → Option (List (Bytes × Json) × Bytes)
  | 0, _, _ => none
  | fuel + 1, depth, s =>
    match s with
    | 0x22 :: rest => do
      let (k, r) ← parseString false rest
      let r ← readExpect [0x3A] (ws c r)
      let (v, r) ← parseValue c fuel depth (ws c r)
      match ws c r with
      | 0x2C :: r => do
        let (more, r) ← parseMembers c fuel depth (ws c r)
        pure ((k, v) :: more, r)
      | 0x7D :: r => pure ([(k, v)], r)
      | _ => none
    | _ => none

/-- Array elements up to and including the closing bracket. -/
def parseElems (c : Bool) : Nat → Nat → Bytes → Option (List Json × Bytes)
  | 0, _, _ => none
  | fuel + 1, depth, s => do
    let (v, r) ← parseValue c fuel depth s
    match ws c r with
    | 0x2C :: r => do
      let (more, r) ← parseElems c fuel depth (ws c r)
      pure (v :: more, r)
    | 0x5D :: r => pure ([v], r)
    | _ => none
end

/-- `json::parse`: the document as one value, in canonical mode or strict
mode. -/
def parseJson (canonical : Bool) (doc : Bytes) : Option Json := do
  let (v, r) ← parseValue canonical (2 * doc.length + 2) 16 (ws canonical doc)
  require (ws canonical r).isEmpty
  pure v

/-- The decimal digits of `n`; `fuel` bounds the digits. -/
def decimal : Nat → Nat → Bytes
  | 0, _ => []
  | fuel + 1, n => (if n < 10 then [] else decimal fuel (n / 10)) ++ [48 + n % 10]

mutual
/-- The canonical encoding of a value. -/
def encode : Json → Bytes
  | .null => ascii!"null"
  | .bool true => ascii!"true"
  | .bool false => ascii!"false"
  | .num n => decimal (n + 1) n
  | .str s => [0x22] ++ s ++ [0x22]
  | .arr items => [0x5B] ++ encodeElems items ++ [0x5D]
  | .obj ms => [0x7B] ++ encodeMembers ms ++ [0x7D]

def encodeElems : List Json → Bytes
  | [] => []
  | [v] => encode v
  | v :: rest => encode v ++ [0x2C] ++ encodeElems rest

def encodeMembers : List (Bytes × Json) → Bytes
  | [] => []
  | [(k, v)] => [0x22] ++ k ++ [0x22, 0x3A] ++ encode v
  | (k, v) :: rest => [0x22] ++ k ++ [0x22, 0x3A] ++ encode v ++ [0x2C] ++ encodeMembers rest
end

/-- An object's value for `key`; `none` when the value isn't an object or
has no such member. -/
def Json.field (key : Bytes) : Json → Option Json
  | .obj ms => ms.lookup key
  | _ => none

def Json.asStr : Json → Option Bytes
  | .str s => some s
  | _ => none

def Json.asNum : Json → Option Nat
  | .num n => some n
  | _ => none

def Json.asArr : Json → Option (List Json)
  | .arr items => some items
  | _ => none

def Json.asObj : Json → Option (List (Bytes × Json))
  | .obj ms => some ms
  | _ => none

def Json.isObj (j : Json) : Bool := j.asObj.isSome

end C3

open C3 in
#guard (parseJson true (ascii!"{\"a\":[1,true,null],\"b\":\"x\"}")).map encode ==
  some (ascii!"{\"a\":[1,true,null],\"b\":\"x\"}")
open C3 in
#guard (parseJson true (ascii!"{\"b\":1,\"a\":2}")).isNone
open C3 in
#guard (parseJson false (ascii!" {\"b\" : 1 , \"a\":[ ]} ")).isSome
open C3 in
#guard (parseJson false (ascii!"{\"a\":1,\"a\":2}")).isNone
open C3 in
#guard (parseJson true (ascii!"[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]")).isSome
open C3 in
#guard (parseJson true (ascii!"[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]")).isNone
open C3 in
#guard (parseJson true (ascii!"01")).isNone
open C3 in
#guard (parseJson true [0x7B, 0x22, 0x01, 0x22, 0x3A, 0x31, 0x7D]).isNone
open C3 in
#guard (parseJson true [0x22, 0x01, 0x22]).isSome
