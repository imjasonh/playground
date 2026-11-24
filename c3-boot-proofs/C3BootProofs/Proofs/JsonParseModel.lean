import C3BootProofs.Proofs.JsonField

/-!
# `json::parse` by positions

`parse` reads a document in one pass with a stack of at most 16 open
containers. The functions here follow the compiled code's passes:
`parseLoop` reads one value per pass, and `closeLoop` reads the closing
brackets and the comma after it. `checkKeys` is `check_keys`, which
`parse` runs on each object as it closes.

All of them work on the document's bytes and positions as natural
numbers. The result of `parseModel` is the value's start and length, or
the error byte: `0x20` (`TufError::Json`) for every syntax error.
-/

namespace C3.Json

/-- The `l` bytes of `d` from `a`. -/
abbrev slice (d : Bytes) (a l : Nat) : Bytes := (d.drop a).take l

/-- The scan in strict `check_keys`: `u` and whether no member from `pos`
has the key `key`. -/
def keysUnique (o key : Bytes) : Nat → Bool → Nat → Except Nat Bool
  | 0, u, _ => .ok u
  | k + 1, u, pos =>
    match nextMember o pos with
    | none => .error 0x20
    | some none => .ok u
    | some (some (kp, kl, _, _, a)) => keysUnique o key k (u && decide (slice o kp kl ≠ key)) a

/-- Strict `check_keys` from the member at `pos`: no key repeats. -/
def keysStrict (o : Bytes) : Nat → Nat → Except Nat Unit
  | 0, _ => .ok ()
  | k + 1, pos =>
    match nextMember o pos with
    | none => .error 0x20
    | some none => .ok ()
    | some (some (kp, kl, _, _, a)) =>
      match keysUnique o (slice o kp kl) (o.length + 1) true a with
      | .error e => .error e
      | .ok u => if u then keysStrict o k a else .error 0x20

/-- Canonical `check_keys` from the member at `pos`, after the key `prev`:
the keys increase. -/
def keysCanon (o : Bytes) : Nat → Option Bytes → Nat → Except Nat Unit
  | 0, _, _ => .ok ()
  | k + 1, prev, pos =>
    match nextMember o pos with
    | none => .error 0x20
    | some none => .ok ()
    | some (some (kp, kl, _, _, a)) =>
      match prev with
      | none => keysCanon o k (some (slice o kp kl)) a
      | some pk => if bytesLt pk (slice o kp kl) then keysCanon o k (some (slice o kp kl)) a else .error 0x20

/-- `check_keys` on the object `o`. -/
def checkKeys (c : Bool) (o : Bytes) : Except Nat Unit :=
  if o.length = 0 ∨ o.getD 0 0 ≠ 123 then .error 0x21
  else if c then keysCanon o (o.length + 1) none (skipWs o 1)
  else keysStrict o (o.length + 1) (skipWs o 1)

/-- How a pass of `closeLoop` ends: the document's value from `a` to `e`, or
the next value to read at `pos` with the stack `stk`. -/
inductive PStep where
  | done (a e : Nat)
  | cont (stk : List (Bool × Nat)) (pos : Nat)

/-- The closing loop at `pos`, with `j` of its 17 passes left. Each stack
entry is whether the container is an object, and its start. -/
def closeLoop (c : Bool) (d : Bytes) (start : Nat) : Nat → List (Bool × Nat) → Nat → Except Nat PStep
  | 0, stk, pos => .ok (.cont stk pos)
  | j + 1, stk, pos =>
    match stk.getLast? with
    | none =>
      if wsIn c d pos ≠ d.length ∨ pos < start ∨ d.length < pos then .error 0x20 else .ok (.done start pos)
    | some (ob, st) =>
      if d.length ≤ wsIn c d pos then .error 0x20
      else if d.getD (wsIn c d pos) 0 = 93 then
        if ob then .error 0x20 else closeLoop c d start j stk.dropLast (wsIn c d pos + 1)
      else if d.getD (wsIn c d pos) 0 = 125 then
        if ob then
          if wsIn c d pos + 1 < st then .error 0x20
          else match checkKeys c (slice d st (wsIn c d pos + 1 - st)) with
            | .error e => .error e
            | .ok () => closeLoop c d start j stk.dropLast (wsIn c d pos + 1)
        else .error 0x20
      else if d.getD (wsIn c d pos) 0 = 44 then
        if ob then
          match keyEnd c d (wsIn c d (wsIn c d pos + 1)) with
          | none => .error 0x20
          | some v => .ok (.cont stk v)
        else .ok (.cont stk (wsIn c d (wsIn c d pos + 1)))
      else .error 0x20

/-- The parse after a closing loop: its value's start and length, its error,
or `next` from where it stopped. -/
def afterClose (r : Except Nat PStep) (next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)) :
    Except Nat (Nat × Nat) :=
  match r with
  | .error e => .error e
  | .ok (.done a e) => .ok (a, e - a)
  | .ok (.cont stk p) => next stk p

/-- The value pass at `pos`, with `k` of the document's passes left. -/
def parseLoop (c : Bool) (d : Bytes) (start : Nat) : Nat → List (Bool × Nat) → Nat → Except Nat (Nat × Nat)
  | 0, _, _ => .error 0x20
  | k + 1, stk, pos =>
    if d.length ≤ pos then .error 0x20
    else if d.getD pos 0 = 34 then
      match stringEnd c d pos with
      | none => .error 0x20
      | some e => afterClose (closeLoop c d start 17 stk e) (parseLoop c d start k)
    else if d.getD pos 0 = 91 ∨ d.getD pos 0 = 123 then
      if 16 ≤ stk.length then .error 0x20
      else if d.getD pos 0 = 91 then
        if wsIn c d (pos + 1) < d.length ∧ d.getD (wsIn c d (pos + 1)) 0 = 93 then
          afterClose (closeLoop c d start 17 (stk ++ [(false, pos)]) (wsIn c d (pos + 1))) (parseLoop c d start k)
        else parseLoop c d start k (stk ++ [(false, pos)]) (wsIn c d (pos + 1))
      else if wsIn c d (pos + 1) < d.length ∧ d.getD (wsIn c d (pos + 1)) 0 = 125 then
        afterClose (closeLoop c d start 17 (stk ++ [(true, pos)]) (wsIn c d (pos + 1))) (parseLoop c d start k)
      else
        match keyEnd c d (wsIn c d (pos + 1)) with
        | none => .error 0x20
        | some v => parseLoop c d start k (stk ++ [(true, pos)]) v
    else if d.getD pos 0 = 102 ∨ d.getD pos 0 = 110 ∨ d.getD pos 0 = 116 then
      match literalEnd d pos with
      | none => .error 0x20
      | some e => afterClose (closeLoop c d start 17 stk e) (parseLoop c d start k)
    else if isDigit (d.getD pos 0) then
      match numberEnd d pos with
      | none => .error 0x20
      | some e => afterClose (closeLoop c d start 17 stk e) (parseLoop c d start k)
    else .error 0x20

/-- `parse(doc, mode)`, with `c` for canonical mode: the value's start and
length, or the error byte. -/
def parseModel (c : Bool) (d : Bytes) : Except Nat (Nat × Nat) :=
  parseLoop c d (wsIn c d 0) (d.length + 1) [] (wsIn c d 0)

open C3 in
#guard (parseModel true (ascii!"{\"a\":[1,true,null],\"b\":\"x\"}")).toOption == some (0, 27)
open C3 in
#guard (parseModel true (ascii!"{\"b\":1,\"a\":2}")).toOption == none
open C3 in
#guard (parseModel false (ascii!" {\"b\" : 1 , \"a\":[ ]} ")).toOption == some (1, 19)
open C3 in
#guard (parseModel false (ascii!"{\"a\":1,\"a\":2}")).toOption == none
open C3 in
#guard (parseModel true (ascii!"[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]")).toOption == some (0, 32)
open C3 in
#guard (parseModel true (ascii!"[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]")).toOption == none
open C3 in
#guard (parseModel true (ascii!"01")).toOption == none

end C3.Json
