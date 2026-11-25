import C3BootProofs.Models.JsonLink

/-!
# The lax grammar for the JSON link

`jlxValue`, `jlxMembers`, and `jlxElems` are the grammar of
`Spec/Json.lean` with one change: they read an object key in the mode of
the document, as `parse`'s scan does, so a canonical key may hold a control
byte. `parse` rejects such a key only when it checks the object's keys,
after reading the rest of the object, so its proofs follow this grammar.
`JsonLinkFilter.lean` shows that the spec accepts exactly the values of this
grammar with no control byte in a key (`noCtlKeys`).

The `jlx…Stmt` statements are the link statements for this grammar. The
link theorems for the spec follow from them.
-/

namespace C3.Json

open C3
open C3.RV32 (Word strRes curOpen)

mutual
def jlxValue (c : Bool) : Nat → Nat → Bytes → Option (Json × Bytes)
  | 0, _, _ => none
  | fuel + 1, depth, s =>
    match s with
    | 0x7B :: rest => do
      require (depth ≥ 1)
      match ws c rest with
      | 0x7D :: r => pure (.obj [], r)
      | r => do
        let (ms, r) ← jlxMembers c fuel (depth - 1) r
        require (keysOk c (ms.map (·.1)))
        pure (.obj ms, r)
    | 0x5B :: rest => do
      require (depth ≥ 1)
      match ws c rest with
      | 0x5D :: r => pure (.arr [], r)
      | r => do
        let (items, r) ← jlxElems c fuel (depth - 1) r
        pure (.arr items, r)
    | 0x22 :: rest => do
      let (st, r) ← parseString c rest
      pure (.str st, r)
    | b :: _ => if isDigit b then parseNumber s else parseLiteral s
    | [] => none

def jlxMembers (c : Bool) : Nat → Nat → Bytes → Option (List (Bytes × Json) × Bytes)
  | 0, _, _ => none
  | fuel + 1, depth, s =>
    match s with
    | 0x22 :: rest => do
      let (k, r) ← parseString c rest
      let r ← readExpect [0x3A] (ws c r)
      let (v, r) ← jlxValue c fuel depth (ws c r)
      match ws c r with
      | 0x2C :: r => do
        let (more, r) ← jlxMembers c fuel depth (ws c r)
        pure ((k, v) :: more, r)
      | 0x7D :: r => pure ([(k, v)], r)
      | _ => none
    | _ => none

def jlxElems (c : Bool) : Nat → Nat → Bytes → Option (List Json × Bytes)
  | 0, _, _ => none
  | fuel + 1, depth, s => do
    let (v, r) ← jlxValue c fuel depth s
    match ws c r with
    | 0x2C :: r => do
      let (more, r) ← jlxElems c fuel depth (ws c r)
      pure (v :: more, r)
    | 0x5D :: r => pure ([v], r)
    | _ => none
end

def jlxJson (canonical : Bool) (doc : Bytes) : Option Json := do
  let (v, r) ← jlxValue canonical (2 * doc.length + 2) 16 (ws canonical doc)
  require (ws canonical r).isEmpty
  pure v

mutual
/-- No object key in `j` has a byte below `0x20`. -/
def noCtlKeys : Json → Bool
  | .obj ms => noCtlMembers ms
  | .arr js => noCtlElems js
  | _ => true

def noCtlMembers : List (Bytes × Json) → Bool
  | [] => true
  | (k, j) :: ms => k.all (fun b => decide (0x20 ≤ b)) && noCtlKeys j && noCtlMembers ms

def noCtlElems : List Json → Bool
  | [] => true
  | j :: js => noCtlKeys j && noCtlElems js
end

def JValX (c : Bool) (v : Bytes) (j : Json) : Prop :=
  ∃ fuel depth, jlxValue c fuel depth v = some (j, [])

def JDenX (c : Bool) (doc : Bytes) (a l : Nat) (j : Json) : Prop :=
  a + l ≤ doc.length ∧ JValX c (slice doc a l) j

def jlxJValUniqueStmt : Prop :=
  ∀ c v j j', JValX c v j → JValX c v j' → j = j'

def jlxStrictNoCtlStmt : Prop :=
  ∀ v j, JValX false v j → noCtlKeys j = true

def jlxParseModelOkStmt : Prop :=
  ∀ c doc a l, parseModel c doc = .ok (a, l) →
    ∃ j, jlxJson c doc = some j ∧ JDenX c doc a l j ∧ noCtlKeys j = true

def jlxParseJsonSomeStmt : Prop :=
  ∀ c doc j, jlxJson c doc = some j → noCtlKeys j = true →
    ∃ a l, parseModel c doc = .ok (a, l) ∧ JDenX c doc a l j

def jlxParseModelErrorStmt : Prop :=
  ∀ c doc e, parseModel c doc = .error e → ∀ j, jlxJson c doc = some j → c = true ∧ noCtlKeys j = false

def jlxObjGetStmt : Prop :=
  ∀ c v j key, JValX c v j → noCtlKeys j = true →
    match j.asObj with
    | none => objGet v key = .error 0x21
    | some ms =>
      match ms.lookup key with
      | none => objGet v key = .ok none
      | some j' => ∃ vp vl, objGet v key = .ok (some (vp, vl)) ∧ JDenX c v vp vl j'

def jlxObjFieldStmt : Prop :=
  ∀ c v j key, JValX c v j → noCtlKeys j = true →
    match j.field key with
    | none => objField v key = .error 0x21
    | some j' => ∃ vp vl, objField v key = .ok (vp, vl) ∧ JDenX c v vp vl j'

def jlxStrResStmt : Prop :=
  ∀ c v j (p : Word), JValX c v j →
    strRes p v = j.asStr.map (fun s => (p + 1, s.length)) ∧
      ∀ s, j.asStr = some s → slice v 1 s.length = s

def jlxU64ValStmt : Prop :=
  ∀ c v j, JValX c v j → u64Val v = j.asNum

def jlxCurOpenStmt : Prop :=
  ∀ c v j (p : Word), JValX c v j →
    (curOpen 123 p v).isSome = j.asObj.isSome ∧ (curOpen 91 p v).isSome = j.asArr.isSome ∧
      ∀ x, (curOpen 123 p v = some x ∨ curOpen 91 p v = some x) → x = (p, v.length, skipWs v 1)

def MembersFromX (c : Bool) (v : Bytes) : Nat → List (Bytes × Json) → Prop
  | pos, [] => nextMember v pos = some none
  | pos, (k, j) :: ms => ∃ kp vp vl a, nextMember v pos = some (some (kp, k.length, vp, vl, a)) ∧
      slice v kp k.length = k ∧ JDenX c v vp vl j ∧ MembersFromX c v a ms

def ElementsFromX (c : Bool) (v : Bytes) : Nat → List Json → Prop
  | pos, [] => nextElement v pos = some none
  | pos, j :: js => ∃ l a, nextElement v pos = some (some (pos, l, a)) ∧ JDenX c v pos l j ∧ ElementsFromX c v a js

def jlxMembersStmt : Prop :=
  ∀ c v ms, JValX c v (.obj ms) → noCtlMembers ms = true → MembersFromX c v (skipWs v 1) ms

def jlxElementsStmt : Prop :=
  ∀ c v js, JValX c v (.arr js) → ElementsFromX c v (skipWs v 1) js

def jlxObjKeysStmt : Prop :=
  ∀ c v ms, JValX c v (.obj ms) → keysOk c (ms.map (·.1)) = true

def jlxCanonEncodeStmt : Prop :=
  ∀ v j, JValX true v j → v = encode j

end C3.Json
