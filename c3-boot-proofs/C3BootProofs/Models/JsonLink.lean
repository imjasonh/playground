import C3BootProofs.Proofs.JsonParseEnd
import C3BootProofs.Proofs.JsonU64
import C3BootProofs.Proofs.JsonStr

/-!
# The JSON position models and `Spec/Json.lean`

The machine-code theorems for `c3_verify::json` are stated with position
models: `parseModel` for `parse`, and `objGet`, `objField`, `strRes`,
`u64Val`, `curOpen`, `nextMember`, and `nextElement` for the functions on a
parsed `Value`, which is a slice of the document. This file relates them to
the grammar in `Spec/Json.lean`.

`JVal c v j` says that the bytes `v` are exactly one value that the spec
parses to `j`. `JDen c doc a l j` says the same of the `l` bytes of `doc`
at `a`, which is how a `Value` slice and its position in the document are
named.

Each `…Stmt` below is the statement of one link theorem. The theorem that
proves it has the same name without `Stmt`.
-/

namespace C3.Json

open C3.RV32 (Word strRes curOpen)

/-- The bytes `v` are exactly one value that the spec parses to `j`, for
some fuel and remaining nesting depth. -/
def JVal (c : Bool) (v : Bytes) (j : Json) : Prop :=
  ∃ fuel depth, parseValue c fuel depth v = some (j, [])

/-- The `l` bytes of `doc` at `a` are one value that the spec parses to
`j`. -/
def JDen (c : Bool) (doc : Bytes) (a l : Nat) (j : Json) : Prop :=
  a + l ≤ doc.length ∧ JVal c (slice doc a l) j

/-- A slice holds at most one value. -/
def JValUniqueStmt : Prop :=
  ∀ c v j j', JVal c v j → JVal c v j' → j = j'

mutual
/-- No object key in `j` has a byte below `0x20`. `next_member` reads a key
with `key_end` in strict mode, which rejects those bytes, while canonical
mode allows them in strings. So the compiled code rejects a canonical
document such as `{"\x01":1}` that `parseJson true` accepts. -/
def noCtlKeys : Json → Bool
  | .obj ms => noCtlMembers ms
  | .arr js => noCtlElems js
  | _ => true

/-- `noCtlKeys` for each member, and no byte below `0x20` in each key. -/
def noCtlMembers : List (Bytes × Json) → Bool
  | [] => true
  | (k, j) :: ms => k.all (fun b => decide (0x20 ≤ b)) && noCtlKeys j && noCtlMembers ms

/-- `noCtlKeys` for each item. -/
def noCtlElems : List Json → Bool
  | [] => true
  | j :: js => noCtlKeys j && noCtlElems js
end

/-- A strict-mode value has no control byte in any key. -/
def StrictNoCtlStmt : Prop :=
  ∀ v j, JVal false v j → noCtlKeys j = true

/-! ## `parse` -/

/-- An `.ok` result of `parse` is the slice of the value that the spec
parses the document to. -/
def ParseModelOkStmt : Prop :=
  ∀ c doc a l, parseModel c doc = .ok (a, l) →
    ∃ j, parseJson c doc = some j ∧ JDen c doc a l j ∧ noCtlKeys j = true

/-- When the spec accepts a document with no control byte in a key, so does
`parse`. -/
def ParseJsonSomeStmt : Prop :=
  ∀ c doc j, parseJson c doc = some j → noCtlKeys j = true →
    ∃ a l, parseModel c doc = .ok (a, l) ∧ JDen c doc a l j

/-- An `.error` result of `parse` means the spec rejects the document, or
accepts it in canonical mode with a control byte in a key. -/
def ParseModelErrorStmt : Prop :=
  ∀ c doc e, parseModel c doc = .error e → ∀ j, parseJson c doc = some j → c = true ∧ noCtlKeys j = false

/-! ## Functions on a `Value` -/

/-- `Value::get(key)` on a value: the error byte `0x21` when it is not an
object, `.ok none` when it has no member `key`, and otherwise the slice of
the first such member's value. -/
def ObjGetStmt : Prop :=
  ∀ c v j key, JVal c v j → noCtlKeys j = true →
    match j.asObj with
    | none => objGet v key = .error 0x21
    | some ms =>
      match ms.lookup key with
      | none => objGet v key = .ok none
      | some j' => ∃ vp vl, objGet v key = .ok (some (vp, vl)) ∧ JDen c v vp vl j'

/-- `Value::field(key)` on a value is `Json.field key`, with the error byte
`0x21` for `none`. -/
def ObjFieldStmt : Prop :=
  ∀ c v j key, JVal c v j → noCtlKeys j = true →
    match j.field key with
    | none => objField v key = .error 0x21
    | some j' => ∃ vp vl, objField v key = .ok (vp, vl) ∧ JDen c v vp vl j'

/-- `Value::str` on a value is `Json.asStr`: the body's address and length,
and the body is the string. -/
def StrResStmt : Prop :=
  ∀ c v j (p : Word), JVal c v j →
    strRes p v = j.asStr.map (fun s => (p + 1, s.length)) ∧
      ∀ s, j.asStr = some s → slice v 1 s.length = s

/-- `Value::u64` on a value is `Json.asNum`. Its `2 ^ 64` check never fails
on a value: the spec reads at most 19 digits, and `10 ^ 19 < 2 ^ 64`. -/
def U64ValStmt : Prop :=
  ∀ c v j, JVal c v j → u64Val v = j.asNum

/-- The cursor over an object (`o = 123`) or an array (`o = 91`) exists
exactly for an object or an array, and starts after `{` or `[` and the
whitespace after it. -/
def CurOpenStmt : Prop :=
  ∀ c v j (p : Word), JVal c v j →
    (curOpen 123 p v).isSome = j.asObj.isSome ∧ (curOpen 91 p v).isSome = j.asArr.isSome ∧
      ∀ x, (curOpen 123 p v = some x ∨ curOpen 91 p v = some x) → x = (p, v.length, skipWs v 1)

/-- `nextMember` from `pos` walks the members `ms` of the object `v`, in
order: each step gives the key's slice, the value's slice, and the position
of the next member, and the last step gives `some none`. -/
def MembersFrom (c : Bool) (v : Bytes) : Nat → List (Bytes × Json) → Prop
  | pos, [] => nextMember v pos = some none
  | pos, (k, j) :: ms => ∃ kp vp vl a, nextMember v pos = some (some (kp, k.length, vp, vl, a)) ∧
      slice v kp k.length = k ∧ JDen c v vp vl j ∧ MembersFrom c v a ms

/-- `nextElement` from `pos` walks the items of the array `v`, in order. -/
def ElementsFrom (c : Bool) (v : Bytes) : Nat → List Json → Prop
  | pos, [] => nextElement v pos = some none
  | pos, j :: js => ∃ l a, nextElement v pos = some (some (pos, l, a)) ∧ JDen c v pos l j ∧ ElementsFrom c v a js

/-- An object's members, walked from the cursor that `curOpen 123` gives. -/
def MembersStmt : Prop :=
  ∀ c v ms, JVal c v (.obj ms) → noCtlMembers ms = true → MembersFrom c v (skipWs v 1) ms

/-- An array's items, walked from the cursor that `curOpen 91` gives. -/
def ElementsStmt : Prop :=
  ∀ c v js, JVal c v (.arr js) → ElementsFrom c v (skipWs v 1) js

/-! ## Keys -/

/-- Every object in a value passed `keysOk`: in canonical mode its keys
strictly increase, and in strict mode they are distinct. -/
def ObjKeysStmt : Prop :=
  ∀ c v ms, JVal c v (.obj ms) → keysOk c (ms.map (·.1)) = true

/-- Increasing keys are distinct. -/
def KeysIncreasingDistinctStmt : Prop :=
  ∀ ks, keysIncreasing ks = true → distinct ks = true

/-- A canonical value is the encoding of what it parses to, so the bytes a
signature covers are `encode` of the signed value. -/
def CanonEncodeStmt : Prop :=
  ∀ v j, JVal true v j → v = encode j

/-! Where the compiled code and the spec differ: a control byte in a
canonical key. -/

#guard (parseJson true [0x7B, 0x22, 0x01, 0x22, 0x3A, 0x31, 0x7D]).isSome
#guard (parseModel true [0x7B, 0x22, 0x01, 0x22, 0x3A, 0x31, 0x7D]).toOption.isNone
#guard (parseJson true [0x7B, 0x22, 0x01, 0x22, 0x3A, 0x31, 0x7D] |>.bind (Json.field [0x01])).isSome
#guard objGet [0x7B, 0x22, 0x01, 0x22, 0x3A, 0x31, 0x7D] [0x01] matches .error _

end C3.Json
