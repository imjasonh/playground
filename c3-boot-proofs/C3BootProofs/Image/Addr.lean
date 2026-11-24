/-!
# Image addresses as names

The proofs name an address in the image by the definition that the
extractor writes for it, such as `p256GAddress`, instead of by its value.
After a rebuild moves the data, the regenerated definitions carry the new
values and the proofs follow them.

`(img% e)` expands to the numeral that `e` evaluates to. `e` is built from
numerals, names the extractor defines, `+`, `-` (truncated, as on `Nat`),
`hi20`, `lo12`, and parentheses. It extends as far as it can, so the proofs
always write the form in parentheses, as in `(img% p256GAddress + 0x20)`.
The kernel sees the same literal that the proof would have written by hand,
so naming an address changes neither what is proved nor how fast it checks,
and `rw`, `simp`, `omega`, and `decide` treat it as the literal they always
did.

Each image file ends with a table of its names and an `imgVal%` rule that
looks a name up in it. A macro keeps this file and
the image files free of `import Lean`, which would add about a gigabyte to
every module's imports.
-/

namespace C3.Image

/-- The value that `lui` loads so that `addi` with `lo12 a` reaches `a`. -/
def hi20 (a : Nat) : Nat := (a + 0x800) / 0x1000 * 0x1000 % 2 ^ 32

/-- The `addi` immediate, sign-extended to 32 bits, that pairs with `hi20 a`. -/
def lo12 (a : Nat) : Nat := if a % 0x1000 < 0x800 then a % 0x1000 else a % 0x1000 + 0xFFFFF000

/-- `imgVal% n` is the numeral that the extractor defines the name `n` as. -/
syntax "imgVal% " ident : term

/-- `(img% e)` is the numeral that `e` evaluates to. -/
syntax "img% " term : term

/-- The value that `names` gives the name `i`, as a numeral, for an
`imgVal%` rule. -/
def imgLookup (names : List (String × Nat)) (i : Lean.TSyntax `ident) : Lean.MacroM Lean.Syntax :=
  match names.lookup (i.getId.replacePrefix `C3.Image .anonymous).toString with
  | some n => return Lean.Syntax.mkNumLit (toString n)
  | none => Lean.Macro.throwUnsupported

/-- The value of an `img%` expression. -/
partial def imgEval : Lean.Syntax → Lean.MacroM Nat
  | `($a + $b) => return (← imgEval a) + (← imgEval b)
  | `($a - $b) => return (← imgEval a) - (← imgEval b)
  | `(($a)) => imgEval a
  | `(hi20 $a) => return hi20 (← imgEval a)
  | `(lo12 $a) => return lo12 (← imgEval a)
  | `($n:num) => return n.getNat
  | `($i:ident) => do
    let some v ← Lean.Macro.expandMacro? (← `(imgVal% $i))
      | Lean.Macro.throwErrorAt i s!"img%: the image defines no address {i.getId}"
    match v.isNatLit? with
    | some n => return n
    | none => Lean.Macro.throwErrorAt i s!"img%: {i.getId} is not a numeral"
  | e => Lean.Macro.throwErrorAt e "img%: expected numerals, names, +, -, hi20, lo12, or parentheses"

macro_rules
  | `(img% $e) => return Lean.Syntax.mkNumLit (toString (← imgEval e))

end C3.Image
