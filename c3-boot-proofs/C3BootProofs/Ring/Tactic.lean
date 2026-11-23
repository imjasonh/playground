import Lean
import C3BootProofs.Ring.Basic

/-!
# `ring_eq` and `ring_mod`: polynomial identities by kernel computation

Two tactics that prove polynomial identities over `Int` and `Nat` without
`Classical.choice`: every proof they build depends only on `propext`. Each
reifies both sides of the goal into `C3.Ring.Expr`, normalizes them with
`Expr.toPoly`, and has the kernel check that the normal forms are equal by
evaluating `Poly.beq` to `true`. The soundness theorem, `toPoly_sound`, is
in `C3BootProofs.Ring.Basic`.

## `ring_eq`

`ring_eq` proves `a = b` over `Int` or `Nat` when the two sides are equal
as polynomials. The sides can use `+`, `*`, `^` with a numeral exponent,
numerals, and, over `Int`, `-` and negation. Anything else is an atom:
a variable, a function application, a cast, or a `^` whose exponent isn't a
numeral. Atoms are identified up to reducible definitional equality.

```
example (x y : Int) : (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by ring_eq
example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring_eq
```

Over `Nat`, `-` and `/` are atoms, so an identity that needs truncated
subtraction to cancel fails. To prove one, cast the goal to `Int` first
(`Int.ofNat.inj`), and state the subtraction there.

## `ring_mod`

`ring_mod` proves `a % n = b % n` or `a % n = 0`, over `Int` or `Nat`,
when `a - b` is a polynomial whose coefficients are all multiples of `n`.
It normalizes both sides with coefficients reduced modulo `n`, so `n` has
to reduce to a numeral: a literal, or a constant defined as one. Large
constants, such as a 256-bit prime, are fine.

```
example (x : Int) : (x + 7) ^ 2 % 7 = x ^ 2 % 7 := by ring_mod
example (x : Nat) : (x + 7) ^ 2 % 7 = x ^ 2 % 7 := by ring_mod
```

Over `Int`, `ring_mod [h₁ * c₁, …, hₖ * cₖ]` also uses hypotheses
`hᵢ : Eᵢ % n = 0`, such as curve equations, with cofactors `cᵢ`. It proves
the goal when `a - b - (E₁ * c₁ + … + Eₖ * cₖ)` has all coefficients
multiples of `n`. Each `hᵢ` is a term at argument precedence (a name, or a
term in parentheses), and each `cᵢ` is any `Int` term over the goal's
variables. `scripts/ring-cofactors.py` computes cofactors by multivariate
division modulo `n` and prints them as Lean terms:

```
example (x₁ y₁ x₂ y₂ : Int)
    (h₁ : (y₁ ^ 2 - x₁ ^ 3 - 7) % 101 = 0) (h₂ : (y₂ ^ 2 - x₂ ^ 3 - 7) % 101 = 0) :
    (y₁ ^ 2 * y₂ ^ 2) % 101 = ((x₁ ^ 3 + 7) * (x₂ ^ 3 + 7)) % 101 := by
  ring_mod [h₁ * (y₂ ^ 2), h₂ * (x₁ ^ 3 + 7)]
```

`C3.Ring.emod_eq_of_sub_eq_mul` takes the other form of certificate,
`a - b = k * n`, which `ring_eq` proves:

```
example (x : Int) : (x * 7 + 3) % 7 = 3 % 7 :=
  C3.Ring.emod_eq_of_sub_eq_mul (k := x) (by ring_eq)
```

## Failures and cost

Before calling the kernel, each tactic runs the same normalizer as compiled
code. When the sides differ, it fails with the normalized difference, in
terms of the atoms it found. The kernel check is a separate auxiliary
theorem, added with `mkAuxLemma`, so a repeated check is reused.

The kernel's cost grows with the number of terms the normal forms and
their intermediate products reach, and only mildly with coefficient size,
because the kernel does `Nat` arithmetic with GMP. `C3BootProofs.Ring.Test`
records timings.
-/

namespace C3.Ring

open Lean Meta Elab Tactic

/-! ## Lean terms for reflected syntax -/

/-- An `Int` value as constructors applied to raw literals. -/
def intToLean (c : Int) : Lean.Expr :=
  match c with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

/-- The Lean term for an `Expr`. -/
def Expr.toLean : Expr → Lean.Expr
  | .const c => mkApp (mkConst ``Expr.const) (intToLean c)
  | .var i => mkApp (mkConst ``Expr.var) (mkRawNatLit i)
  | .add a b => mkApp2 (mkConst ``Expr.add) a.toLean b.toLean
  | .sub a b => mkApp2 (mkConst ``Expr.sub) a.toLean b.toLean
  | .neg a => mkApp (mkConst ``Expr.neg) a.toLean
  | .mul a b => mkApp2 (mkConst ``Expr.mul) a.toLean b.toLean
  | .pow a k => mkApp2 (mkConst ``Expr.pow) a.toLean (mkRawNatLit k)

/-- The Lean term for an `NExpr`. -/
def NExpr.toLean : NExpr → Lean.Expr
  | .const c => mkApp (mkConst ``NExpr.const) (mkRawNatLit c)
  | .var i => mkApp (mkConst ``NExpr.var) (mkRawNatLit i)
  | .add a b => mkApp2 (mkConst ``NExpr.add) a.toLean b.toLean
  | .mul a b => mkApp2 (mkConst ``NExpr.mul) a.toLean b.toLean
  | .pow a k => mkApp2 (mkConst ``NExpr.pow) a.toLean (mkRawNatLit k)

/-! ## Reification -/

/-- The atoms found so far. -/
abbrev ReifyM := StateRefT (Array Lean.Expr) MetaM

/-- The index of `e` among the atoms, adding it if it is new. -/
def atomIndex (e : Lean.Expr) : ReifyM Nat := do
  let atoms ← getThe (Array Lean.Expr)
  for h : i in [:atoms.size] do
    if ← withReducible (isDefEq atoms[i] e) then
      return i
  modifyThe (Array Lean.Expr) (·.push e)
  return atoms.size

/-- A raw numeral: a literal, or `OfNat.ofNat` of one. -/
def rawNat? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg! with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- The value of a closed `Int` or `Nat` term that reduces to a numeral. -/
partial def evalLit? (e : Lean.Expr) : MetaM (Option Int) := do
  let e ← whnf e
  if let .lit (.natVal n) := e then return some n
  match e.getAppFnArgs with
  | (``Int.ofNat, #[x]) => return (← evalLit? x).map id
  | (``Int.negSucc, #[x]) => return (← evalLit? x).map (fun v => -v - 1)
  | _ => return none

/-- An atom, or a numeral when `e` is a global constant that reduces to one. -/
def atomOrConst (e : Lean.Expr) : ReifyM (Sum Nat Int) := do
  if e.isConst then
    if let some v ← evalLit? e then
      return .inr v
  return .inl (← atomIndex e)

/-- Whether `inst` is the instance that `cls` synthesizes. -/
def isStdInst (inst cls : Lean.Expr) : MetaM Bool := do
  let some std ← synthInstance? cls | return false
  if inst == std then return true
  withReducibleAndInstances (isDefEq inst std)

/-- Reifies an `Int` expression. -/
partial def reifyInt (e : Lean.Expr) : ReifyM Expr := do
  let int := mkConst ``Int
  let nat := mkConst ``Nat
  let binop (cls : Name) (a b : Lean.Expr) (inst : Lean.Expr)
      (k : Expr → Expr → Expr) : ReifyM Expr := do
    if ← isStdInst inst (mkApp3 (mkConst cls [0, 0, 0]) int int int) then
      return k (← reifyInt a) (← reifyInt b)
    else
      return .var (← atomIndex e)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, inst, a, b]) =>
    if α.isConstOf ``Int then binop ``HAdd a b inst .add else return .var (← atomIndex e)
  | (``HSub.hSub, #[α, _, _, inst, a, b]) =>
    if α.isConstOf ``Int then binop ``HSub a b inst .sub else return .var (← atomIndex e)
  | (``HMul.hMul, #[α, _, _, inst, a, b]) =>
    if α.isConstOf ``Int then binop ``HMul a b inst .mul else return .var (← atomIndex e)
  | (``Neg.neg, #[α, inst, a]) =>
    if α.isConstOf ``Int && (← isStdInst inst (mkApp (mkConst ``Neg [0]) int)) then
      return .neg (← reifyInt a)
    else return .var (← atomIndex e)
  | (``HPow.hPow, #[α, β, _, inst, a, k]) =>
    match rawNat? k with
    | some k =>
      if α.isConstOf ``Int && β.isConstOf ``Nat &&
          (← isStdInst inst (mkApp3 (mkConst ``HPow [0, 0, 0]) int nat int)) then
        return .pow (← reifyInt a) k
      else return .var (← atomIndex e)
    | none => return .var (← atomIndex e)
  | (``OfNat.ofNat, #[α, _, inst]) =>
    match rawNat? e with
    | some n =>
      if α.isConstOf ``Int &&
          (← isStdInst inst (mkApp2 (mkConst ``OfNat [0]) int (mkRawNatLit n))) then
        return .const n
      else return .var (← atomIndex e)
    | none => return .var (← atomIndex e)
  | _ =>
    match ← atomOrConst e with
    | .inl i => return .var i
    | .inr v => return .const v

/-- Reifies a `Nat` expression. -/
partial def reifyNat (e : Lean.Expr) : ReifyM NExpr := do
  let nat := mkConst ``Nat
  let binop (cls : Name) (a b : Lean.Expr) (inst : Lean.Expr)
      (k : NExpr → NExpr → NExpr) : ReifyM NExpr := do
    if ← isStdInst inst (mkApp3 (mkConst cls [0, 0, 0]) nat nat nat) then
      return k (← reifyNat a) (← reifyNat b)
    else
      return .var (← atomIndex e)
  if let .lit (.natVal n) := e then
    return .const n
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, _, _, inst, a, b]) =>
    if α.isConstOf ``Nat then binop ``HAdd a b inst .add else return .var (← atomIndex e)
  | (``HMul.hMul, #[α, _, _, inst, a, b]) =>
    if α.isConstOf ``Nat then binop ``HMul a b inst .mul else return .var (← atomIndex e)
  | (``HPow.hPow, #[α, β, _, inst, a, k]) =>
    match rawNat? k with
    | some k =>
      if α.isConstOf ``Nat && β.isConstOf ``Nat &&
          (← isStdInst inst (mkApp3 (mkConst ``HPow [0, 0, 0]) nat nat nat)) then
        return .pow (← reifyNat a) k
      else return .var (← atomIndex e)
    | none => return .var (← atomIndex e)
  | (``OfNat.ofNat, #[α, _, inst]) =>
    match rawNat? e with
    | some n =>
      if α.isConstOf ``Nat &&
          (← isStdInst inst (mkApp2 (mkConst ``OfNat [0]) nat (mkRawNatLit n))) then
        return .const n
      else return .var (← atomIndex e)
    | none => return .var (← atomIndex e)
  | _ =>
    match ← atomOrConst e with
    | .inl i => return .var i
    | .inr v => if 0 ≤ v then return .const v.toNat else return .var (← atomIndex e)

/-! ## Checking -/

/-- A polynomial for an error message, with the atoms printed. -/
def Poly.toMessage (atoms : Array Lean.Expr) (p : Poly) (limit : Nat := 12) : MessageData :=
  let rec mon : Mon → List MessageData
    | .one => []
    | .cons x k m =>
      let a := m!"{atoms.getD x (mkConst `atom)}"
      (if k == 1 then a else m!"{a} ^ {k}") :: mon m
  let rec terms : Poly → Nat → List MessageData
    | .zero, _ => []
    | .term _ _ _, 0 => [m!"…"]
    | .term c m p, fuel + 1 =>
      let ms := mon m
      let t := if ms.isEmpty then m!"{c}"
        else if c == 1 then MessageData.joinSep ms " * "
        else MessageData.joinSep (m!"{c}" :: ms) " * "
      t :: terms p fuel
  let rec count : Poly → Nat
    | .zero => 0
    | .term _ _ p => count p + 1
  match p with
  | .zero => m!"0"
  | _ =>
    let k := count p
    m!"{MessageData.joinSep (terms p limit) " + "}\n({k} {if k == 1 then "term" else "terms"})"

/-- Has the kernel check `Poly.beq lhs rhs = true`, as a new auxiliary
theorem, and returns that theorem. -/
def kernelCheck (tactic : String) (lhs rhs : Lean.Expr) : MetaM Lean.Expr := do
  let bool := mkConst ``Bool
  let ty := mkApp3 (mkConst ``Eq [1]) bool (mkApp2 (mkConst ``Poly.beq) lhs rhs)
    (mkConst ``Bool.true)
  let pf := mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true)
  try
    let name ← withOptions (Elab.async.set · false) (mkAuxLemma [] ty pf)
    return mkConst name
  catch ex =>
    throwError "{tactic} failed: the kernel did not reduce the normal-form \
      comparison to `true`:{indentD ex.toMessageData}"

/-- Fails with the normalized difference when `e₁` and `e₂` don't have
equal normal forms modulo `n`. -/
def precheck (tactic : String) (atoms : Array Lean.Expr) (n : Int) (e₁ e₂ : Expr) :
    MetaM Unit := do
  unless Poly.beq (e₁.toPoly n) (e₂.toPoly n) do
    let diff := (Expr.sub e₁ e₂).toPoly n
    let modulo := if n == 0 then m!"" else m!", modulo {n},"
    throwError "{tactic} failed: the left side minus the right side{modulo} \
      normalizes to{indentD (diff.toMessage atoms)}"

/-! ## `ring_eq` -/

/-- Proves an `Int` or `Nat` equation `a = b` whose sides are equal as
polynomials. -/
syntax (name := ringEq) "ring_eq" : tactic

@[tactic ringEq] def evalRingEq : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let ty ← zetaReduce (← instantiateMVars (← goal.getType'))
  let some (α, a, b) := ty.eq? | throwError "ring_eq: the goal is not an equation{indentExpr ty}"
  let zero := intToLean 0
  if α.isConstOf ``Int then
    let ((e₁, e₂), atoms) ← (do return (← reifyInt a, ← reifyInt b)).run #[]
    precheck "ring_eq" atoms 0 e₁ e₂
    let env ← mkListLit (mkConst ``Int) atoms.toList
    let l₁ := e₁.toLean
    let l₂ := e₂.toLean
    let aux ← kernelCheck "ring_eq"
      (mkApp2 (mkConst ``Expr.toPoly) zero l₁) (mkApp2 (mkConst ``Expr.toPoly) zero l₂)
    goal.assign (mkApp4 (mkConst ``eq_of_beq) l₁ l₂ env aux)
  else if α.isConstOf ``Nat then
    let ((e₁, e₂), atoms) ← (do return (← reifyNat a, ← reifyNat b)).run #[]
    precheck "ring_eq" atoms 0 e₁.toExpr e₂.toExpr
    let env ← mkListLit (mkConst ``Nat) atoms.toList
    let l₁ := e₁.toLean
    let l₂ := e₂.toLean
    let toPoly (l : Lean.Expr) :=
      mkApp2 (mkConst ``Expr.toPoly) zero (mkApp (mkConst ``NExpr.toExpr) l)
    let aux ← kernelCheck "ring_eq" (toPoly l₁) (toPoly l₂)
    goal.assign (mkApp4 (mkConst ``nat_eq_of_beq) l₁ l₂ env aux)
  else
    throwError "ring_eq: the goal is an equation in{indentExpr α}\nnot in `Int` or `Nat`"
  replaceMainGoal []

/-! ## `ring_mod` -/

/-- A hypothesis `h : E % n = 0` and its cofactor. -/
syntax ringModCert := term:max " * " term

/-- Proves `a % n = b % n` or `a % n = 0` over `Int` or `Nat` when `a - b`,
less the hypotheses times their cofactors, has every coefficient a multiple
of `n`. -/
syntax (name := ringMod) "ring_mod" ("[" ringModCert,* "]")? : tactic

/-- The `a` and `n` of `a % n`, at type `α`. -/
def emodArgs? (α e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  match e.getAppFnArgs with
  | (``HMod.hMod, #[β, _, _, _, a, n]) => if β == α then some (a, n) else none
  | _ => none

@[tactic ringMod] def evalRingMod : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let ty ← zetaReduce (← instantiateMVars (← goal.getType'))
  let some (α, lhs, rhs) := ty.eq? |
    throwError "ring_mod: the goal is not an equation{indentExpr ty}"
  let some (a, n) := emodArgs? α lhs |
    throwError "ring_mod: the goal's left side is not of the form `a % n`{indentExpr lhs}"
  let (b, toZero) ← match emodArgs? α rhs with
    | some (b, n') =>
      unless ← isDefEq n n' do
        throwError "ring_mod: the two sides use different moduli{indentExpr n}\n{indentExpr n'}"
      pure (b, false)
    | none =>
      if rawNat? rhs == some 0 then pure (rhs, true)
      else throwError "ring_mod: the goal's right side is neither `b % n` nor `0`{indentExpr rhs}"
  let certs : Array (Syntax × Syntax) :=
    if stx[1].isNone then #[]
    else stx[1][1].getSepArgs.map fun c => (c[0], c[2])
  let nVal? ← evalLit? n
  if α.isConstOf ``Int then
    let nLean := match nVal? with
      | some v => intToLean v
      | none => n
    let mut t? : Option (Lean.Expr × Lean.Expr) := none
    for (hStx, cStx) in certs do
      let h ← elabTerm hStx none
      let hTy ← zetaReduce (← instantiateMVars (← whnfR (← inferType h)))
      let some (_, hl, hr) := hTy.eq? |
        throwError "ring_mod: the hypothesis is not an equation{indentExpr hTy}"
      let some (E, n') := emodArgs? α hl |
        throwError "ring_mod: the hypothesis is not of the form `E % n = 0`{indentExpr hTy}"
      unless rawNat? hr == some 0 && (← isDefEq n n') do
        throwError "ring_mod: the hypothesis is not of the form `E % n = 0` for the goal's \
          modulus{indentExpr hTy}"
      let c ← elabTerm cStx (some (mkConst ``Int))
      let c ← instantiateMVars c
      let Ec ← mkAppM ``HMul.hMul #[E, c]
      let hEc ← mkAppM ``emod_mul_eq_zero #[h, c]
      t? ← match t? with
        | none => pure (some (Ec, hEc))
        | some (t, ht) => do
          pure (some (← mkAppM ``HAdd.hAdd #[t, Ec],
            mkApp5 (mkConst ``emod_add_eq_zero) t Ec n ht hEc))
    let b' ← match t? with
      | none => pure b
      | some (t, _) => mkAppM ``HAdd.hAdd #[b, t]
    let ((e₁, e₂), atoms) ← (do return (← reifyInt a, ← reifyInt b')).run #[]
    if let some v := nVal? then
      precheck "ring_mod" atoms v e₁ e₂
    let env ← mkListLit (mkConst ``Int) atoms.toList
    let l₁ := e₁.toLean
    let l₂ := e₂.toLean
    let aux ← kernelCheck "ring_mod"
      (mkApp2 (mkConst ``Expr.toPoly) nLean l₁) (mkApp2 (mkConst ``Expr.toPoly) nLean l₂)
    let mut pf := mkApp5 (mkConst ``emod_eq_of_beq) n l₁ l₂ env aux
    if let some (t, ht) := t? then
      pf := mkApp6 (mkConst ``emod_eq_of_emod_eq_add) a b t n pf ht
    if toZero then
      pf := mkApp3 (mkConst ``emod_eq_zero_of_emod_eq) a n pf
    goal.assign pf
  else if α.isConstOf ``Nat then
    unless certs.isEmpty do
      throwError "ring_mod: hypotheses are supported only for `Int` goals"
    let nLean := match nVal? with
      | some v => mkRawNatLit v.toNat
      | none => n
    let ((e₁, e₂), atoms) ← (do return (← reifyNat a, ← reifyNat b)).run #[]
    if let some v := nVal? then
      precheck "ring_mod" atoms v e₁.toExpr e₂.toExpr
    let env ← mkListLit (mkConst ``Nat) atoms.toList
    let l₁ := e₁.toLean
    let l₂ := e₂.toLean
    let toPoly (l : Lean.Expr) :=
      mkApp2 (mkConst ``Expr.toPoly) (mkApp (mkConst ``Int.ofNat) nLean)
        (mkApp (mkConst ``NExpr.toExpr) l)
    let aux ← kernelCheck "ring_mod" (toPoly l₁) (toPoly l₂)
    let mut pf := mkApp5 (mkConst ``nat_emod_eq_of_beq) n l₁ l₂ env aux
    if toZero then
      pf := mkApp3 (mkConst ``nat_emod_eq_zero_of_emod_eq) a n pf
    goal.assign pf
  else
    throwError "ring_mod: the goal is an equation in{indentExpr α}\nnot in `Int` or `Nat`"
  replaceMainGoal []

end C3.Ring
