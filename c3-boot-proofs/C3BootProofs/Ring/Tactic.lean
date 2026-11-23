import C3BootProofs.Ring.Basic

/-!
# `ring_eq` and `ring_mod`: polynomial identities by kernel computation

Two tactics that prove polynomial identities over `Int` and `Nat` without
`Classical.choice`: every proof they build depends only on `propext`. Each
reifies both sides of the goal into `C3.Ring.Expr`, normalizes them with
`Expr.toPoly`, and has the kernel check that the normal forms are equal by
evaluating `Poly.beq` to `true`, with `decide +kernel`. The soundness
theorem, `Expr.toPoly_sound`, is in `C3BootProofs.Ring.Basic`.

## `ring_eq`

`ring_eq` proves `a = b` over `Int` or `Nat` when the two sides are equal
as polynomials. The sides can use `+`, `*`, `^` with a numeral exponent,
numerals, and, over `Int`, `-` and negation. Anything else is an atom:
a variable, a function application, a named constant, a cast, or a `^`
whose exponent isn't a numeral. Atoms are identified up to reducible
definitional equality.

```
example (x y : Int) : (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by ring_eq
example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring_eq
```

Over `Nat`, `-` and `/` are atoms, so an identity that needs truncated
subtraction to cancel fails. To prove one, state it over `Int`.

The tactics don't look through `let`, projections, or definitions. Unfold
those first with `dsimp only [f, g]`, which adds no axioms.

## `ring_mod`

`ring_mod` proves `a % n = b % n` or `a % n = 0`, over `Int` or `Nat`,
when `a - b` is a polynomial whose coefficients are all multiples of `n`.
It normalizes both sides with coefficients reduced modulo `n`, so the
kernel has to be able to reduce `n` to a numeral: a literal, or a closed
term such as a constant defined as one. Large moduli, such as a 384-bit
prime, are fine.

```
example (x : Int) : (x + 7) ^ 2 % 7 = x ^ 2 % 7 := by ring_mod
example (x : Nat) : (x + 7) ^ 2 % 7 = x ^ 2 % 7 := by ring_mod
```

A named constant inside `a` or `b`, such as the modulus itself, is an atom,
so `(x + p) ^ 2 % p = x ^ 2 % p` needs `dsimp only [p]` first, which turns
`p` into the numeral it is defined as.

Over `Int`, `ring_mod [h₁ * c₁, …, hₖ * cₖ]` also uses hypotheses
`hᵢ : Eᵢ % n = 0`, such as curve equations, with cofactors `cᵢ`. It proves
the goal when `a - b - (E₁ * c₁ + … + Eₖ * cₖ)` has every coefficient a
multiple of `n`. Each `hᵢ` is a term at argument precedence (a name, or a
term in parentheses), and each `cᵢ` is any `Int` term over the goal's
variables. `scripts/ring-cofactors.py` computes cofactors by multivariate
division modulo `n` and prints the `ring_mod […]` call:

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

When the sides differ, `decide` fails and prints the reified comparison,
in which `var i` is the `i`th atom, counting from the left of the goal.
To see the difference itself, give the two sides to
`scripts/ring-cofactors.py` with no `--hyp`; it prints the normalized
difference. With hypotheses, it prints the remainder of the division.

Reification is type class resolution over the `ReifyInt` instances below,
so it needs no metaprograms, which would depend on `Classical.choice`
and fail the axiom audit. It takes about 2 ms for each operation in the
goal. The kernel's cost grows with the number of terms that the normal
forms and their intermediate products reach, and only mildly with
coefficient size, because the kernel does `Nat` arithmetic with GMP.
`C3BootProofs.Ring.Test` records timings.

Lean elaborates a term with many `x ^ 2` slowly, before any tactic runs,
because it resolves each exponent's type by default instances; 100 of
them take about 4 s. Writing `x ^ (2 : Nat)` avoids that, and
`scripts/ring-cofactors.py` prints cofactors that way.
-/

namespace C3.Ring

/-! ## Atoms -/

theorem get_append_length (l s : List Int) (a : Int) : get (l ++ a :: s) l.length = a := by
  induction l with
  | nil => rfl
  | cons x xs ih => exact ih

/-- `n` is the length of `l`. -/
class Len (l : List Int) (n : outParam Nat) : Prop where
  eq : l.length = n

instance lenNil : Len [] 0 := ⟨rfl⟩

instance lenCons (b : Int) (l : List Int) (n : Nat) [h : Len l n] :
    Len (b :: l) (n + 1) :=
  ⟨congrArg (· + 1) h.eq⟩

/-- `a` is at index `i` of the reverse of `l`. -/
class FindAtom (a : Int) (l : List Int) (i : outParam Nat) : Prop where
  get_eq : ∀ s, get (l.reverse ++ s) i = a

instance findHead (a : Int) (l : List Int) (n : Nat) [h : Len l n] : FindAtom a (a :: l) n :=
  ⟨fun s => by
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, ← h.eq,
      ← List.length_reverse]
    exact get_append_length _ _ _⟩

instance findTail (a b : Int) (l : List Int) (i : Nat) [h : FindAtom a l i] :
    FindAtom a (b :: l) i :=
  ⟨fun s => by
    rw [List.reverse_cons, List.append_assoc]
    exact h.get_eq _⟩

/-! ## Reification -/

/-- `e` evaluates to `a` in every environment that starts with the reverse
of `l'`, and `l'` extends `l` at the front. Resolving `ReifyInt a l ?l' ?e`
reifies `a`, adding its new atoms to `l`. -/
class ReifyInt (a : Int) (l : List Int) (l' : outParam (List Int)) (e : outParam Expr) :
    Prop where
  ext : ∃ t, l' = t ++ l
  sound : ∀ s, e.eval (l'.reverse ++ s) = a

theorem ReifyInt.sound_of_ext {a : Int} {l l' l'' : List Int} {e : Expr} (h : ReifyInt a l l' e)
    (t : List Int) (ht : l'' = t ++ l') (s : List Int) : e.eval (l''.reverse ++ s) = a := by
  rw [ht, List.reverse_append, List.append_assoc]
  exact h.sound _

theorem ext_trans {l l₁ l₂ : List Int} (h₁ : ∃ t, l₁ = t ++ l) (h₂ : ∃ t, l₂ = t ++ l₁) :
    ∃ t, l₂ = t ++ l := by
  obtain ⟨t₁, rfl⟩ := h₁
  obtain ⟨t₂, rfl⟩ := h₂
  exact ⟨t₂ ++ t₁, (List.append_assoc _ _ _).symm⟩

theorem ReifyInt.binop {a b : Int} {l l₁ l₂ : List Int} {ea eb e : Expr}
    (ha : ReifyInt a l l₁ ea) (hb : ReifyInt b l₁ l₂ eb) (f : Int → Int → Int) (c : Int)
    (he : ∀ env, e.eval env = f (ea.eval env) (eb.eval env)) (hc : f a b = c) :
    ReifyInt c l l₂ e where
  ext := ext_trans ha.ext hb.ext
  sound s := by
    obtain ⟨t, ht⟩ := hb.ext
    rw [he, ha.sound_of_ext t ht, hb.sound, hc]

theorem ReifyInt.unop {a : Int} {l l₁ : List Int} {ea e : Expr} (ha : ReifyInt a l l₁ ea)
    (f : Int → Int) (c : Int) (he : ∀ env, e.eval env = f (ea.eval env)) (hc : f a = c) :
    ReifyInt c l l₁ e where
  ext := ha.ext
  sound s := by rw [he, ha.sound, hc]

instance reifyAdd (a b : Int) (l l₁ l₂ : List Int) (ea eb : Expr)
    [ha : ReifyInt a l l₁ ea] [hb : ReifyInt b l₁ l₂ eb] :
    ReifyInt (a + b) l l₂ (.add ea eb) :=
  ha.binop hb (· + ·) _ (fun _ => rfl) rfl

instance reifySub (a b : Int) (l l₁ l₂ : List Int) (ea eb : Expr)
    [ha : ReifyInt a l l₁ ea] [hb : ReifyInt b l₁ l₂ eb] :
    ReifyInt (a - b) l l₂ (.sub ea eb) :=
  ha.binop hb (· - ·) _ (fun _ => rfl) rfl

instance reifyMul (a b : Int) (l l₁ l₂ : List Int) (ea eb : Expr)
    [ha : ReifyInt a l l₁ ea] [hb : ReifyInt b l₁ l₂ eb] :
    ReifyInt (a * b) l l₂ (.mul ea eb) :=
  ha.binop hb (· * ·) _ (fun _ => rfl) rfl

instance reifyNeg (a : Int) (l l₁ : List Int) (ea : Expr) [ha : ReifyInt a l l₁ ea] :
    ReifyInt (-a) l l₁ (.neg ea) :=
  ha.unop (- ·) _ (fun _ => rfl) rfl

/-- `k` is a numeral. The numeral instances here match `0` and `k + 1`, not
`OfNat.ofNat k`, because unification solves `OfNat.ofNat ?k _ =?= x` for a
variable `x`, while offset unification solves `?k + 1 =?= x` only for a
numeral `x`. -/
class IsNumeral (k : Nat) : Prop

instance isNumeralZero : IsNumeral 0 := ⟨⟩

instance isNumeralSucc (k : Nat) : IsNumeral (no_index (k + 1)) := ⟨⟩

instance reifyPow (a : Int) (k : Nat) (l l₁ : List Int) (ea : Expr) [IsNumeral k]
    [ha : ReifyInt a l l₁ ea] : ReifyInt (a ^ k) l l₁ (.pow ea k) :=
  ha.unop (· ^ k) _ (fun _ => rfl) rfl

instance (priority := low + 1) reifyZero (l : List Int) : ReifyInt 0 l l (.const 0) where
  ext := ⟨[], rfl⟩
  sound _ := rfl

instance (priority := low + 1) reifySucc (n : Nat) (l : List Int) :
    ReifyInt (no_index (OfNat.ofNat (n + 1))) l l (.const (OfNat.ofNat (n + 1))) where
  ext := ⟨[], rfl⟩
  sound _ := rfl

instance reifyNatCastAdd (a b : Nat) (l l₁ l₂ : List Int) (ea eb : Expr)
    [ha : ReifyInt a l l₁ ea] [hb : ReifyInt b l₁ l₂ eb] :
    ReifyInt ((a + b : Nat) : Int) l l₂ (.add ea eb) :=
  ha.binop hb (· + ·) _ (fun _ => rfl) (Int.natCast_add a b).symm

instance reifyNatCastMul (a b : Nat) (l l₁ l₂ : List Int) (ea eb : Expr)
    [ha : ReifyInt a l l₁ ea] [hb : ReifyInt b l₁ l₂ eb] :
    ReifyInt ((a * b : Nat) : Int) l l₂ (.mul ea eb) :=
  ha.binop hb (· * ·) _ (fun _ => rfl) (Int.natCast_mul a b).symm

instance reifyNatCastPow (a : Nat) (k : Nat) (l l₁ : List Int) (ea : Expr) [IsNumeral k]
    [ha : ReifyInt a l l₁ ea] : ReifyInt ((a ^ k : Nat) : Int) l l₁ (.pow ea k) :=
  ha.unop (· ^ k) _ (fun _ => rfl) (Int.natCast_pow a k).symm

instance (priority := low + 1) reifyNatCastZero (l : List Int) :
    ReifyInt ((0 : Nat) : Int) l l (.const 0) where
  ext := ⟨[], rfl⟩
  sound _ := rfl

instance (priority := low + 1) reifyNatCastSucc (n : Nat) (l : List Int) :
    ReifyInt ((no_index (n + 1) : Nat) : Int) l l (.const ((n + 1 : Nat) : Int)) where
  ext := ⟨[], rfl⟩
  sound _ := rfl

instance (priority := low) reifyOldAtom (a : Int) (l : List Int) (i : Nat)
    [h : FindAtom a l i] : ReifyInt a l l (.var i) where
  ext := ⟨[], rfl⟩
  sound s := h.get_eq s

instance (priority := low - 1) reifyNewAtom (a : Int) (l : List Int) (n : Nat) [Len l n] :
    ReifyInt a l (a :: l) (.var n) where
  ext := ⟨[a], rfl⟩
  sound s := (findHead a l n).get_eq s

/-! ## Goals -/

/-- `x = y` follows when `e₁` and `e₂` have equal normal forms modulo `m`.
Resolving `RingEq false x y ?e₁ ?e₂ ?m` reifies an `Int` or `Nat` equation,
and `RingEq true` a congruence `a % n = b % n` or `a % n = 0`. -/
class RingEq {α : Type} (mod : Bool) (x y : α) (e₁ e₂ : outParam Expr) (m : outParam Int) :
    Prop where
  of_beq : Poly.beq (e₁.toPoly m) (e₂.toPoly m) = true → x = y

theorem RingEq.eq {α : Type} (mod : Bool) {x y : α} {e₁ e₂ : Expr} {m : Int}
    [h : RingEq mod x y e₁ e₂ m]
    (hb : Poly.beq (e₁.toPoly m) (e₂.toPoly m) = true) : x = y :=
  h.of_beq hb

theorem reify_eval {a b : Int} {l₁ l₂ : List Int} {e₁ e₂ : Expr}
    (h₁ : ReifyInt a [] l₁ e₁) (h₂ : ReifyInt b l₁ l₂ e₂) :
    e₁.eval l₂.reverse = a ∧ e₂.eval l₂.reverse = b := by
  obtain ⟨t, ht⟩ := h₂.ext
  have h₁' := h₁.sound_of_ext t ht []
  have h₂' := h₂.sound []
  rw [List.append_nil] at h₁' h₂'
  exact ⟨h₁', h₂'⟩

instance ringEqInt (a b : Int) (l₁ l₂ : List Int) (e₁ e₂ : Expr)
    [h₁ : ReifyInt a [] l₁ e₁] [h₂ : ReifyInt b l₁ l₂ e₂] :
    RingEq false a b e₁ e₂ 0 where
  of_beq hb := by
    obtain ⟨ha, hb'⟩ := reify_eval h₁ h₂
    rw [← ha, ← hb']
    exact eq_of_beq e₁ e₂ _ hb

instance ringEqNat (a b : Nat) (l₁ l₂ : List Int) (e₁ e₂ : Expr)
    [h₁ : ReifyInt a [] l₁ e₁] [h₂ : ReifyInt b l₁ l₂ e₂] :
    RingEq false a b e₁ e₂ 0 where
  of_beq hb := by
    obtain ⟨ha, hb'⟩ := reify_eval h₁ h₂
    apply Int.ofNat.inj
    rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, ← ha, ← hb']
    exact eq_of_beq e₁ e₂ _ hb

instance ringModInt (a b n : Int) (l₁ l₂ : List Int) (e₁ e₂ : Expr)
    [h₁ : ReifyInt a [] l₁ e₁] [h₂ : ReifyInt b l₁ l₂ e₂] :
    RingEq true (a % n) (b % n) e₁ e₂ n where
  of_beq hb := by
    obtain ⟨ha, hb'⟩ := reify_eval h₁ h₂
    rw [← ha, ← hb']
    exact emod_eq_of_beq n e₁ e₂ _ hb

instance ringModIntZero (a n : Int) (l₁ : List Int) (e₁ : Expr) [h₁ : ReifyInt a [] l₁ e₁] :
    RingEq true (a % n) (no_index (OfNat.ofNat 0)) e₁ (.const 0) n where
  of_beq hb := by
    have h := emod_eq_of_beq n e₁ (.const 0) l₁.reverse hb
    have ha := h₁.sound []
    rw [List.append_nil] at ha
    rw [ha] at h
    exact emod_eq_zero_of_emod_eq h

instance ringModNat (a b n : Nat) (l₁ l₂ : List Int) (e₁ e₂ : Expr)
    [h₁ : ReifyInt a [] l₁ e₁] [h₂ : ReifyInt b l₁ l₂ e₂] :
    RingEq true (a % n) (b % n) e₁ e₂ (n : Int) where
  of_beq hb := by
    obtain ⟨ha, hb'⟩ := reify_eval h₁ h₂
    apply nat_emod_eq_of_int
    rw [← ha, ← hb']
    exact emod_eq_of_beq n e₁ e₂ _ hb

instance ringModNatZero (a n : Nat) (l₁ : List Int) (e₁ : Expr) [h₁ : ReifyInt a [] l₁ e₁] :
    RingEq true (a % n) (no_index (OfNat.ofNat 0)) e₁ (.const 0) (n : Int) where
  of_beq hb := by
    have h := emod_eq_of_beq n e₁ (.const 0) l₁.reverse hb
    have ha := h₁.sound []
    rw [List.append_nil] at ha
    rw [ha] at h
    apply nat_emod_eq_zero_of_emod_eq
    apply nat_emod_eq_of_int
    exact h

/-! ## Tactics -/

/-- Proves an `Int` or `Nat` equation whose sides are equal as polynomials. -/
macro "ring_eq" : tactic =>
  `(tactic| (
    set_option synthInstance.maxSize 1000000 in
    set_option synthInstance.maxHeartbeats 0 in
    refine C3.Ring.RingEq.eq false ?_
    decide +kernel))

/-- A hypothesis `h : E % n = 0` and its cofactor. -/
syntax ringModCert := term:max " * " term

/-- Proves `a % n = b % n` or `a % n = 0` over `Int` or `Nat` when `a - b`,
less the hypotheses times their cofactors, has every coefficient a multiple
of `n`. -/
syntax (name := ringMod) "ring_mod" ("[" ringModCert,* "]")? : tactic

macro_rules
  | `(tactic| ring_mod) =>
    `(tactic| (
      set_option synthInstance.maxSize 1000000 in
      set_option synthInstance.maxHeartbeats 0 in
      refine C3.Ring.RingEq.eq true ?_
      decide +kernel))
  | `(tactic| ring_mod [$cs,*]) => do
    let hs ← cs.getElems.toList.mapM fun (c : Lean.TSyntax `C3.Ring.ringModCert) =>
      match c with
      | `(ringModCert| $h:term * $k:term) => `(C3.Ring.emod_mul_eq_zero $h $k)
      | _ => Lean.Macro.throwUnsupported
    let h₀ :: hs := hs | `(tactic| ring_mod)
    let ht ← hs.foldlM (fun acc h => `(C3.Ring.emod_add_eq_zero $acc $h)) h₀
    `(tactic| (
      (try refine C3.Ring.emod_eq_zero_of_emod_eq ?_)
      refine C3.Ring.emod_eq_of_emod_eq_add ?_ $ht
      ring_mod))

end C3.Ring
