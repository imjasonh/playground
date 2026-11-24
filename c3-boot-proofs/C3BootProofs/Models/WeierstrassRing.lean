import C3BootProofs.Ring.Tactic
import C3BootProofs.Models.EcdsaField

/-!
# Congruences modulo a variable modulus and curve equations

`curve_mod` proves `MEq p a b` for any modulus `p`, numeral or not, from
hypotheses `h : MEq p (y ^ d) f` that rewrite powers of atoms, such as
the curve equations `y ^ 2 ≡ x ^ 3 + a x + b`, and hypotheses
`h : MEq p E 0` with cofactors. It reifies the goal and hypotheses with
the `ReifyInt` instances of `C3BootProofs.Ring.Tactic`, normalizes
`a - b - (E₁ c₁ + … + Eₖ cₖ)` with exact coefficients, and after every
product replaces each `y ^ d` by `f` until no atom has an exponent at
least its rule's `d`. The kernel then checks that the result is zero.

```
example (p : Nat) (x y b : Int) (h : MEq p (y ^ 2) (x ^ 3 - 3 * x + b)) :
    MEq p (y ^ 4) ((x ^ 3 - 3 * x + b) * y ^ 2) := by
  curve_mod [h] []
```

A rule `MEq p (y ^ d) f` applies to every monomial whose exponent of `y`
is at least `d`, so with the rules for `y₁ ^ 2`, `y₂ ^ 2`, … the result is
the normal form modulo the curve equations, and the check succeeds
exactly when `a - b - Σ Eᵢ cᵢ` is in their ideal over `ℤ`. Each rule
applies once a round, in the order given, and `curve_mod` runs `2` rounds
after each product; `curve_mod (fuel := n)` runs `n`.
-/

namespace C3.Ring

open C3.Models

/-! ## Kernel functions -/

/-- `get env k ^ d` divides the monomial. -/
noncomputable def Mon.geExp (k d : Nat) (m : Mon) : Bool :=
  Mon.rec (motive := fun _ => Bool) false
    (fun x e _ ih => Bool.rec (motive := fun _ => Bool) ih (Nat.ble d e) (Nat.beq x k)) m

/-- The monomial divided by `get env k ^ d`, when `geExp k d` holds. -/
noncomputable def Mon.divExp (k d : Nat) (m : Mon) : Mon :=
  Mon.rec (motive := fun _ => Mon) Mon.one
    (fun x e m ih =>
      Bool.rec (motive := fun _ => Mon) (Mon.cons x e ih)
        (Bool.rec (motive := fun _ => Mon) (Mon.cons x (Nat.sub e d) m) m (Nat.beq e d))
        (Nat.beq x k))
    m

/-- The terms that `get env k ^ d` divides, divided by it. -/
noncomputable def Poly.hiPart (k d : Nat) (p : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.zero
    (fun c m _ ih =>
      Bool.rec (motive := fun _ => Poly) ih (Poly.term c (Mon.divExp k d m) ih) (Mon.geExp k d m))
    p

/-- The other terms. -/
noncomputable def Poly.loPart (k d : Nat) (p : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.zero
    (fun c m _ ih => Bool.rec (motive := fun _ => Poly) (Poly.term c m ih) ih (Mon.geExp k d m)) p

/-- A rewrite rule: atom `k` to the power `d` is congruent to `f`. -/
structure Rule where
  k : Nat
  d : Nat
  f : Poly

/-- One application of a rule to every term. -/
noncomputable def Poly.redStep (r : Rule) (p : Poly) : Poly :=
  Poly.add 0 (Poly.loPart r.k r.d p) (Poly.mul 0 r.f (Poly.hiPart r.k r.d p))

/-- Each rule once, in order. -/
noncomputable def Poly.redRules (rs : List Rule) (p : Poly) : Poly :=
  List.rec (motive := fun _ => Poly → Poly) (fun p => p) (fun r _ ih p => ih (Poly.redStep r p)) rs p

/-- `fuel` rounds of the rules. -/
noncomputable def Poly.red (rs : List Rule) (fuel : Nat) (p : Poly) : Poly :=
  Nat.rec (motive := fun _ => Poly) p (fun _ ih => Poly.redRules rs ih) fuel

/-- The normal form of an expression with exact coefficients, reduced by
the rules after every product and power. -/
noncomputable def Expr.toPolyR (rs : List Rule) (fuel : Nat) (e : Expr) : Poly :=
  Expr.rec (motive := fun _ => Poly)
    (fun c => Poly.monomial 0 c Mon.one)
    (fun i => Poly.monomial 0 1 (Mon.cons i 1 Mon.one))
    (fun _ _ a b => Poly.add 0 a b)
    (fun _ _ a b => Poly.add 0 a (Poly.neg 0 b))
    (fun _ a => Poly.neg 0 a)
    (fun _ _ a b => Poly.red rs fuel (Poly.mul 0 a b))
    (fun _ k a => Poly.red rs fuel (Poly.pow 0 a k))
    e

/-- Whether an expression is an atom. -/
noncomputable def Expr.isVar (e : Expr) : Bool :=
  Expr.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => true) (fun _ _ _ _ => false)
    (fun _ _ _ _ => false) (fun _ _ => false) (fun _ _ _ _ => false) (fun _ _ _ => false) e

/-- An atom's index. -/
noncomputable def Expr.varIdx (e : Expr) : Nat :=
  Expr.rec (motive := fun _ => Nat) (fun _ => 0) (fun i => i) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ => 0) e

/-- The rules that reified hypotheses `(y, d, f)` state. -/
noncomputable def mkRules (es : List (Expr × Nat × Expr)) : List Rule :=
  List.rec (motive := fun _ => List Rule) [] (fun t _ ih => ⟨t.1.varIdx, t.2.1, t.2.2.toPoly 0⟩ :: ih) es

/-- Every rule's left side is an atom. -/
noncomputable def allVars (es : List (Expr × Nat × Expr)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun t _ ih => Bool.and t.1.isVar ih) es

/-- `E₁ c₁ + … + Eₖ cₖ`. -/
noncomputable def sumCofs (cs : List (Expr × Expr)) : Expr :=
  List.rec (motive := fun _ => Expr) (.const 0) (fun t _ ih => .add (.mul t.1 t.2) ih) cs

/-- The check `curve_mod` has the kernel run. -/
noncomputable def curveCheck (fuel : Nat) (e₁ e₂ : Expr) (es : List (Expr × Nat × Expr))
    (cs : List (Expr × Expr)) : Bool :=
  Bool.and (allVars es)
    (Poly.beq (Poly.red (mkRules es) fuel (Expr.toPolyR (mkRules es) fuel (.sub (.sub e₁ e₂) (sumCofs cs))))
      Poly.zero)

/-! ## Soundness -/

theorem poly_eval_add (env : List Int) (p q : Poly) :
    (Poly.add 0 p q).eval env = p.eval env + q.eval env := by
  have := Poly.eval_add env 0 p q
  rwa [Int.emod_zero, Int.emod_zero] at this

theorem poly_eval_mul (env : List Int) (p q : Poly) :
    (Poly.mul 0 p q).eval env = p.eval env * q.eval env := by
  have := Poly.eval_mul env 0 p q
  rwa [Int.emod_zero, Int.emod_zero] at this

theorem poly_eval_neg (env : List Int) (p : Poly) : (Poly.neg 0 p).eval env = -p.eval env := by
  have := Poly.eval_neg env 0 p
  rwa [Int.emod_zero, Int.emod_zero] at this

theorem poly_eval_pow (env : List Int) (p : Poly) (k : Nat) :
    (Poly.pow 0 p k).eval env = p.eval env ^ k := by
  have := Poly.eval_pow env 0 p k
  rwa [Int.emod_zero, Int.emod_zero] at this

theorem poly_eval_monomial (env : List Int) (c : Int) (m : Mon) :
    (Poly.monomial 0 c m).eval env = c * m.eval env := by
  have := Poly.eval_monomial env 0 c m
  rwa [Int.emod_zero, Int.emod_zero] at this

theorem expr_toPoly_eval (env : List Int) (e : Expr) : (e.toPoly 0).eval env = e.eval env := by
  have := Expr.toPoly_sound env 0 e
  rwa [Int.emod_zero, Int.emod_zero] at this

theorem Mon.eval_divExp (env : List Int) (k d : Nat) (m : Mon) (h : Mon.geExp k d m = true) :
    m.eval env = get env k ^ d * (Mon.divExp k d m).eval env := by
  induction m with
  | one => exact absurd h Bool.false_ne_true
  | cons x e m ih =>
    change Bool.rec (motive := fun _ => Bool) (Mon.geExp k d m) (Nat.ble d e) (Nat.beq x k) = true at h
    show get env x ^ e * m.eval env = get env k ^ d *
      (Bool.rec (motive := fun _ => Mon) (Mon.cons x e (Mon.divExp k d m))
        (Bool.rec (motive := fun _ => Mon) (Mon.cons x (Nat.sub e d) m) m (Nat.beq e d))
        (Nat.beq x k)).eval env
    cases hx : Nat.beq x k with
    | false =>
      rw [hx] at h
      show _ = get env k ^ d * (get env x ^ e * (Mon.divExp k d m).eval env)
      rw [ih h, Int.mul_left_comm]
    | true =>
      rw [hx] at h
      have hxk := Nat.eq_of_beq_eq_true hx
      have hde := Nat.le_of_ble_eq_true h
      subst hxk
      cases he : Nat.beq e d with
      | true =>
        have := Nat.eq_of_beq_eq_true he
        subst this
        rfl
      | false =>
        show _ = get env x ^ d * (get env x ^ (e - d) * m.eval env)
        rw [← Int.mul_assoc, ← Int.pow_add, Nat.add_sub_cancel' hde]

theorem Poly.eval_split (env : List Int) (k d : Nat) (p : Poly) :
    p.eval env = (Poly.loPart k d p).eval env + get env k ^ d * (Poly.hiPart k d p).eval env := by
  induction p with
  | zero => show (0 : Int) = 0 + get env k ^ d * 0; rw [Int.mul_zero, Int.add_zero]
  | term c m p ih =>
    show c * m.eval env + p.eval env =
      (Bool.rec (motive := fun _ => Poly) (Poly.term c m (Poly.loPart k d p)) (Poly.loPart k d p)
        (Mon.geExp k d m)).eval env + get env k ^ d *
      (Bool.rec (motive := fun _ => Poly) (Poly.hiPart k d p)
        (Poly.term c (Mon.divExp k d m) (Poly.hiPart k d p)) (Mon.geExp k d m)).eval env
    cases hg : Mon.geExp k d m with
    | false =>
      show _ = (c * m.eval env + (Poly.loPart k d p).eval env) + _
      rw [ih, Int.add_assoc]
    | true =>
      show _ = _ + get env k ^ d * (c * (Mon.divExp k d m).eval env + (Poly.hiPart k d p).eval env)
      rw [ih, Mon.eval_divExp env k d m hg, Int.mul_add]
      simp only [Int.mul_left_comm, Int.add_comm, Int.add_assoc]

/-- The rules hold in `env` modulo `p`. -/
def RulesHold (p : Nat) (env : List Int) : List Rule → Prop
  | [] => True
  | r :: rs => MEq p (get env r.k ^ r.d) (r.f.eval env) ∧ RulesHold p env rs

theorem redStep_sound {p : Nat} {env : List Int} {r : Rule} (h : MEq p (get env r.k ^ r.d) (r.f.eval env))
    (q : Poly) : MEq p ((Poly.redStep r q).eval env) (q.eval env) := by
  unfold Poly.redStep
  rw [poly_eval_add, poly_eval_mul, Poly.eval_split env r.k r.d q]
  exact (MEq.refl _).add ((h.symm).mul (MEq.refl _))

theorem redRules_sound {p : Nat} {env : List Int} :
    ∀ {rs : List Rule}, RulesHold p env rs → ∀ q : Poly, MEq p ((Poly.redRules rs q).eval env) (q.eval env)
  | [], _, _ => MEq.refl _
  | _ :: _, ⟨h, hs⟩, q => (redRules_sound hs _).trans (redStep_sound h q)

theorem red_sound {p : Nat} {env : List Int} {rs : List Rule} (h : RulesHold p env rs) (fuel : Nat) (q : Poly) :
    MEq p ((Poly.red rs fuel q).eval env) (q.eval env) := by
  induction fuel with
  | zero => exact MEq.refl _
  | succ n ih => exact (redRules_sound h _).trans ih

theorem toPolyR_sound {p : Nat} {env : List Int} {rs : List Rule} (h : RulesHold p env rs) (fuel : Nat)
    (e : Expr) : MEq p ((e.toPolyR rs fuel).eval env) (e.eval env) := by
  induction e with
  | const c =>
    show MEq p ((Poly.monomial 0 c Mon.one).eval env) c
    rw [poly_eval_monomial, Mon.eval_one, Int.mul_one]; exact MEq.refl _
  | var i =>
    show MEq p ((Poly.monomial 0 1 (Mon.cons i 1 Mon.one)).eval env) (get env i)
    rw [poly_eval_monomial, Mon.eval_cons, Mon.eval_one, Int.mul_one, Int.one_mul, Int.pow_one]
    exact MEq.refl _
  | add a b iha ihb =>
    show MEq p ((Poly.add 0 _ _).eval env) _
    rw [poly_eval_add]; exact iha.add ihb
  | sub a b iha ihb =>
    show MEq p ((Poly.add 0 _ (Poly.neg 0 _)).eval env) (a.eval env - b.eval env)
    rw [poly_eval_add, poly_eval_neg, ← Int.sub_eq_add_neg]; exact iha.sub ihb
  | neg a iha =>
    show MEq p ((Poly.neg 0 _).eval env) (-a.eval env)
    rw [poly_eval_neg]; exact iha.neg
  | mul a b iha ihb =>
    show MEq p ((Poly.red rs fuel (Poly.mul 0 _ _)).eval env) (a.eval env * b.eval env)
    refine (red_sound h fuel _).trans ?_
    rw [poly_eval_mul]; exact iha.mul ihb
  | pow a k iha =>
    show MEq p ((Poly.red rs fuel (Poly.pow 0 _ k)).eval env) (a.eval env ^ k)
    refine (red_sound h fuel _).trans ?_
    rw [poly_eval_pow]
    induction k with
    | zero => rw [Int.pow_zero, Int.pow_zero]; exact MEq.refl _
    | succ k ihk => rw [Int.pow_succ, Int.pow_succ]; exact ihk.mul iha

theorem Expr.eq_var_of_isVar {e : Expr} (h : e.isVar = true) : e = Expr.var e.varIdx := by
  cases e <;> first | rfl | exact absurd h Bool.false_ne_true

/-! ## Hypotheses -/

/-- Proofs of the rewrite hypotheses `MEq p (y ^ d) f`. -/
inductive Hyps (p : Nat) : List (Int × Nat × Int) → Prop
  | nil : Hyps p []
  | cons {y : Int} {d : Nat} {f : Int} {hs : List (Int × Nat × Int)} :
      MEq p (y ^ d) f → Hyps p hs → Hyps p ((y, d, f) :: hs)

/-- Proofs of the hypotheses `MEq p E 0`, with their cofactors. -/
inductive Cofs (p : Nat) : List (Int × Int) → Prop
  | nil : Cofs p []
  | cons {E : Int} {cs : List (Int × Int)} : MEq p E 0 → (c : Int) → Cofs p cs → Cofs p ((E, c) :: cs)

/-- The reified rules evaluate to the hypotheses. -/
def RulesEval (env : List Int) : List (Expr × Nat × Expr) → List (Int × Nat × Int) → Prop
  | [], [] => True
  | e :: es, h :: hs => e.1.eval env = h.1 ∧ e.2.1 = h.2.1 ∧ e.2.2.eval env = h.2.2 ∧ RulesEval env es hs
  | _, _ => False

/-- The reified cofactor pairs evaluate to the given ones. -/
def CofsEval (env : List Int) : List (Expr × Expr) → List (Int × Int) → Prop
  | [], [] => True
  | e :: es, h :: hs => e.1.eval env = h.1 ∧ e.2.eval env = h.2 ∧ CofsEval env es hs
  | _, _ => False

theorem rulesHold_of {p : Nat} {env : List Int} :
    ∀ {es : List (Expr × Nat × Expr)} {hs : List (Int × Nat × Int)}, RulesEval env es hs → Hyps p hs →
      allVars es = true → RulesHold p env (mkRules es)
  | [], [], _, _, _ => trivial
  | e :: es, _ :: _, ⟨h1, h2, h3, hr⟩, .cons hh ht, hv => by
    change Bool.and e.1.isVar (allVars es) = true at hv
    cases hve : e.1.isVar with
    | false => rw [hve] at hv; exact absurd hv Bool.false_ne_true
    | true =>
      rw [hve] at hv
      refine ⟨?_, rulesHold_of hr ht hv⟩
      show MEq p (get env e.1.varIdx ^ e.2.1) ((e.2.2.toPoly 0).eval env)
      rw [expr_toPoly_eval, h3, h2, ← Expr.eval_var, ← Expr.eq_var_of_isVar hve, h1]
      exact hh

theorem sumCofs_zero {p : Nat} {env : List Int} :
    ∀ {cs : List (Expr × Expr)} {hs : List (Int × Int)}, CofsEval env cs hs → Cofs p hs →
      MEq p ((sumCofs cs).eval env) 0
  | [], [], _, _ => MEq.refl _
  | e :: es, _ :: _, ⟨h1, h2, hr⟩, hk => by
    cases hk with
    | cons hh c ht =>
    show MEq p (e.1.eval env * e.2.eval env + (sumCofs es).eval env) 0
    rw [h1, h2]
    have := (hh.mul (MEq.refl c)).add (sumCofs_zero hr ht)
    rwa [Int.zero_mul, Int.zero_add] at this

theorem curveCheck_sound {p : Nat} {env : List Int} {fuel : Nat} {e₁ e₂ : Expr}
    {es : List (Expr × Nat × Expr)} {cs : List (Expr × Expr)} {hs : List (Int × Nat × Int)}
    {hc : List (Int × Int)} (hr : RulesEval env es hs) (hcs : CofsEval env cs hc) (hh : Hyps p hs)
    (hk : Cofs p hc) (h : curveCheck fuel e₁ e₂ es cs = true) : MEq p (e₁.eval env) (e₂.eval env) := by
  unfold curveCheck at h
  cases hv : allVars es with
  | false => rw [hv] at h; exact absurd h Bool.false_ne_true
  | true =>
    rw [hv] at h
    have hR := rulesHold_of hr hh hv
    have h0 := Poly.eq_of_beq h
    have e1 := (red_sound hR fuel _).trans (toPolyR_sound hR fuel (.sub (.sub e₁ e₂) (sumCofs cs)))
    rw [h0] at e1
    have e2 : MEq p (e₁.eval env - e₂.eval env - (sumCofs cs).eval env) 0 := e1.symm
    have e3 := e2.add (sumCofs_zero hcs hk)
    rw [Int.sub_add_cancel, Int.zero_add] at e3
    exact MEq.iff_sub.mpr e3

/-! ## Reification -/

/-- Reifies a list of rewrite hypotheses, extending the atoms `l`. -/
class ReifyRules (hs : List (Int × Nat × Int)) (l : List Int) (l' : outParam (List Int))
    (es : outParam (List (Expr × Nat × Expr))) : Prop where
  ext : ∃ t, l' = t ++ l
  sound : ∀ s, RulesEval (l'.reverse ++ s) es hs

/-- Reifies a list of cofactor pairs, extending the atoms `l`. -/
class ReifyCofs (hs : List (Int × Int)) (l : List Int) (l' : outParam (List Int))
    (es : outParam (List (Expr × Expr))) : Prop where
  ext : ∃ t, l' = t ++ l
  sound : ∀ s, CofsEval (l'.reverse ++ s) es hs

theorem rev_ext {l l' : List Int} (h : ∃ t, l' = t ++ l) (s : List Int) :
    ∃ s', l'.reverse ++ s = l.reverse ++ s' := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t.reverse ++ s, by rw [List.reverse_append, List.append_assoc]⟩

instance reifyRulesNil (l : List Int) : ReifyRules [] l l [] where
  ext := ⟨[], rfl⟩
  sound _ := trivial

instance reifyRulesCons (y : Int) (d : Nat) (f : Int) (hs : List (Int × Nat × Int)) (l l₁ l₂ l₃ : List Int)
    (ey ef : Expr) (es : List (Expr × Nat × Expr)) [hy : ReifyInt y l l₁ ey] [hf : ReifyInt f l₁ l₂ ef]
    [hr : ReifyRules hs l₂ l₃ es] : ReifyRules ((y, d, f) :: hs) l l₃ ((ey, d, ef) :: es) where
  ext := ext_trans (ext_trans hy.ext hf.ext) hr.ext
  sound s := by
    refine ⟨?_, rfl, ?_, hr.sound s⟩
    · obtain ⟨s', hs'⟩ := rev_ext (ext_trans hf.ext hr.ext) s
      show ey.eval (l₃.reverse ++ s) = y
      rw [hs']; exact hy.sound s'
    · obtain ⟨s', hs'⟩ := rev_ext hr.ext s
      show ef.eval (l₃.reverse ++ s) = f
      rw [hs']; exact hf.sound s'

instance reifyCofsNil (l : List Int) : ReifyCofs [] l l [] where
  ext := ⟨[], rfl⟩
  sound _ := trivial

instance reifyCofsCons (E c : Int) (hs : List (Int × Int)) (l l₁ l₂ l₃ : List Int) (eE ec : Expr)
    (es : List (Expr × Expr)) [hE : ReifyInt E l l₁ eE] [hc : ReifyInt c l₁ l₂ ec]
    [hr : ReifyCofs hs l₂ l₃ es] : ReifyCofs ((E, c) :: hs) l l₃ ((eE, ec) :: es) where
  ext := ext_trans (ext_trans hE.ext hc.ext) hr.ext
  sound s := by
    refine ⟨?_, ?_, hr.sound s⟩
    · obtain ⟨s', hs'⟩ := rev_ext (ext_trans hc.ext hr.ext) s
      show eE.eval (l₃.reverse ++ s) = E
      rw [hs']; exact hE.sound s'
    · obtain ⟨s', hs'⟩ := rev_ext hr.ext s
      show ec.eval (l₃.reverse ++ s) = c
      rw [hs']; exact hc.sound s'

/-- A goal `MEq p a b` with its hypotheses, reified over one environment. -/
class CurveGoal (a b : Int) (hs : List (Int × Nat × Int)) (hc : List (Int × Int)) (e₁ e₂ : outParam Expr)
    (es : outParam (List (Expr × Nat × Expr))) (cs : outParam (List (Expr × Expr))) (env : outParam (List Int)) :
    Prop where
  sound : e₁.eval env = a ∧ e₂.eval env = b ∧ RulesEval env es hs ∧ CofsEval env cs hc

instance curveGoal (a b : Int) (hs : List (Int × Nat × Int)) (hc : List (Int × Int)) (l₁ l₂ l₃ l₄ : List Int)
    (e₁ e₂ : Expr) (es : List (Expr × Nat × Expr)) (cs : List (Expr × Expr)) [h₁ : ReifyInt a [] l₁ e₁]
    [h₂ : ReifyInt b l₁ l₂ e₂] [h₃ : ReifyRules hs l₂ l₃ es] [h₄ : ReifyCofs hc l₃ l₄ cs] :
    CurveGoal a b hs hc e₁ e₂ es cs l₄.reverse where
  sound := by
    have x₄ := h₄.sound []
    rw [List.append_nil] at x₄
    obtain ⟨s₃, e₃⟩ := rev_ext h₄.ext []
    rw [List.append_nil] at e₃
    have x₃ := h₃.sound s₃
    rw [← e₃] at x₃
    obtain ⟨s₂, e₂'⟩ := rev_ext (ext_trans h₃.ext h₄.ext) []
    rw [List.append_nil] at e₂'
    have x₂ := h₂.sound s₂
    rw [← e₂'] at x₂
    obtain ⟨s₁, e₁'⟩ := rev_ext (ext_trans h₂.ext (ext_trans h₃.ext h₄.ext)) []
    rw [List.append_nil] at e₁'
    have x₁ := h₁.sound s₁
    rw [← e₁'] at x₁
    exact ⟨x₁, x₂, x₃, x₄⟩

theorem curve_mod_of {p : Nat} {a b : Int} {hs : List (Int × Nat × Int)} {hc : List (Int × Int)}
    (fuel : Nat) (hh : Hyps p hs) (hk : Cofs p hc) {e₁ e₂ : Expr} {es : List (Expr × Nat × Expr)}
    {cs : List (Expr × Expr)} {env : List Int} [h : CurveGoal a b hs hc e₁ e₂ es cs env]
    (hchk : curveCheck fuel e₁ e₂ es cs = true) : MEq p a b := by
  obtain ⟨x₁, x₂, x₃, x₄⟩ := h.sound
  rw [← x₁, ← x₂]
  exact curveCheck_sound x₃ x₄ hh hk hchk

/-! ## Tactic -/

/-- `curve_mod [h₁, …] [k₁ * c₁, …]` proves `MEq p a b` from rewrite
hypotheses `hᵢ : MEq p (y ^ d) f` and hypotheses `kⱼ : MEq p E 0` with
cofactors `cⱼ`. -/
syntax (name := curveMod) "curve_mod" ("(" &"fuel" " := " num ")")? "[" term,* "]" "[" ringModCert,* "]" :
  tactic

macro_rules
  | `(tactic| curve_mod [$hs,*] [$cs,*]) => `(tactic| curve_mod (fuel := 2) [$hs,*] [$cs,*])
  | `(tactic| curve_mod (fuel := $n) [$hs,*] [$cs,*]) => do
    let hh ← hs.getElems.foldrM (fun h acc => `(C3.Ring.Hyps.cons $h $acc)) (← `(C3.Ring.Hyps.nil))
    let hk ← cs.getElems.foldrM (fun (c : Lean.TSyntax `C3.Ring.ringModCert) acc =>
      match c with
      | `(ringModCert| $h:term * $k:term) => `(C3.Ring.Cofs.cons $h $k $acc)
      | _ => Lean.Macro.throwUnsupported) (← `(C3.Ring.Cofs.nil))
    `(tactic| (
      set_option synthInstance.maxSize 1000000 in
      set_option synthInstance.maxHeartbeats 0 in
      refine C3.Ring.curve_mod_of $n $hh $hk ?_
      decide +kernel))

end C3.Ring
