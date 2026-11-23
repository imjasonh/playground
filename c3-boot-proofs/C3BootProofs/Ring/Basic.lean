/-!
# Polynomial normal forms over `Int`

The reflected syntax, normal forms, and soundness proofs behind the
`ring_eq` and `ring_mod` tactics in `C3BootProofs.Ring.Tactic`.

`Expr` is a polynomial expression over `Int` whose atoms are indexed by
`Nat` into an environment. `Expr.toPoly n` normalizes it to a `Poly`: a
list of terms sorted strictly by a lexicographic monomial order, each with
a coefficient reduced modulo `n` and not zero. With `n = 0` the
coefficients are exact, because `c % 0 = c`. `Expr.toPoly_sound` proves
that the normal form evaluates to the same value as the expression, modulo
`n`.

The kernel evaluates `toPoly`, so the functions it reaches are written
with recursors (`Mon.rec`, `Poly.rec`, `Nat.rec`, `Bool.rec`) and with
`Int` and `Nat` operations that reduce to the kernel's accelerated `Nat`
primitives. The code generator doesn't support recursors, so they're
`noncomputable`: only the kernel runs them.
-/

namespace C3.Ring

/-- A polynomial expression over `Int`. `var i` is the `i`th atom. -/
inductive Expr where
  | const (c : Int)
  | var (i : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (k : Nat)
  deriving Inhabited, Repr

/-- A monomial: `cons x k m` is `x ^ k * m`, with the variables strictly
increasing and every exponent positive. -/
inductive Mon where
  | one
  | cons (x k : Nat) (m : Mon)
  deriving Inhabited, Repr

/-- A polynomial: `term c m p` is `c * m + p`, with the monomials strictly
decreasing in `Mon.cmp` and every coefficient reduced and not zero. -/
inductive Poly where
  | zero
  | term (c : Int) (m : Mon) (p : Poly)
  deriving Inhabited, Repr

/-! ## Evaluation -/

/-- The `i`th atom of `env`, or `0` past its end. -/
noncomputable def get (env : List Int) (i : Nat) : Int :=
  List.rec (motive := fun _ => Nat → Int) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Int) x (fun j _ => ih j) i) env i

theorem get_nil (i : Nat) : get [] i = 0 := rfl
theorem get_cons_zero (x : Int) (xs : List Int) : get (x :: xs) 0 = x := rfl
theorem get_cons_succ (x : Int) (xs : List Int) (i : Nat) :
    get (x :: xs) (i + 1) = get xs i := rfl

/-- The value of an expression. -/
noncomputable def Expr.eval (env : List Int) (e : Expr) : Int :=
  Expr.rec (motive := fun _ => Int) (fun c => c) (fun i => get env i)
    (fun _ _ a b => a + b) (fun _ _ a b => a - b) (fun _ a => -a)
    (fun _ _ a b => a * b) (fun _ k a => a ^ k) e

/-- The value of a monomial. -/
noncomputable def Mon.eval (env : List Int) (m : Mon) : Int :=
  Mon.rec (motive := fun _ => Int) 1 (fun x k _ ih => get env x ^ k * ih) m

/-- The value of a polynomial. -/
noncomputable def Poly.eval (env : List Int) (p : Poly) : Int :=
  Poly.rec (motive := fun _ => Int) 0 (fun c m _ ih => c * m.eval env + ih) p

/-! ## Kernel functions -/

/-- `a == b`, by the constructors. -/
noncomputable def intBeq (a b : Int) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun x => Int.rec (motive := fun _ => Bool) (fun y => Nat.beq x y) (fun _ => false) b)
    (fun x => Int.rec (motive := fun _ => Bool) (fun _ => false) (fun y => Nat.beq x y) b) a

/-- `c == 0`, by the constructors. -/
noncomputable def intIsZero (c : Int) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun x => Nat.beq x 0) (fun _ => false) c

/-- The product of two monomials: their variable lists merged, with the
exponents of a shared variable added. -/
noncomputable def Mon.mul (m₁ : Mon) : Mon → Mon :=
  Mon.rec (motive := fun _ => Mon → Mon) (fun m₂ => m₂)
    (fun x k m₁ ih m₂ =>
      Mon.rec (motive := fun _ => Mon) (Mon.cons x k m₁)
        (fun y l m₂ ih₂ =>
          Bool.rec (motive := fun _ => Mon)
            (Bool.rec (motive := fun _ => Mon) (Mon.cons x (Nat.add k l) (ih m₂))
              (Mon.cons y l ih₂) (Nat.blt y x))
            (Mon.cons x k (ih (Mon.cons y l m₂))) (Nat.blt x y))
        m₂)
    m₁

/-- The lexicographic monomial order, with lower-indexed variables more
significant. It respects multiplication, so `mulTerm` keeps a polynomial
sorted. -/
noncomputable def Mon.cmp (m₁ : Mon) : Mon → Ordering :=
  Mon.rec (motive := fun _ => Mon → Ordering)
    (fun m₂ => Mon.rec (motive := fun _ => Ordering) .eq (fun _ _ _ _ => .lt) m₂)
    (fun x k _ ih m₂ =>
      Mon.rec (motive := fun _ => Ordering) .gt
        (fun y l m₂ _ =>
          Bool.rec (motive := fun _ => Ordering)
            (Bool.rec (motive := fun _ => Ordering)
              (Bool.rec (motive := fun _ => Ordering)
                (Bool.rec (motive := fun _ => Ordering) (ih m₂) .gt (Nat.blt l k))
                .lt (Nat.blt k l))
              .lt (Nat.blt y x))
            .gt (Nat.blt x y))
        m₂)
    m₁

/-- Equality of monomials. -/
noncomputable def Mon.beq (m₁ : Mon) : Mon → Bool :=
  Mon.rec (motive := fun _ => Mon → Bool)
    (fun m₂ => Mon.rec (motive := fun _ => Bool) true (fun _ _ _ _ => false) m₂)
    (fun x k _ ih m₂ =>
      Mon.rec (motive := fun _ => Bool) false
        (fun y l m₂ _ =>
          Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false (ih m₂) (Nat.beq k l)) (Nat.beq x y))
        m₂)
    m₁

/-- `c * m + p`, or `p` when `c` is zero. -/
noncomputable def Poly.mkTerm (c : Int) (m : Mon) (p : Poly) : Poly :=
  Bool.rec (motive := fun _ => Poly) (Poly.term c m p) p (intIsZero c)

/-- `c * m` with `c` reduced modulo `n`. -/
noncomputable def Poly.monomial (n c : Int) (m : Mon) : Poly := Poly.mkTerm (Int.emod c n) m Poly.zero

/-- The sum of two polynomials, by merging their terms. -/
noncomputable def Poly.add (n : Int) (p : Poly) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly → Poly) (fun q => q)
    (fun c m p ih q =>
      Poly.rec (motive := fun _ => Poly) (Poly.term c m p)
        (fun d m' q ih₂ =>
          Ordering.rec (motive := fun _ => Poly)
            (Poly.term d m' ih₂)
            (Poly.mkTerm (Int.emod (Int.add c d) n) m (ih q))
            (Poly.term c m (ih (Poly.term d m' q)))
            (Mon.cmp m m'))
        q)
    p

/-- `c * m * q`. -/
noncomputable def Poly.mulTerm (n c : Int) (m : Mon) (q : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.zero
    (fun d m' _ ih => Poly.mkTerm (Int.emod (Int.mul c d) n) (Mon.mul m m') ih) q

/-- The product of two polynomials. -/
noncomputable def Poly.mul (n : Int) (p q : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.zero
    (fun c m _ ih => Poly.add n (Poly.mulTerm n c m q) ih) p

/-- `-p`. -/
noncomputable def Poly.neg (n : Int) (p : Poly) : Poly := Poly.mulTerm n (-1) Mon.one p

/-- `p ^ k`, by `k` multiplications. -/
noncomputable def Poly.pow (n : Int) (p : Poly) (k : Nat) : Poly :=
  Nat.rec (motive := fun _ => Poly) (Poly.monomial n 1 Mon.one)
    (fun _ ih => Poly.mul n p ih) k

/-- The normal form of an expression, with coefficients modulo `n`. -/
noncomputable def Expr.toPoly (n : Int) (e : Expr) : Poly :=
  Expr.rec (motive := fun _ => Poly)
    (fun c => Poly.monomial n c Mon.one)
    (fun i => Poly.monomial n 1 (Mon.cons i 1 Mon.one))
    (fun _ _ a b => Poly.add n a b)
    (fun _ _ a b => Poly.add n a (Poly.neg n b))
    (fun _ a => Poly.neg n a)
    (fun _ _ a b => Poly.mul n a b)
    (fun _ k a => Poly.pow n a k)
    e

/-- Equality of polynomials. -/
noncomputable def Poly.beq (p : Poly) : Poly → Bool :=
  Poly.rec (motive := fun _ => Poly → Bool)
    (fun q => Poly.rec (motive := fun _ => Bool) true (fun _ _ _ _ => false) q)
    (fun c m _ ih q =>
      Poly.rec (motive := fun _ => Bool) false
        (fun d m' q _ =>
          Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false (ih q) (Mon.beq m m'))
            (intBeq c d))
        q)
    p

/-! ## `Int` arithmetic -/

theorem emod_add_cong {n a b a' b' : Int} (ha : a % n = a' % n) (hb : b % n = b' % n) :
    (a + b) % n = (a' + b') % n := by
  rw [Int.add_emod, ha, hb, ← Int.add_emod]

theorem emod_mul_cong {n a b a' b' : Int} (ha : a % n = a' % n) (hb : b % n = b' % n) :
    (a * b) % n = (a' * b') % n := by
  rw [Int.mul_emod, ha, hb, ← Int.mul_emod]

theorem emod_neg_cong {n a a' : Int} (ha : a % n = a' % n) : (-a) % n = (-a') % n := by
  rw [← Int.neg_one_mul a, ← Int.neg_one_mul a']
  exact emod_mul_cong rfl ha

theorem emod_pow_cong {n a a' : Int} (ha : a % n = a' % n) (k : Nat) :
    (a ^ k) % n = (a' ^ k) % n := by
  induction k with
  | zero => rw [Int.pow_zero, Int.pow_zero]
  | succ k ih => rw [Int.pow_succ, Int.pow_succ]; exact emod_mul_cong ih ha

theorem emod_emod_cong (n a : Int) : (a % n) % n = a % n := Int.emod_emod a n

theorem nat_eq_of_not_lt {x y : Nat} (h₁ : ¬ x < y) (h₂ : ¬ y < x) : x = y :=
  Nat.le_antisymm (Nat.ge_of_not_lt h₂) (Nat.ge_of_not_lt h₁)

theorem not_lt_of_blt_false {x y : Nat} (h : Nat.blt x y = false) : ¬ x < y := by
  intro hlt
  have : Nat.blt x y = true := Nat.ble_eq_true_of_le hlt
  rw [h] at this
  exact Bool.false_ne_true this

theorem intBeq_eq {a b : Int} (h : intBeq a b = true) : a = b := by
  cases a with
  | ofNat x => cases b with
    | ofNat y => exact congrArg Int.ofNat (Nat.eq_of_beq_eq_true h)
    | negSucc y => exact absurd h Bool.false_ne_true
  | negSucc x => cases b with
    | ofNat y => exact absurd h Bool.false_ne_true
    | negSucc y => exact congrArg Int.negSucc (Nat.eq_of_beq_eq_true h)

theorem intIsZero_eq {c : Int} (h : intIsZero c = true) : c = 0 := by
  cases c with
  | ofNat x => exact congrArg Int.ofNat (Nat.eq_of_beq_eq_true h)
  | negSucc x => exact absurd h Bool.false_ne_true

/-! ## Soundness -/

theorem Mon.eval_one (env : List Int) : Mon.one.eval env = 1 := rfl

theorem Mon.eval_cons (env : List Int) (x k : Nat) (m : Mon) :
    (Mon.cons x k m).eval env = get env x ^ k * m.eval env := rfl

theorem Mon.mul_one_left (m : Mon) : Mon.mul Mon.one m = m := rfl

theorem Mon.mul_cons_one (x k : Nat) (m : Mon) :
    Mon.mul (Mon.cons x k m) Mon.one = Mon.cons x k m := rfl

theorem Mon.mul_cons_cons (x k y l : Nat) (m₁ m₂ : Mon) :
    Mon.mul (Mon.cons x k m₁) (Mon.cons y l m₂) =
      Bool.rec (motive := fun _ => Mon)
        (Bool.rec (motive := fun _ => Mon) (Mon.cons x (Nat.add k l) (Mon.mul m₁ m₂))
          (Mon.cons y l (Mon.mul (Mon.cons x k m₁) m₂)) (Nat.blt y x))
        (Mon.cons x k (Mon.mul m₁ (Mon.cons y l m₂))) (Nat.blt x y) := rfl

theorem Mon.eval_mul (env : List Int) (m₁ m₂ : Mon) :
    (Mon.mul m₁ m₂).eval env = m₁.eval env * m₂.eval env := by
  induction m₁ generalizing m₂ with
  | one => rw [mul_one_left, eval_one, Int.one_mul]
  | cons x k m₁ ih =>
    induction m₂ with
    | one => rw [mul_cons_one, eval_one, Int.mul_one]
    | cons y l m₂ ih₂ =>
      rw [mul_cons_cons]
      cases hxy : Nat.blt x y with
      | true =>
        show (Mon.cons x k (Mon.mul m₁ (Mon.cons y l m₂))).eval env = _
        simp only [eval_cons, ih, Int.mul_assoc]
      | false =>
        cases hyx : Nat.blt y x with
        | true =>
          show (Mon.cons y l (Mon.mul (Mon.cons x k m₁) m₂)).eval env = _
          simp only [eval_cons, ih₂, Int.mul_assoc, Int.mul_left_comm]
        | false =>
          show (Mon.cons x (Nat.add k l) (Mon.mul m₁ m₂)).eval env = _
          have hx : x = y :=
            nat_eq_of_not_lt (not_lt_of_blt_false hxy) (not_lt_of_blt_false hyx)
          subst hx
          simp only [eval_cons, ih, Nat.add_eq, Int.pow_add, Int.mul_assoc, Int.mul_left_comm]

theorem Poly.eval_zero (env : List Int) : Poly.zero.eval env = 0 := rfl

theorem Poly.eval_term (env : List Int) (c : Int) (m : Mon) (p : Poly) :
    (Poly.term c m p).eval env = c * m.eval env + p.eval env := rfl

theorem Poly.eval_mkTerm (env : List Int) (c : Int) (m : Mon) (p : Poly) :
    (Poly.mkTerm c m p).eval env = c * m.eval env + p.eval env := by
  unfold Poly.mkTerm
  cases h : intIsZero c with
  | false => rfl
  | true =>
    show p.eval env = _
    rw [intIsZero_eq h, Int.zero_mul, Int.zero_add]

theorem Poly.eval_monomial (env : List Int) (n c : Int) (m : Mon) :
    (Poly.monomial n c m).eval env % n = (c * m.eval env) % n := by
  unfold Poly.monomial
  rw [eval_mkTerm, eval_zero, Int.add_zero]
  exact emod_mul_cong (emod_emod_cong n c) rfl

theorem Poly.add_zero_left (n : Int) (q : Poly) : Poly.add n Poly.zero q = q := rfl

theorem Poly.add_term_zero (n c : Int) (m : Mon) (p : Poly) :
    Poly.add n (Poly.term c m p) Poly.zero = Poly.term c m p := rfl

theorem Poly.add_term_term (n c d : Int) (m m' : Mon) (p q : Poly) :
    Poly.add n (Poly.term c m p) (Poly.term d m' q) =
      Ordering.rec (motive := fun _ => Poly)
        (Poly.term d m' (Poly.add n (Poly.term c m p) q))
        (Poly.mkTerm (Int.emod (Int.add c d) n) m (Poly.add n p q))
        (Poly.term c m (Poly.add n p (Poly.term d m' q)))
        (Mon.cmp m m') := rfl

theorem Mon.cmp_cons_cons (x k y l : Nat) (m₁ m₂ : Mon) :
    Mon.cmp (Mon.cons x k m₁) (Mon.cons y l m₂) =
      Bool.rec (motive := fun _ => Ordering)
        (Bool.rec (motive := fun _ => Ordering)
          (Bool.rec (motive := fun _ => Ordering)
            (Bool.rec (motive := fun _ => Ordering) (Mon.cmp m₁ m₂) .gt (Nat.blt l k))
            .lt (Nat.blt k l))
          .lt (Nat.blt y x))
        .gt (Nat.blt x y) := rfl

theorem Mon.eq_of_cmp_eq {m₁ m₂ : Mon} (h : Mon.cmp m₁ m₂ = .eq) : m₁ = m₂ := by
  induction m₁ generalizing m₂ with
  | one =>
    cases m₂ with
    | one => rfl
    | cons y l m₂ => exact Ordering.noConfusion h
  | cons x k m₁ ih =>
    cases m₂ with
    | one => exact Ordering.noConfusion h
    | cons y l m₂ =>
      rw [cmp_cons_cons] at h
      cases hxy : Nat.blt x y <;> rw [hxy] at h
      · cases hyx : Nat.blt y x <;> rw [hyx] at h
        · cases hkl : Nat.blt k l <;> rw [hkl] at h
          · cases hlk : Nat.blt l k <;> rw [hlk] at h
            · have hx := nat_eq_of_not_lt (not_lt_of_blt_false hxy) (not_lt_of_blt_false hyx)
              have hk := nat_eq_of_not_lt (not_lt_of_blt_false hkl) (not_lt_of_blt_false hlk)
              rw [hx, hk, ih h]
            · exact Ordering.noConfusion h
          · exact Ordering.noConfusion h
        · exact Ordering.noConfusion h
      · exact Ordering.noConfusion h

theorem Poly.eval_add (env : List Int) (n : Int) (p q : Poly) :
    (Poly.add n p q).eval env % n = (p.eval env + q.eval env) % n := by
  induction p generalizing q with
  | zero => rw [add_zero_left, eval_zero, Int.zero_add]
  | term c m p ih =>
    induction q with
    | zero => rw [add_term_zero, eval_zero, Int.add_zero]
    | term d m' q ih₂ =>
      rw [add_term_term]
      cases hc : Mon.cmp m m' with
      | lt =>
        show (Poly.term d m' (Poly.add n (Poly.term c m p) q)).eval env % n = _
        rw [eval_term]
        refine (emod_add_cong rfl ih₂).trans ?_
        simp only [eval_term, Int.add_assoc, Int.add_left_comm]
      | eq =>
        show (Poly.mkTerm (Int.emod (Int.add c d) n) m (Poly.add n p q)).eval env % n = _
        rw [eval_mkTerm]
        refine (emod_add_cong (emod_mul_cong (emod_emod_cong n (Int.add c d)) rfl)
          (ih q)).trans ?_
        rw [← Mon.eq_of_cmp_eq hc]
        simp only [eval_term, Int.add_def, Int.add_mul, Int.add_assoc, Int.add_left_comm]
      | gt =>
        show (Poly.term c m (Poly.add n p (Poly.term d m' q))).eval env % n = _
        rw [eval_term]
        refine (emod_add_cong rfl (ih _)).trans ?_
        simp only [eval_term, Int.add_assoc]

theorem Poly.mulTerm_zero (n c : Int) (m : Mon) : Poly.mulTerm n c m Poly.zero = Poly.zero := rfl

theorem Poly.mulTerm_term (n c d : Int) (m m' : Mon) (q : Poly) :
    Poly.mulTerm n c m (Poly.term d m' q) =
      Poly.mkTerm (Int.emod (Int.mul c d) n) (Mon.mul m m') (Poly.mulTerm n c m q) := rfl

theorem Poly.eval_mulTerm (env : List Int) (n c : Int) (m : Mon) (q : Poly) :
    (Poly.mulTerm n c m q).eval env % n = (c * m.eval env * q.eval env) % n := by
  induction q with
  | zero => rw [mulTerm_zero, eval_zero, Int.mul_zero]
  | term d m' q ih =>
    rw [mulTerm_term, eval_mkTerm]
    refine (emod_add_cong (emod_mul_cong (emod_emod_cong n (Int.mul c d)) rfl) ih).trans ?_
    simp only [eval_term, Mon.eval_mul, Int.mul_def, Int.mul_add, Int.mul_assoc,
      Int.mul_left_comm]

theorem Poly.mul_zero_left (n : Int) (q : Poly) : Poly.mul n Poly.zero q = Poly.zero := rfl

theorem Poly.mul_term (n c : Int) (m : Mon) (p q : Poly) :
    Poly.mul n (Poly.term c m p) q = Poly.add n (Poly.mulTerm n c m q) (Poly.mul n p q) := rfl

theorem Poly.eval_mul (env : List Int) (n : Int) (p q : Poly) :
    (Poly.mul n p q).eval env % n = (p.eval env * q.eval env) % n := by
  induction p with
  | zero => rw [mul_zero_left, eval_zero, Int.zero_mul]
  | term c m p ih =>
    rw [mul_term]
    refine (eval_add env n _ _).trans ?_
    refine (emod_add_cong (eval_mulTerm env n c m q) ih).trans ?_
    simp only [eval_term, Int.add_mul]

theorem Poly.eval_neg (env : List Int) (n : Int) (p : Poly) :
    (Poly.neg n p).eval env % n = (-p.eval env) % n := by
  unfold Poly.neg
  rw [eval_mulTerm, Mon.eval_one, Int.mul_one, Int.neg_one_mul]

theorem Poly.pow_zero (n : Int) (p : Poly) : Poly.pow n p 0 = Poly.monomial n 1 Mon.one := rfl

theorem Poly.pow_succ (n : Int) (p : Poly) (k : Nat) :
    Poly.pow n p (k + 1) = Poly.mul n p (Poly.pow n p k) := rfl

theorem Poly.eval_pow (env : List Int) (n : Int) (p : Poly) (k : Nat) :
    (Poly.pow n p k).eval env % n = (p.eval env ^ k) % n := by
  induction k with
  | zero => rw [pow_zero, eval_monomial, Mon.eval_one, Int.mul_one, Int.pow_zero]
  | succ k ih =>
    rw [pow_succ]
    refine (eval_mul env n _ _).trans ?_
    refine (emod_mul_cong rfl ih).trans ?_
    rw [Int.pow_succ, Int.mul_comm]

theorem Expr.eval_const (env : List Int) (c : Int) : (Expr.const c).eval env = c := rfl
theorem Expr.eval_var (env : List Int) (i : Nat) : (Expr.var i).eval env = get env i := rfl
theorem Expr.eval_add (env : List Int) (a b : Expr) :
    (Expr.add a b).eval env = a.eval env + b.eval env := rfl
theorem Expr.eval_sub (env : List Int) (a b : Expr) :
    (Expr.sub a b).eval env = a.eval env - b.eval env := rfl
theorem Expr.eval_neg (env : List Int) (a : Expr) : (Expr.neg a).eval env = -a.eval env := rfl
theorem Expr.eval_mul (env : List Int) (a b : Expr) :
    (Expr.mul a b).eval env = a.eval env * b.eval env := rfl
theorem Expr.eval_pow (env : List Int) (a : Expr) (k : Nat) :
    (Expr.pow a k).eval env = a.eval env ^ k := rfl

/-- The normal form evaluates to the expression's value modulo `n`. -/
theorem Expr.toPoly_sound (env : List Int) (n : Int) (e : Expr) :
    (e.toPoly n).eval env % n = e.eval env % n := by
  induction e with
  | const c =>
    show (Poly.monomial n c Mon.one).eval env % n = _
    rw [Poly.eval_monomial, Mon.eval_one, Int.mul_one, eval_const]
  | var i =>
    show (Poly.monomial n 1 (Mon.cons i 1 Mon.one)).eval env % n = _
    rw [Poly.eval_monomial, Mon.eval_cons, Mon.eval_one, Int.mul_one, Int.one_mul,
      Int.pow_one, eval_var]
  | add a b iha ihb =>
    show (Poly.add n (a.toPoly n) (b.toPoly n)).eval env % n = _
    rw [Poly.eval_add, eval_add]
    exact emod_add_cong iha ihb
  | sub a b iha ihb =>
    show (Poly.add n (a.toPoly n) (Poly.neg n (b.toPoly n))).eval env % n = _
    rw [Poly.eval_add, eval_sub, Int.sub_eq_add_neg]
    exact emod_add_cong iha ((Poly.eval_neg env n _).trans (emod_neg_cong ihb))
  | neg a iha =>
    show (Poly.neg n (a.toPoly n)).eval env % n = _
    rw [eval_neg]
    exact (Poly.eval_neg env n _).trans (emod_neg_cong iha)
  | mul a b iha ihb =>
    show (Poly.mul n (a.toPoly n) (b.toPoly n)).eval env % n = _
    rw [Poly.eval_mul, eval_mul]
    exact emod_mul_cong iha ihb
  | pow a k iha =>
    show (Poly.pow n (a.toPoly n) k).eval env % n = _
    rw [Poly.eval_pow, eval_pow]
    exact emod_pow_cong iha k

theorem Mon.eq_of_beq {m₁ m₂ : Mon} (h : Mon.beq m₁ m₂ = true) : m₁ = m₂ := by
  induction m₁ generalizing m₂ with
  | one =>
    cases m₂ with
    | one => rfl
    | cons y l m₂ => exact absurd h Bool.false_ne_true
  | cons x k m₁ ih =>
    cases m₂ with
    | one => exact absurd h Bool.false_ne_true
    | cons y l m₂ =>
      change Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (Mon.beq m₁ m₂) (Nat.beq k l))
        (Nat.beq x y) = true at h
      cases hxy : Nat.beq x y <;> rw [hxy] at h
      · exact absurd h Bool.false_ne_true
      · cases hkl : Nat.beq k l <;> rw [hkl] at h
        · exact absurd h Bool.false_ne_true
        · rw [Nat.eq_of_beq_eq_true hxy, Nat.eq_of_beq_eq_true hkl, ih h]

theorem Poly.eq_of_beq {p q : Poly} (h : Poly.beq p q = true) : p = q := by
  induction p generalizing q with
  | zero =>
    cases q with
    | zero => rfl
    | term d m' q => exact absurd h Bool.false_ne_true
  | term c m p ih =>
    cases q with
    | zero => exact absurd h Bool.false_ne_true
    | term d m' q =>
      change Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (Poly.beq p q) (Mon.beq m m'))
        (intBeq c d) = true at h
      cases hcd : intBeq c d <;> rw [hcd] at h
      · exact absurd h Bool.false_ne_true
      · cases hm : Mon.beq m m' <;> rw [hm] at h
        · exact absurd h Bool.false_ne_true
        · rw [intBeq_eq hcd, Mon.eq_of_beq hm, ih h]

/-! ## Main theorems -/

/-- Two expressions with equal normal forms modulo `n` are congruent modulo
`n`. -/
theorem emod_eq_of_beq (n : Int) (e₁ e₂ : Expr) (env : List Int)
    (h : Poly.beq (e₁.toPoly n) (e₂.toPoly n) = true) :
    e₁.eval env % n = e₂.eval env % n := by
  rw [← Expr.toPoly_sound env n e₁, ← Expr.toPoly_sound env n e₂, Poly.eq_of_beq h]

/-- Two expressions with equal normal forms are equal. -/
theorem eq_of_beq (e₁ e₂ : Expr) (env : List Int)
    (h : Poly.beq (e₁.toPoly 0) (e₂.toPoly 0) = true) : e₁.eval env = e₂.eval env := by
  have := emod_eq_of_beq 0 e₁ e₂ env h
  rwa [Int.emod_zero, Int.emod_zero] at this

/-! ## Certificates -/

/-- `a ≡ b` modulo `n` from `a - b = k * n`. -/
theorem emod_eq_of_sub_eq_mul {a b k n : Int} (h : a - b = k * n) : a % n = b % n := by
  have : a = b + k * n := by rw [← h, Int.add_comm, Int.sub_add_cancel]
  rw [this, Int.add_mul_emod_self_right]

/-- `a ≡ b` modulo `n` from `a ≡ b + t` and `t ≡ 0`. -/
theorem emod_eq_of_emod_eq_add {a b t n : Int} (h : a % n = (b + t) % n) (ht : t % n = 0) :
    a % n = b % n := by
  rw [h, Int.add_emod, ht, Int.add_zero, Int.emod_emod]

theorem emod_add_eq_zero {x y n : Int} (hx : x % n = 0) (hy : y % n = 0) :
    (x + y) % n = 0 := by
  rw [Int.add_emod, hx, hy]; rfl

theorem emod_mul_eq_zero {x n : Int} (hx : x % n = 0) (c : Int) : (x * c) % n = 0 := by
  rw [Int.mul_emod, hx, Int.zero_mul]; rfl

theorem emod_eq_zero_of_emod_eq {a n : Int} (h : a % n = 0 % n) : a % n = 0 := by
  rw [h, Int.zero_emod]

theorem nat_emod_eq_zero_of_emod_eq {a n : Nat} (h : a % n = 0 % n) : a % n = 0 := by
  rw [h, Nat.zero_mod]

/-- `a ≡ b` modulo `n` over `Nat`, from the same congruence over `Int`. -/
theorem nat_emod_eq_of_int {a b n : Nat} (h : (a : Int) % (n : Int) = (b : Int) % (n : Int)) :
    a % n = b % n := by
  apply Int.ofNat.inj
  rw [Int.ofNat_eq_natCast, Int.natCast_emod, Int.ofNat_eq_natCast, Int.natCast_emod]
  exact h

end C3.Ring
