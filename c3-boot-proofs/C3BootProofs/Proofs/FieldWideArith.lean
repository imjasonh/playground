import C3BootProofs.Proofs.FieldSubInnerMain

/-!
# Arithmetic for `widening_mul_fixed::<8, 8>`

`wmWord` and `wmCarry` are the new accumulator word and carry from one step
of the schoolbook inner loop, in the compiled code's order, and `wm_step`
shows they add `y * x` to the word and carry. `accV` is the value of a run
of words, and `accV_store` says how a store changes it.
-/

namespace C3.RV32

theorem mul_mulhu (x y : Word) :
    (aluEval .mul x y).toNat + 2 ^ 32 * (aluEval .mulhu x y).toNat = x.toNat * y.toNat := by
  show (x * y).toNat + 2 ^ 32 * (BitVec.ofNat 32 ((x.toNat * y.toNat) / 2 ^ 32)).toNat = _
  have hx := x.isLt; have hy := y.isLt
  have hp : x.toNat * y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_lt hx hy
  have hq : x.toNat * y.toNat / 2 ^ 32 < 2 ^ 32 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hp
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  exact Nat.mod_add_div _ _

/-- The new accumulator word and carry from one step of `widening_mul_fixed`'s
inner loop, in the compiled code's order: `x * y + w + t`. -/
def wmWord (x y w t : Word) : Word := aluEval .add (aluEval .mul x y) (aluEval .add t w)

def wmCarry (x y w t : Word) : Word :=
  aluEval .add (aluEval .sltu (wmWord x y w t) (aluEval .add t w))
    (aluEval .add (aluEval .mulhu x y) (aluEval .sltu (aluEval .add t w) w))

theorem wm_step (x y w t : Word) :
    (wmWord x y w t).toNat + 2 ^ 32 * (wmCarry x y w t).toNat = x.toNat * y.toNat + w.toNat + t.toNat := by
  unfold wmCarry wmWord
  have e0 := mul_mulhu x y
  have e1 := add_carry t w
  have e2 := add_carry (aluEval .mul x y) (aluEval .add t w)
  generalize aluEval .mulhu x y = hi at e0 ⊢
  generalize aluEval .mul x y = lo at e0 e2 ⊢
  generalize aluEval .add t w = t1 at e1 e2 ⊢
  generalize aluEval .sltu t1 w = c1 at e1 ⊢
  generalize aluEval .add lo t1 = lo' at e2 ⊢
  generalize aluEval .sltu lo' t1 = c2 at e2 ⊢
  have b1 : c1.toNat ≤ 1 := by
    have := e1; have := t1.isLt; have := t.isLt; have := w.isLt
    rcases Nat.lt_or_ge c1.toNat 2 with h | h
    · omega
    · exfalso; omega
  have b2 : c2.toNat ≤ 1 := by
    have := e2; have := lo'.isLt; have := lo.isLt; have := t1.isLt
    rcases Nat.lt_or_ge c2.toNat 2 with h | h
    · omega
    · exfalso; omega
  have hx := x.isLt; have hy := y.isLt
  have hP : x.toNat * y.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hw := w.isLt; have ht := t.isLt; have hl := lo.isLt; have hl' := lo'.isLt; have ht1 := t1.isLt
  generalize x.toNat * y.toNat = P at e0 hP ⊢
  have hhi : (aluEval .add hi c1).toNat = hi.toNat + c1.toNat := by
    show (hi + c1).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [show (aluEval .add c2 (aluEval .add hi c1)).toNat = c2.toNat + (aluEval .add hi c1).toNat by
    show (c2 + aluEval .add hi c1).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)], hhi]
  omega

/-- The value of the `n` words at `b`, little-endian. -/
def accV (M : Word → BitVec 8) (b : Word) : Nat → Nat
  | 0 => 0
  | n + 1 => accV M b n + (memLoad32 M (b + BitVec.ofNat 32 (4 * n))).toNat * 2 ^ (32 * n)

theorem accV_congr {M M' : Word → BitVec 8} {b : Word} :
    ∀ n, (∀ i, i < n → memLoad32 M' (b + BitVec.ofNat 32 (4 * i)) = memLoad32 M (b + BitVec.ofNat 32 (4 * i))) →
      accV M' b n = accV M b n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [accV]; rw [accV_congr n fun i hi => h i (by omega), h n (by omega)]

theorem accV_store_above {M : Word → BitVec 8} {b v : Word} {k : Nat} (hw : b.toNat + 4 * (k + 1) ≤ 2 ^ 32) :
    ∀ n, n ≤ k → accV (memStore32 M (b + BitVec.ofNat 32 (4 * k)) v) b n = accV M b n :=
  fun n hn => accV_congr n fun i hi =>
    memLoad32_store32_sep (sep_offsets b (.inr (by omega)) (by omega) (by omega))

/-- **A store changes the value by the difference at its place.** -/
theorem accV_store {M : Word → BitVec 8} {b v : Word} {k : Nat} :
    ∀ n, k < n → b.toNat + 4 * n ≤ 2 ^ 32 →
      accV (memStore32 M (b + BitVec.ofNat 32 (4 * k)) v) b n +
          (memLoad32 M (b + BitVec.ofNat 32 (4 * k))).toNat * 2 ^ (32 * k) =
        accV M b n + v.toNat * 2 ^ (32 * k)
  | 0, h, _ => absurd h (Nat.not_lt_zero k)
  | n + 1, h, hw => by
    simp only [accV]
    by_cases hk : k = n
    · subst hk
      rw [accV_store_above (by omega) k (Nat.le_refl k), memLoad32_store32_same]
      omega
    · have ih := accV_store (M := M) (b := b) (v := v) (k := k) n (by omega) (by omega)
      rw [memLoad32_store32_sep (sep_offsets b (c := 4 * k) (n := 4) (d := 4 * n) (k := 4) (.inl (by omega))
        (by omega) (by omega))]
      omega

end C3.RV32
