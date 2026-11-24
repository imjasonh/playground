import C3BootProofs.Proofs.Pv384CIt
import C3BootProofs.Proofs.LincombShiftMod8

/-!
# Safegcd: `d` and `e` stay below the modulus

The inversions in `sigstore::verify` and `p384_verify_prehash` run
Bernstein–Yang divsteps in batches of at most 62. A batch's matrix,
built from the identity by `dsStep`, has rows with `|u| + |v| ≤ 2 ^ n`
after `n` divsteps, so its 64-bit words never wrap. Applied to `d` and
`e` below the modulus `M` by `lincomb_int_reduce_shift_mod`, it leaves
values below `M` again: the sum and the multiple of `M` that makes it
divisible by `2 ^ n` are both below `M · 2 ^ n`, so the quotient is
below `M`, and the final conditional subtraction keeps it. None of this
depends on how many divsteps run or on whether `f` ends as ±1.
-/

namespace C3.RV32.Safegcd

open C3.RV32.Pv

/-- `|x| + |y| ≤ B`, as four linear inequalities. -/
def RowB (B x y : Int) : Prop := x + y ≤ B ∧ x - y ≤ B ∧ y - x ≤ B ∧ -x - y ≤ B

theorem i64_mod (x : Nat) : (x : Int) % 2 ^ 64 = i64Val x % 2 ^ 64 := by
  unfold i64Val; split <;> omega

theorem i64_eq {x : Nat} {z : Int} (hx : x < 2 ^ 64) (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63)
    (h : (x : Int) % 2 ^ 64 = z % 2 ^ 64) : i64Val x = z := by
  unfold i64Val; split <;> omega

theorem i64_dbl {x : Nat} (h1 : -2 ^ 61 ≤ i64Val x) (h2 : i64Val x ≤ 2 ^ 61) :
    i64Val (2 * x % 2 ^ 64) = 2 * i64Val x := by
  have := i64_mod x
  exact i64_eq (Nat.mod_lt _ (by decide)) (by omega) (by omega) (by omega)

theorem i64_add {x y : Nat} (h1 : -2 ^ 62 ≤ i64Val x + i64Val y) (h2 : i64Val x + i64Val y ≤ 2 ^ 62) :
    i64Val ((x + y) % 2 ^ 64) = i64Val x + i64Val y := by
  have := i64_mod x; have := i64_mod y
  exact i64_eq (Nat.mod_lt _ (by decide)) (by omega) (by omega) (by omega)

theorem i64_sub {x y : Nat} (hy : y < 2 ^ 64) (h1 : -2 ^ 62 ≤ i64Val x - i64Val y)
    (h2 : i64Val x - i64Val y ≤ 2 ^ 62) : i64Val ((x + 2 ^ 64 - y) % 2 ^ 64) = i64Val x - i64Val y := by
  have := i64_mod x; have := i64_mod y
  exact i64_eq (Nat.mod_lt _ (by decide)) (by omega) (by omega) (by omega)

/-- The matrix's words are below `2 ^ 64`, and each row, read as signed words, has `|·| + |·| ≤ B`. -/
def MB (B : Int) (s : Ds) : Prop :=
  s.u < 2 ^ 64 ∧ s.v < 2 ^ 64 ∧ s.q < 2 ^ 64 ∧ s.r < 2 ^ 64 ∧
    RowB B (i64Val s.u) (i64Val s.v) ∧ RowB B (i64Val s.q) (i64Val s.r)

theorem mb_step {B : Int} {s : Ds} (h : MB B s) (hB : 0 ≤ B) (hB' : B ≤ 2 ^ 61) : MB (2 * B) (dsStep s) := by
  obtain ⟨hu, hv, hq, hr, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := h
  have m : ∀ x : Nat, x % 2 ^ 64 < 2 ^ 64 := fun x => Nat.mod_lt _ (by decide)
  unfold dsStep MB
  split
  · dsimp only
    refine ⟨m _, m _, hq, hr, ?_, ?_⟩
    · rw [i64_dbl (by omega) (by omega), i64_dbl (by omega) (by omega)]
      exact ⟨by omega, by omega, by omega, by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega⟩
  · split
    · dsimp only
      refine ⟨m _, m _, m _, m _, ?_, ?_⟩
      · rw [i64_dbl (by omega) (by omega), i64_dbl (by omega) (by omega)]
        exact ⟨by omega, by omega, by omega, by omega⟩
      · rw [i64_sub hu (by omega) (by omega), i64_sub hv (by omega) (by omega)]
        exact ⟨by omega, by omega, by omega, by omega⟩
    · dsimp only
      refine ⟨m _, m _, m _, m _, ?_, ?_⟩
      · rw [i64_dbl (by omega) (by omega), i64_dbl (by omega) (by omega)]
        exact ⟨by omega, by omega, by omega, by omega⟩
      · rw [i64_add (by omega) (by omega), i64_add (by omega) (by omega)]
        exact ⟨by omega, by omega, by omega, by omega⟩

theorem mb_init (δ f g : Nat) : MB 1 ⟨δ, f, g, 1, 0, 0, 1⟩ := by
  unfold MB RowB
  dsimp only
  decide

theorem two_pow_le {k : Nat} (h : k ≤ 61) : (2 : Int) ^ k ≤ 2 ^ 61 := by
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
  exact_mod_cast this

theorem mb_iter : ∀ n k (s : Ds), MB (2 ^ k) s → k + n ≤ 62 → MB (2 ^ (k + n)) (dsIter n s)
  | 0, _, _, h, _ => h
  | n + 1, k, s, h, hk => by
    have h1 := mb_step h (by have := Int.pow_pos (m := k) (show (0 : Int) < 2 by decide); omega)
      (two_pow_le (by omega))
    rw [← Int.pow_succ'] at h1
    rw [show k + (n + 1) = k + 1 + n by omega]
    exact mb_iter n (k + 1) (dsStep s) h1 (by omega)

/-- **A batch's matrix**: after `n ≤ 62` divsteps from the identity, each row's entries, read as signed
64-bit words, have `|·| + |·| ≤ 2 ^ n`, whatever `δ`, `f`, and `g` are. -/
theorem batch_rows {n : Nat} (hn : n ≤ 62) (δ f g : Nat) :
    RowB (2 ^ n) (i64Val (dsIter n ⟨δ, f, g, 1, 0, 0, 1⟩).u) (i64Val (dsIter n ⟨δ, f, g, 1, 0, 0, 1⟩).v) ∧
    RowB (2 ^ n) (i64Val (dsIter n ⟨δ, f, g, 1, 0, 0, 1⟩).q) (i64Val (dsIter n ⟨δ, f, g, 1, 0, 0, 1⟩).r) := by
  have := mb_iter n 0 ⟨δ, f, g, 1, 0, 0, 1⟩ (mb_init δ f g) (by omega)
  rw [Nat.zero_add] at this
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2⟩

theorem rowB_natAbs {B x y : Int} (h : RowB B x y) : ((x.natAbs + y.natAbs : Nat) : Int) ≤ B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  omega

theorem lin_lt {D E u v : Int} {M s : Nat} (hD : D.natAbs < M) (hE : E.natAbs < M)
    (huv : u.natAbs + v.natAbs ≤ 2 ^ s) : (D * u + E * v).natAbs < M * 2 ^ s := by
  have h0 : 0 < 2 ^ s := Nat.two_pow_pos s
  have e : (M - 1) * 2 ^ s + 2 ^ s = M * 2 ^ s := by
    rw [← Nat.succ_mul, show (M - 1).succ = M by omega]
  calc (D * u + E * v).natAbs ≤ (D * u).natAbs + (E * v).natAbs := Int.natAbs_add_le _ _
    _ = D.natAbs * u.natAbs + E.natAbs * v.natAbs := by rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ (M - 1) * u.natAbs + (M - 1) * v.natAbs :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_right _ (by omega))
    _ = (M - 1) * (u.natAbs + v.natAbs) := (Nat.mul_add _ _ _).symm
    _ ≤ (M - 1) * 2 ^ s := Nat.mul_le_mul_left _ huv
    _ < M * 2 ^ s := by omega

/-- The quotient that `lincomb_int_reduce_shift_mod` divides out is below `M`, so its final
conditional subtraction keeps it. -/
theorem red_lt {A XA s M W : Nat} (hA : A < M * 2 ^ s) (hX : XA < M * 2 ^ s) (hW : M ≤ 2 ^ W) :
    (if (if A < XA then XA - A else A - XA) / 2 ^ s / 2 ^ W % 2 ^ 32 = 0 ∧
        (if A < XA then XA - A else A - XA) / 2 ^ s % 2 ^ W < M then
      (if A < XA then XA - A else A - XA) / 2 ^ s % 2 ^ W
    else ((if A < XA then XA - A else A - XA) / 2 ^ s % 2 ^ W + 2 ^ W - M) % 2 ^ W) < M := by
  generalize hY : (if A < XA then XA - A else A - XA) = Y
  have hY' : Y < M * 2 ^ s := by
    rw [← hY]; split <;> omega
  have hZ : Y / 2 ^ s < M := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).2 hY'
  have hZW : Y / 2 ^ s < 2 ^ W := Nat.lt_of_lt_of_le hZ hW
  rw [Nat.div_eq_of_lt hZW, Nat.mod_eq_of_lt hZW, ite_eq_left ⟨Nat.zero_mod _, hZ⟩]
  exact hZ

theorem lrsm8_lt {σ A MI s M : Nat} (hM : 0 < M) (hW : M ≤ 2 ^ 256) (hA : A < M * 2 ^ s) :
    (lrsm8 σ A MI s M).2 < M :=
  red_lt hA (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ (Nat.two_pow_pos s)) hM) hW

set_option exponentiation.threshold 600 in
theorem lrsm_lt {σ A MI s M : Nat} (hM : 0 < M) (hW : M ≤ 2 ^ 384) (hA : A < M * 2 ^ s) :
    (lrsm σ A MI s M).2 < M :=
  red_lt hA (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ (Nat.two_pow_pos s)) hM) hW

theorem sgnVal_natAbs (σ A : Nat) : (sgnVal σ A).natAbs = A := by
  unfold sgnVal; split
  · rw [Int.natAbs_neg]; rfl
  · rfl

theorem normVal8_lt {σ fs X p : Nat} (hX : X < p) (hW : p ≤ 2 ^ 256) : normVal8 σ fs X p < p := by
  unfold normVal8
  split
  · rename_i h
    have h0 : X ≠ 0 := h.2
    rw [show p + 2 ^ 256 - X = (p - X) + 2 ^ 256 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact hX

set_option exponentiation.threshold 600 in
theorem normVal_lt {σ fs X p : Nat} (hX : X < p) (hW : p ≤ 2 ^ 384) : normVal σ fs X p < p := by
  unfold normVal
  split
  · rename_i h
    have h0 : X ≠ 0 := h.2
    rw [show p + 2 ^ 384 - X = (p - X) + 2 ^ 384 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact hX

/-- `d` and `e` are below the modulus `M`. -/
def DeB (M : Nat) (s : Iv) : Prop := s.d.natAbs < M ∧ s.e.natAbs < M

theorem deB_init {M δ R rem : Nat} {f g : Int} (hR : R < M) : DeB M ⟨δ, f, g, 0, (R : Int), rem⟩ :=
  ⟨by show (0 : Int).natAbs < M; omega, by show (R : Int).natAbs < M; rw [Int.natAbs_natCast]; exact hR⟩

end C3.RV32.Safegcd
