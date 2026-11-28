import C3BootProofs.Models.EcdsaField
import C3BootProofs.Proofs.Pv384CIt

/-!
# The safegcd inversions compute inverses

The compiled inversions run batches of at most 62 divsteps on the low words
of `f` and `g`, then apply the batch's matrix to `f`, `g`, `d`, and `e`.
`stepW` is one batch for `W`-bit values; `ivStep8`, `zvStep`, `ivStep`, and
`hvStep` are instances. Each batch keeps `IvOk`: `f` odd, the values in
range, and `f e₀ ≡ d x`, `g e₀ ≡ e x` modulo `M`, where `x` is the value
inverted and `e₀` the starting `e`. So when `f` ends as `±1`, the
normalized `d` times `x` is `e₀` (`normW_inv`). Nothing here bounds the
number of batches the loops need.
-/

namespace C3.Models

open C3.RV32 C3.RV32.Pv

/-- `lincomb_int_reduce_shift_mod` for `W`-bit magnitudes. -/
def lrsmW (W σ A MI s M : Nat) : Nat × Nat :=
  let XA := M * lrsmMf A MI s
  let Y := if A < XA then XA - A else A - XA
  let Z := Y / 2 ^ s
  let lo := Z % 2 ^ W
  (if A < XA then 1 - σ else σ,
    if Z / 2 ^ W % 2 ^ 32 = 0 ∧ lo < M then lo else (lo + 2 ^ W - M) % 2 ^ W)

/-- `update_fg` for `W`-bit values. -/
def fgW (W : Nat) (F G u v : Int) (s : Nat) : Int :=
  sgnI (F * u + G * v) ((F * u + G * v).natAbs / 2 ^ s % 2 ^ W)

/-- `update_de` for `W`-bit values. -/
def deW (W : Nat) (D E u v : Int) (MI s M : Nat) : Int :=
  let X := D * u + E * v
  let r := lrsmW W (if X < 0 then 1 else 0) X.natAbs MI s M
  sgnVal r.1 r.2

/-- One batch of an inversion modulo `M` on `W`-bit values. -/
def stepW (W MI M : Nat) (s : Iv) : Iv :=
  let n := min s.rem 62
  let t := dsIter n ⟨s.δ, lowestI s.f, lowestI s.g, 1, 0, 0, 1⟩
  ⟨t.δ, fgW W s.f s.g (i64Val t.u) (i64Val t.v) n, fgW W s.f s.g (i64Val t.q) (i64Val t.r) n,
    deW W s.d s.e (i64Val t.u) (i64Val t.v) MI n M, deW W s.d s.e (i64Val t.q) (i64Val t.r) MI n M, s.rem - n⟩

/-- `SignedInt::norm` for `W`-bit values. -/
def normW (W σ fs X p : Nat) : Nat := if σ ≠ fs ∧ X ≠ 0 then (p + 2 ^ W - X) % 2 ^ W else X

/-! ## Divsteps on 64-bit words -/

/-- After `k` divsteps from the words `F0` and `G0`, the batch's words
track a signed matrix `[[u, v], [q, r]]` whose rows sum to at most `2^k` in
magnitude, with `2^k f ≡ u F0 + v G0` and `2^k g ≡ q F0 + r G0` modulo
`2^64`, and `f` odd. -/
def DsInv (F0 G0 : Int) (k : Nat) (t : Ds) (u v q r : Int) : Prop :=
  t.f < 2 ^ 64 ∧ t.g < 2 ^ 64 ∧ t.u < 2 ^ 64 ∧ t.v < 2 ^ 64 ∧ t.q < 2 ^ 64 ∧ t.r < 2 ^ 64 ∧ t.f % 2 = 1 ∧
    (t.u : Int) % 2 ^ 64 = u % 2 ^ 64 ∧ (t.v : Int) % 2 ^ 64 = v % 2 ^ 64 ∧
    (t.q : Int) % 2 ^ 64 = q % 2 ^ 64 ∧ (t.r : Int) % 2 ^ 64 = r % 2 ^ 64 ∧
    u.natAbs + v.natAbs ≤ 2 ^ k ∧ q.natAbs + r.natAbs ≤ 2 ^ k ∧
    (2 ^ k * (t.f : Int)) % 2 ^ 64 = (u * F0 + v * G0) % 2 ^ 64 ∧
    (2 ^ k * (t.g : Int)) % 2 ^ 64 = (q * F0 + r * G0) % 2 ^ 64

theorem emul {a b m : Int} (c : Int) (h : a % m = b % m) : (c * a) % m = (c * b) % m := by
  rw [Int.mul_emod, h, ← Int.mul_emod]

theorem asr2 {x : Nat} (hx : x < 2 ^ 64) (he : x % 2 = 0) :
    (2 * (asr64 x : Int)) % 2 ^ 64 = (x : Int) % 2 ^ 64 ∧ asr64 x < 2 ^ 64 := by
  unfold asr64
  exact ⟨by split <;> omega, by split <;> omega⟩

theorem dsStep_inv {F0 G0 : Int} {k : Nat} {t : Ds} {u v q r : Int} (h : DsInv F0 G0 k t u v q r) :
    ∃ u' v' q' r', DsInv F0 G0 (k + 1) (dsStep t) u' v' q' r' := by
  obtain ⟨hf, hg, hu, hv, hq, hr, hfo, eu, ev, eq, er, b1, b2, cf, cg⟩ := h
  have p2 : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by rw [Int.pow_succ, Int.mul_comm]
  have p2n : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold dsStep
  by_cases he : t.g % 2 = 0
  · rw [ite_eq_left he]
    obtain ⟨a1, a2⟩ := asr2 hg he
    refine ⟨2 * u, 2 * v, q, r, ?_⟩
    dsimp only [DsInv]
    refine ⟨hf, a2, by omega, by omega, hq, hr, hfo, by omega, by omega, eq, er, by omega, by omega, ?_, ?_⟩
    · rw [p2, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]; omega
    · rw [p2, Int.mul_comm 2, Int.mul_assoc, emul _ a1]; exact cg
  · rw [ite_eq_right he]
    by_cases hd : dsPos t.δ
    · rw [ite_eq_left hd]
      have hx : (t.g + 2 ^ 64 - t.f) % 2 ^ 64 % 2 = 0 := by omega
      obtain ⟨a1, a2⟩ := asr2 (Nat.mod_lt _ (by decide)) hx
      refine ⟨2 * q, 2 * r, q - u, r - v, ?_⟩
      dsimp only [DsInv]
      refine ⟨hg, a2, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, ?_, ?_⟩
      · rw [p2, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]; omega
      · rw [p2, Int.mul_comm 2, Int.mul_assoc, emul _ a1]
        have e2 : ((((t.g + 2 ^ 64 - t.f) % 2 ^ 64 : Nat) : Int)) % 2 ^ 64 = ((t.g : Int) - t.f) % 2 ^ 64 := by
          omega
        rw [emul _ e2, Int.mul_sub, Int.sub_mul, Int.sub_mul]
        omega
    · rw [ite_eq_right hd]
      have hx : (t.g + t.f) % 2 ^ 64 % 2 = 0 := by omega
      obtain ⟨a1, a2⟩ := asr2 (Nat.mod_lt _ (by decide)) hx
      refine ⟨2 * u, 2 * v, q + u, r + v, ?_⟩
      dsimp only [DsInv]
      refine ⟨hf, a2, by omega, by omega, by omega, by omega, hfo, by omega, by omega, by omega, by omega,
        by omega, by omega, ?_, ?_⟩
      · rw [p2, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]; omega
      · rw [p2, Int.mul_comm 2, Int.mul_assoc, emul _ a1]
        have e2 : ((((t.g + t.f) % 2 ^ 64 : Nat) : Int)) % 2 ^ 64 = ((t.g : Int) + t.f) % 2 ^ 64 := by omega
        rw [emul _ e2, Int.mul_add, Int.add_mul, Int.add_mul]
        omega

theorem dsIter_inv {F0 G0 : Int} : ∀ n k (t : Ds) (u v q r : Int), DsInv F0 G0 k t u v q r →
    ∃ u' v' q' r', DsInv F0 G0 (k + n) (dsIter n t) u' v' q' r'
  | 0, k, t, u, v, q, r, h => ⟨u, v, q, r, h⟩
  | n + 1, k, t, u, v, q, r, h => by
    obtain ⟨u', v', q', r', h'⟩ := dsStep_inv h
    obtain ⟨u'', v'', q'', r'', h''⟩ := dsIter_inv n (k + 1) _ _ _ _ _ h'
    exact ⟨u'', v'', q'', r'', by rw [show k + (n + 1) = k + 1 + n by omega]; exact h''⟩

theorem lowestI_lt (X : Int) : lowestI X < 2 ^ 64 := by
  unfold lowestI lowestVal; split <;> split <;> omega

theorem lowestI_mod (X : Int) : (lowestI X : Int) % 2 ^ 63 = X % 2 ^ 63 := by
  unfold lowestI lowestVal; split <;> split <;> omega

theorem i64Val_eq {c : Nat} {u : Int} (hc : c < 2 ^ 64) (h : (c : Int) % 2 ^ 64 = u % 2 ^ 64)
    (hu : u.natAbs < 2 ^ 63) : i64Val c = u := by
  unfold i64Val; split <;> omega

theorem dsInv_init (δ : Nat) (f g : Int) (hf : f % 2 = 1) :
    DsInv (lowestI f) (lowestI g) 0 ⟨δ, lowestI f, lowestI g, 1, 0, 0, 1⟩ 1 0 0 1 := by
  dsimp only [DsInv]
  have := lowestI_mod f
  exact ⟨lowestI_lt f, lowestI_lt g, by decide, by decide, by decide, by decide, by omega,
    rfl, rfl, rfl, rfl, by decide, by decide, by omega, by omega⟩

/-! ## The updates of `f`, `g`, `d`, and `e` -/

theorem ipow (n : Nat) : (2 : Int) ^ n = ((2 ^ n : Nat) : Int) := (Int.natCast_pow 2 n).symm

theorem ipow_dvd {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ∣ (2 : Int) ^ b :=
  ⟨2 ^ (b - a), by rw [← Int.pow_add]; congr 1; omega⟩

theorem natAbs_lc_le {B : Nat} {f g u v : Int} (hf : f.natAbs ≤ B) (hg : g.natAbs ≤ B) :
    (f * u + g * v).natAbs ≤ B * (u.natAbs + v.natAbs) := by
  have h1 := Int.natAbs_add_le (f * u) (g * v)
  rw [Int.natAbs_mul, Int.natAbs_mul] at h1
  have h2 := Nat.mul_le_mul_right u.natAbs hf
  have h3 := Nat.mul_le_mul_right v.natAbs hg
  rw [Nat.mul_add]; omega

theorem fgW_spec {W n : Nat} {f g u v : Int} (hf : f.natAbs < 2 ^ W) (hg : g.natAbs < 2 ^ W)
    (huv : u.natAbs + v.natAbs ≤ 2 ^ n) (hd : (f * u + g * v) % 2 ^ n = 0) :
    (2 : Int) ^ n * fgW W f g u v n = f * u + g * v ∧ (fgW W f g u v n).natAbs < 2 ^ W := by
  unfold fgW
  generalize hX : f * u + g * v = X at *
  have hA : X.natAbs ≤ (2 ^ W - 1) * 2 ^ n := by
    rw [← hX]
    exact Nat.le_trans (natAbs_lc_le (by omega) (by omega)) (Nat.mul_le_mul_left _ huv)
  have hdv : 2 ^ n ∣ X.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr (Int.dvd_of_emod_eq_zero hd)
    rwa [Int.natAbs_pow] at this
  have hq : X.natAbs / 2 ^ n ≤ 2 ^ W - 1 := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hA)
  have hW : 0 < 2 ^ W := Nat.two_pow_pos W
  rw [Nat.mod_eq_of_lt (by omega)]
  have hm : (X.natAbs : Int) = (2 : Int) ^ n * ((X.natAbs / 2 ^ n : Nat) : Int) := by
    rw [ipow, ← Int.natCast_mul, Nat.mul_div_cancel' hdv]
  have hq' : X.natAbs / 2 ^ n < 2 ^ W := by omega
  unfold sgnI
  split
  · refine ⟨?_, by rw [Int.natAbs_neg, Int.natAbs_natCast]; exact hq'⟩
    rw [Int.mul_neg, ← hm]; omega
  · refine ⟨?_, by rw [Int.natAbs_natCast]; exact hq'⟩
    rw [← hm]; omega

/-- `lrsmMf` makes the subtraction exact: `M mf ≡ A` modulo `2^s`. -/
theorem lrsmMf_cong {A MI M s : Nat} (hs : s ≤ 64) (hMI : M * MI % 2 ^ 64 = 1) :
    M * lrsmMf A MI s % 2 ^ s = A % 2 ^ s := by
  unfold lrsmMf
  have hd : 2 ^ s ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hs
  rw [Nat.mod_mod_of_dvd _ hd, Nat.mul_mod_mod, ← Nat.mod_mod_of_dvd (M * _) hd, ← Nat.mod_mod_of_dvd A hd]
  congr 1
  rw [Nat.mul_left_comm, Nat.mul_mod, hMI, Nat.mul_one, Nat.mod_mod, Nat.mod_mod]

theorem deW_spec {W M MI n : Nat} {D E u v : Int} (hn : n ≤ 62) (hMI : M * MI % 2 ^ 64 = 1)
    (hMW : M ≤ 2 ^ W) (hD : D.natAbs < M) (hE : E.natAbs < M) (huv : u.natAbs + v.natAbs ≤ 2 ^ n) :
    MEq M ((2 : Int) ^ n * deW W D E u v MI n M) (D * u + E * v) ∧ (deW W D E u v MI n M).natAbs < M := by
  unfold deW lrsmW
  dsimp only
  generalize hX : D * u + E * v = X
  generalize hmf : lrsmMf X.natAbs MI n = mf
  have hc := lrsmMf_cong (A := X.natAbs) (by omega : n ≤ 64) hMI
  rw [hmf] at hc
  have hmf2 : mf < 2 ^ n := by rw [← hmf]; unfold lrsmMf; exact Nat.mod_lt _ (Nat.two_pow_pos n)
  have hA : X.natAbs ≤ (M - 1) * 2 ^ n := by
    rw [← hX]
    exact Nat.le_trans (natAbs_lc_le (by omega) (by omega)) (Nat.mul_le_mul_left _ huv)
  have hM : 0 < M := by omega
  have hP : 0 < 2 ^ n := Nat.two_pow_pos n
  have hXA : M * mf ≤ M * (2 ^ n - 1) := Nat.mul_le_mul_left _ (by omega)
  have hMn : M * (2 ^ n - 1) + M = M * 2 ^ n := by
    rw [← Nat.mul_succ]; congr 1; omega
  have hMn' : (M - 1) * 2 ^ n + 2 ^ n = M * 2 ^ n := by
    rw [← Nat.succ_mul]; congr 1; omega
  generalize hY : (if X.natAbs < M * mf then M * mf - X.natAbs else X.natAbs - M * mf) = Y
  have hYlt : Y < M * 2 ^ n := by rw [← hY]; split <;> omega
  have hYd : Y % 2 ^ n = 0 := by
    rw [← hY]
    split
    · exact Nat.sub_mod_eq_zero_of_mod_eq hc
    · exact Nat.sub_mod_eq_zero_of_mod_eq hc.symm
  have hZ : Y / 2 ^ n < M := (Nat.div_lt_iff_lt_mul hP).mpr hYlt
  have hZW : Y / 2 ^ n < 2 ^ W := by omega
  rw [Nat.mod_eq_of_lt hZW, Nat.div_eq_of_lt hZW]
  simp only [Nat.zero_mod, true_and, ite_eq_left hZ]
  have hYm : (Y : Int) = (2 : Int) ^ n * ((Y / 2 ^ n : Nat) : Int) := by
    rw [ipow, ← Int.natCast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hYd)]
  generalize Y / 2 ^ n = Z at hYm hZ
  have hmfI : ((M * mf : Nat) : Int) = (M : Int) * (mf : Int) := Int.natCast_mul _ _
  refine ⟨?_, ?_⟩
  · unfold sgnVal
    by_cases hlt : X.natAbs < M * mf
    · have hY' : (Y : Int) = (M : Int) * mf - X.natAbs := by rw [← hY, ite_eq_left hlt]; omega
      by_cases hX0 : X < 0
      · rw [ite_eq_left hlt, ite_eq_left hX0]; simp only [show (1 : Nat) - 1 = 0 from rfl, show ¬ (0 : Nat) = 1 by decide,
          ite_false]
        rw [← hYm, hY', show (M : Int) * mf - X.natAbs = X + (M : Int) * mf by omega]
        exact MEq.add_mul_self _
      · rw [ite_eq_left hlt, ite_eq_right hX0, ite_eq_left (show (1 : Nat) - 0 = 1 from rfl), Int.mul_neg, ← hYm, hY',
          show -((M : Int) * mf - X.natAbs) = X + (M : Int) * (-(mf : Int)) by rw [Int.mul_neg]; omega]
        exact MEq.add_mul_self _
    · have hY' : (Y : Int) = X.natAbs - (M : Int) * mf := by rw [← hY, ite_eq_right hlt]; omega
      by_cases hX0 : X < 0
      · rw [ite_eq_right hlt, ite_eq_left hX0, ite_eq_left rfl, Int.mul_neg, ← hYm, hY',
          show -((X.natAbs : Int) - (M : Int) * mf) = X + (M : Int) * mf by omega]
        exact MEq.add_mul_self _
      · rw [ite_eq_right hlt, ite_eq_right hX0, ite_eq_right (by decide), ← hYm, hY',
          show (X.natAbs : Int) - (M : Int) * mf = X + (M : Int) * (-(mf : Int)) by rw [Int.mul_neg]; omega]
        exact MEq.add_mul_self _
  · unfold sgnVal; split <;> omega

/-! ## The batch invariant -/

/-- The state of an inversion of `x` modulo `M` on `W`-bit values that
started with `e = e₀`. -/
structure IvOk (W M : Nat) (x e0 : Int) (s : Iv) : Prop where
  fodd : s.f % 2 = 1
  fb : s.f.natAbs < 2 ^ W
  gb : s.g.natAbs < 2 ^ W
  db : s.d.natAbs < M
  eb : s.e.natAbs < M
  cf : MEq M (s.f * e0) (s.d * x)
  cg : MEq M (s.g * e0) (s.e * x)

theorem coprime_two_pow {M : Nat} (hM : M % 2 = 1) (n : Nat) : Nat.Coprime (2 ^ n) M := by
  apply Nat.Coprime.pow_left
  show Nat.gcd 2 M = 1
  have h := Nat.gcd_dvd_left 2 M
  have h2 := Nat.gcd_dvd_right 2 M
  have hle : Nat.gcd 2 M ≤ 2 := Nat.le_of_dvd (by decide) h
  rcases (show Nat.gcd 2 M = 0 ∨ Nat.gcd 2 M = 1 ∨ Nat.gcd 2 M = 2 by omega) with h0 | h0 | h0
  · rw [h0] at h; exact absurd (Nat.eq_zero_of_zero_dvd h) (by decide)
  · exact h0
  · rw [h0] at h2; omega

theorem meq_cancel_coprime {M k : Nat} {a b : Int} (hc : Nat.Coprime k M) (h : MEq M ((k : Int) * a) ((k : Int) * b)) :
    MEq M a b := by
  rw [MEq.iff_sub, MEq.zero_iff] at h ⊢
  rw [← Int.mul_sub] at h
  have h1 := Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h1
  exact Int.natAbs_dvd_natAbs.mp (by rw [Int.natAbs_natCast]; exact hc.symm.dvd_of_dvd_mul_left h1)

theorem lc_meq {M : Nat} {f g d e x e0 u v : Int} (cf : MEq M (f * e0) (d * x)) (cg : MEq M (g * e0) (e * x)) :
    MEq M ((f * u + g * v) * e0) ((d * u + e * v) * x) := by
  have h : MEq M ((f * e0) * u + (g * e0) * v) ((d * x) * u + (e * x) * v) :=
    (cf.mul (MEq.refl u)).add (cg.mul (MEq.refl v))
  have e1 : (f * u + g * v) * e0 = (f * e0) * u + (g * e0) * v := by
    rw [Int.add_mul, Int.mul_assoc, Int.mul_comm u, ← Int.mul_assoc, Int.mul_assoc g, Int.mul_comm v,
      ← Int.mul_assoc]
  have e2 : (d * u + e * v) * x = (d * x) * u + (e * x) * v := by
    rw [Int.add_mul, Int.mul_assoc, Int.mul_comm u, ← Int.mul_assoc, Int.mul_assoc e, Int.mul_comm v,
      ← Int.mul_assoc]
  rw [e1, e2]; exact h

theorem stepW_ok {W M MI : Nat} {x e0 : Int} (hM : M % 2 = 1) (hMW : M ≤ 2 ^ W) (hMI : M * MI % 2 ^ 64 = 1)
    {s : Iv} (h : IvOk W M x e0 s) : IvOk W M x e0 (stepW W MI M s) := by
  unfold stepW
  dsimp only
  generalize hn : min s.rem 62 = n
  have hn62 : n ≤ 62 := by omega
  obtain ⟨u, v, q, r, hI⟩ := dsIter_inv n 0 _ 1 0 0 1 (dsInv_init s.δ s.f s.g h.fodd)
  rw [Nat.zero_add] at hI
  generalize dsIter n ⟨s.δ, lowestI s.f, lowestI s.g, 1, 0, 0, 1⟩ = t at hI ⊢
  obtain ⟨hf, hg, hu, hv, hq, hr, hfo, eu, ev, eq, er, b1, b2, cf, cg⟩ := hI
  have h62 : 2 ^ n ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) hn62
  rw [i64Val_eq hu eu (by omega), i64Val_eq hv ev (by omega), i64Val_eq hq eq (by omega),
    i64Val_eq hr er (by omega)]
  have hd63 : (2 : Int) ^ n ∣ 2 ^ 63 := ipow_dvd (by omega)
  have hF := lowestI_mod s.f
  have hG := lowestI_mod s.g
  have red : ∀ {a b : Int}, a % 2 ^ 64 = b % 2 ^ 64 → a % 2 ^ 63 = b % 2 ^ 63 := fun h => by omega
  have mod63 : ∀ (a b : Int), (2 ^ n * (a : Int)) % 2 ^ 64 = (b * (lowestI s.f : Int) + (a - a) + 0) % 2 ^ 64 → True :=
    fun _ _ _ => trivial
  clear mod63
  have key : ∀ (w a b : Int), (2 ^ n * w) % 2 ^ 64 = (a * (lowestI s.f : Int) + b * (lowestI s.g : Int)) % 2 ^ 64 →
      (s.f * a + s.g * b) % 2 ^ 63 = (2 ^ n * w) % 2 ^ 63 := by
    intro w a b hw
    rw [red hw, Int.add_emod (a * (lowestI s.f : Int)), emul a hF, emul b hG, ← Int.add_emod, Int.mul_comm a,
      Int.mul_comm b]
  have div : ∀ (w a b : Int), (s.f * a + s.g * b) % 2 ^ 63 = (2 ^ n * w) % 2 ^ 63 →
      (s.f * a + s.g * b) % 2 ^ n = 0 := by
    intro w a b hw
    rw [← Int.emod_emod_of_dvd _ hd63, hw, Int.emod_emod_of_dvd _ hd63, Int.mul_emod_right]
  have kf := key _ _ _ cf
  have kg := key _ _ _ cg
  obtain ⟨ff, fb⟩ := fgW_spec (W := W) h.fb h.gb b1 (div _ _ _ kf)
  obtain ⟨gg, gb⟩ := fgW_spec (W := W) h.fb h.gb b2 (div _ _ _ kg)
  obtain ⟨dd, db⟩ := deW_spec (W := W) hn62 hMI hMW h.db h.eb b1
  obtain ⟨ee, eb⟩ := deW_spec (W := W) hn62 hMI hMW h.db h.eb b2
  have hc := coprime_two_pow hM n
  have hcI : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := Int.natCast_pow _ _
  refine ⟨?_, fb, gb, db, eb, ?_, ?_⟩
  · show fgW W s.f s.g u v n % 2 = 1
    have h2 : (2 : Int) * 2 ^ n ∣ 2 ^ 63 := by
      rw [← Int.pow_succ']; exact ipow_dvd (by omega)
    have h3 : ((2 : Int) * 2 ^ n) ∣ 2 ^ n * (fgW W s.f s.g u v n - t.f) := by
      refine Int.dvd_trans h2 (Int.dvd_of_emod_eq_zero ?_)
      rw [Int.mul_sub, ff]; omega
    rw [Int.mul_comm 2] at h3
    have h4 := Int.dvd_of_mul_dvd_mul_left (by exact Int.ne_of_gt (Int.pow_pos (by decide))) h3
    omega
  · apply meq_cancel_coprime hc
    rw [hcI, ← Int.mul_assoc, ff, ← Int.mul_assoc]
    exact (lc_meq h.cf h.cg).trans (dd.symm.mul (MEq.refl x))
  · apply meq_cancel_coprime hc
    rw [hcI, ← Int.mul_assoc, gg, ← Int.mul_assoc]
    exact (lc_meq h.cf h.cg).trans (ee.symm.mul (MEq.refl x))

/-- The starting state of an inversion of `x` modulo `M`. -/
theorem ivOk_init {W M : Nat} {x : Nat} {e0 : Nat} (δ rem : Nat) (hM : M % 2 = 1) (hMW : M < 2 ^ W)
    (hx : x < 2 ^ W) (he : e0 < M) :
    IvOk W M x e0 ⟨δ, (M : Int), (x : Int), 0, (e0 : Int), rem⟩ := by
  refine ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega,
    by simp only; omega, ?_, ?_⟩
  · show MEq M ((M : Int) * e0) (0 * x)
    rw [Int.zero_mul]; exact MEq.zero_iff.mpr (Int.dvd_mul_right _ _)
  · show MEq M ((x : Int) * e0) ((e0 : Int) * x)
    rw [Int.mul_comm]; exact MEq.refl _

theorem normW_val {W M : Nat} {f d : Int} (hMW : M ≤ 2 ^ W) (hd : d.natAbs < M) (hf : f = 1 ∨ f = -1) :
    MEq M ((normW W (if d < 0 then 1 else 0) (if f < 0 then 1 else 0) d.natAbs M : Nat) : Int) (f * d) ∧
      normW W (if d < 0 then 1 else 0) (if f < 0 then 1 else 0) d.natAbs M < M := by
  by_cases h0 : d = 0
  · subst h0
    unfold normW
    rw [ite_eq_right (fun h => h.2 rfl), Int.mul_zero]
    exact ⟨MEq.refl _, by omega⟩
  have hmod : (M + 2 ^ W - d.natAbs) % 2 ^ W = M - d.natAbs := by
    rw [show M + 2 ^ W - d.natAbs = (M - d.natAbs) + 2 ^ W by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hX : d.natAbs ≠ 0 := by omega
  unfold normW
  rcases hf with rfl | rfl
  · rw [ite_eq_right (by decide : ¬ (1 : Int) < 0)]
    by_cases hn : d < 0
    · rw [ite_eq_left hn, ite_eq_left ⟨Nat.one_ne_zero, hX⟩, hmod,
        show (((M - d.natAbs : Nat)) : Int) = 1 * d + (M : Int) * 1 by omega]
      exact ⟨MEq.add_mul_self _, by omega⟩
    · rw [ite_eq_right hn, ite_eq_right (fun h => h.1 rfl)]
      exact ⟨MEq.of_eq (by omega), by omega⟩
  · rw [ite_eq_left (by decide : (-1 : Int) < 0)]
    by_cases hn : d < 0
    · rw [ite_eq_left hn, ite_eq_right (fun h => h.1 rfl)]
      exact ⟨MEq.of_eq (by omega), by omega⟩
    · rw [ite_eq_right hn, ite_eq_left ⟨Nat.zero_ne_one, hX⟩, hmod,
        show (((M - d.natAbs : Nat)) : Int) = -1 * d + (M : Int) * 1 by omega]
      exact ⟨MEq.add_mul_self _, by omega⟩

/-- When `f` ends as `±1`, the normalized `d` is the inverse of `x` times
`e₀`. -/
theorem normW_inv {W M : Nat} {x e0 : Int} {s : Iv} (hMW : M ≤ 2 ^ W) (h : IvOk W M x e0 s)
    (hf : s.f.natAbs = 1) :
    MEq M ((normW W (if s.d < 0 then 1 else 0) (if s.f < 0 then 1 else 0) s.d.natAbs M : Nat) * x) e0 ∧
      normW W (if s.d < 0 then 1 else 0) (if s.f < 0 then 1 else 0) s.d.natAbs M < M := by
  have hf' : s.f = 1 ∨ s.f = -1 := by omega
  obtain ⟨hw, hlt⟩ := normW_val hMW h.db hf'
  refine ⟨?_, hlt⟩
  have h1 : MEq M (s.f * (s.f * e0)) (s.f * (s.d * x)) := (MEq.refl s.f).mul h.cf
  have hff : s.f * s.f = 1 := by rcases hf' with h1 | h1 <;> rw [h1] <;> decide
  rw [← Int.mul_assoc, hff, Int.one_mul, ← Int.mul_assoc] at h1
  exact (hw.mul (MEq.refl x)).trans h1.symm

end C3.Models
