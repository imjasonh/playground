import C3BootProofs.Models.Ed25519Field
import C3BootProofs.Models.Ed25519Naf
import C3BootProofs.Proofs.Ed25519VerifyP7

/-!
# The double-base NAF loop computes `[k](-A) + [s]B`

Limb points represent affine points through `fv`: `PRep` for projective
`(X : Y : Z)`, `ERep` for extended `(X : Y : Z : T)`, `CRep` for completed
`((X : Z), (Y : T))`, and `NRep` for projective Niels `(Y + X, Y - X, Z, 2dT)`.
`EdFormulas` states what each limb formula the loop uses computes, as one
`Prop` per formula. From those and `EdGroupLaws`, `ladder_final` shows the
loop's result represents `[k](-A) + [s]B` for the NAF digits of `k` and `s`.
-/

namespace C3.RV32.EdM

/-- Three limb lists: a projective point. -/
abbrev Pr := List Nat × List Nat × List Nat

/-- `(X : Y : Z)` with limbs below 2^26 represents `P`: `X = x Z`, `Y = y Z`,
and `Z ≠ 0`. -/
def PRep (r : Pr) (P : Nat × Nat) : Prop :=
  Lim (2 ^ 26) r.1 ∧ Lim (2 ^ 26) r.2.1 ∧ Lim (2 ^ 26) r.2.2 ∧ fv r.2.2 ≠ 0 ∧
    fv r.1 = P.1 * fv r.2.2 % Ed25519.p ∧ fv r.2.1 = P.2 * fv r.2.2 % Ed25519.p

/-- `(X : Y : Z : T)` with limbs below 2^26 represents `P`: `X = x Z`,
`Y = y Z`, `X Y = Z T`, and `Z ≠ 0`. -/
def ERep (E : Pt) (P : Nat × Nat) : Prop :=
  Lim (2 ^ 26) E.1 ∧ Lim (2 ^ 26) E.2.1 ∧ Lim (2 ^ 26) E.2.2.1 ∧ Lim (2 ^ 26) E.2.2.2 ∧ fv E.2.2.1 ≠ 0 ∧
    fv E.1 = P.1 * fv E.2.2.1 % Ed25519.p ∧ fv E.2.1 = P.2 * fv E.2.2.1 % Ed25519.p ∧
    fv E.1 * fv E.2.1 % Ed25519.p = fv E.2.2.1 * fv E.2.2.2 % Ed25519.p

/-- The completed point `(X, Y, Z, T)` with limbs below 3 · 2^26 represents
`P`: `X = x Z`, `Y = y T`, and `Z, T ≠ 0`. -/
def CRep (C : Pt) (P : Nat × Nat) : Prop :=
  Lim (3 * 2 ^ 26) C.1 ∧ Lim (3 * 2 ^ 26) C.2.1 ∧ Lim (3 * 2 ^ 26) C.2.2.1 ∧ Lim (3 * 2 ^ 26) C.2.2.2 ∧
    fv C.2.2.1 ≠ 0 ∧ fv C.2.2.2 ≠ 0 ∧ fv C.1 = P.1 * fv C.2.2.1 % Ed25519.p ∧
    fv C.2.1 = P.2 * fv C.2.2.2 % Ed25519.p

/-- The projective Niels point `(Y + X, Y - X, Z, 2dT)` with limbs below
3 · 2^26 represents `P`: its coordinates are `(y + x) Z`, `(y - x) Z`, `Z`,
and `2 d x y Z`, with `Z ≠ 0`. -/
def NRep (N : Pt) (P : Nat × Nat) : Prop :=
  Lim (3 * 2 ^ 26) N.1 ∧ Lim (3 * 2 ^ 26) N.2.1 ∧ Lim (3 * 2 ^ 26) N.2.2.1 ∧ Lim (3 * 2 ^ 26) N.2.2.2 ∧
    fv N.2.2.1 ≠ 0 ∧ fv N.1 = (P.2 + P.1) * fv N.2.2.1 % Ed25519.p ∧
    fv N.2.1 = (P.2 + Ed25519.p - P.1) * fv N.2.2.1 % Ed25519.p ∧
    fv N.2.2.2 = 2 * Ed25519.d * P.1 % Ed25519.p * P.2 % Ed25519.p * fv N.2.2.1 % Ed25519.p

/-- `ProjectivePoint::double`: `(X + Y)² - (Y² + X²) = 2XY`, `Y² + X²`,
`Y² - X²`, and `2Z² - (Y² - X²)` are a completed point for `P + P`, that is
`2xy / (y² - x²) = x(2P)` and `(y² + x²) / (2 - y² + x²) = y(2P)`. -/
def EdDblOK : Prop :=
  ∀ (r : Pr) (P : Nat × Nat), OnCurve P → PRep r P → CRep (edDoubleSpec r.1 r.2.1 r.2.2) (Ed25519.add P P)

/-- `CompletedPoint::as_extended`: `(X T, Y Z, Z T, X Y)` for the completed
point `(X, Y, Z, T)`. -/
def EdExtOK : Prop := ∀ (C : Pt) (P : Nat × Nat), OnCurve P → CRep C P → ERep (extL C) P

/-- `CompletedPoint::as_projective`: `(X T, Y Z, Z T)`. -/
def EdProjOK : Prop := ∀ (C : Pt) (P : Nat × Nat), OnCurve P → CRep C P → PRep (projC C) P

/-- `EdwardsPoint + ProjectiveNielsPoint`: with `PP = (Y₁ + X₁)(Y₂ + X₂)`,
`MM = (Y₁ - X₁)(Y₂ - X₂)`, `TT = T₁ · 2dT₂`, and `ZZ = Z₁ Z₂`, the completed
point `(PP - MM, PP + MM, 2ZZ + TT, 2ZZ - TT)` is `P + Q`. -/
def EdAddNOK : Prop :=
  ∀ (E N : Pt) (P Q : Nat × Nat), OnCurve P → OnCurve Q → ERep E P → NRep N Q →
    CRep (addNL E N) (Ed25519.add P Q)

/-- `EdwardsPoint - ProjectiveNielsPoint`: with `PP = (Y₁ + X₁)(Y₂ - X₂)`,
`MM = (Y₁ - X₁)(Y₂ + X₂)`, `TT = T₁ · 2dT₂`, and `ZZ = Z₁ Z₂`, the completed
point `(PP - MM, PP + MM, 2ZZ - TT, 2ZZ + TT)` is `P - Q`. -/
def EdSubNOK : Prop :=
  ∀ (E N : Pt) (P Q : Nat × Nat), OnCurve P → OnCurve Q → ERep E P → NRep N Q →
    CRep (subNL E N) (Ed25519.add P (neg Q))

/-- `EdwardsPoint::as_projective_niels`: `(Y + X, Y - X, Z, T · 2d)`, given
limbs `d2` that hold `2d`. -/
def EdNielsOK : Prop :=
  ∀ (d2 : List Nat) (E : Pt) (P : Nat × Nat), Lim (2 ^ 26) d2 → fv d2 = 2 * Ed25519.d % Ed25519.p → OnCurve P →
    ERep E P → NRep (nielsL E d2) P

/-- `FieldElement2625::neg`: the limbs of `-x`, below 2^26. -/
def FeNegOK : Prop :=
  ∀ l : List Nat, Lim (2 ^ 26) l → Lim (2 ^ 26) (negL l) ∧ fv (negL l) = (Ed25519.p - fv l) % Ed25519.p

/-- What each limb formula of the loop computes. -/
structure EdFormulas : Prop where
  dbl : EdDblOK
  ext : EdExtOK
  proj : EdProjOK
  addN : EdAddNOK
  subN : EdSubNOK
  niels : EdNielsOK

theorem prep_of_erep {E : Pt} {P : Nat × Nat} (h : ERep E P) : PRep (E.1, E.2.1, E.2.2.1) P :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- Negating `X` and `T` represents the negated point. -/
theorem erep_neg (hn : FeNegOK) {X Y Z T : List Nat} {P : Nat × Nat} (hP : OnCurve P) (h : ERep (X, Y, Z, T) P) :
    ERep (negL X, Y, Z, negL T) (neg P) := by
  obtain ⟨hX, hY, hZ, hT, hz, ex, ey, et⟩ := h
  obtain ⟨hX', eX⟩ := hn X hX
  obtain ⟨hT', eT⟩ := hn T hT
  refine ⟨hX', hY, hZ, hT', hz, ?_, ey, ?_⟩
  · show fv (negL X) = (Ed25519.p - P.1) % Ed25519.p * fv Z % Ed25519.p
    rw [eX, ex, ← Nat.mod_eq_of_lt hP.1, neg_mul_mod, Nat.mod_eq_of_lt hP.1]
  · show fv (negL X) * fv Y % Ed25519.p = fv Z * fv (negL T) % Ed25519.p
    rw [eX, eT, ← Nat.mod_eq_of_lt (fv_lt X), neg_mul_mod, Nat.mul_comm (fv Z), ← Nat.mod_eq_of_lt (fv_lt T),
      neg_mul_mod, Nat.mul_comm (fv T), ← et]

section
variable (G : EdGroupLaws) (F : EdFormulas)
include G F

/-- Entry `j` of the table of `A` represents `(2j + 1) Q`. -/
theorem tab_rep (d2 : List Nat) (hd2 : Lim (2 ^ 26) d2) (hd2v : fv d2 = 2 * Ed25519.d % Ed25519.p) (A : Pt)
    (Q : Nat × Nat) (hQ : OnCurve Q) (hA : ERep A Q) : ∀ j, NRep (nafTab A d2 j) (nsmul (2 * j + 1) Q)
  | 0 => by
    rw [show 2 * 0 + 1 = 1 from rfl, nsmul_one Q hQ]
    exact F.niels d2 A Q hd2 hd2v hQ hA
  | j + 1 => by
    have h2 := G.closed Q Q hQ hQ
    have he := F.ext _ _ h2 (F.dbl (A.1, A.2.1, A.2.2.1) Q hQ (prep_of_erep hA))
    have hj := nsmul_on G Q hQ (2 * j + 1)
    have ha := F.addN _ _ _ _ h2 hj he (tab_rep d2 hd2 hd2v A Q hQ hA j)
    have hs : Ed25519.add (Ed25519.add Q Q) (nsmul (2 * j + 1) Q) = nsmul (2 * (j + 1) + 1) Q := by
      rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by omega, nsmul_add G Q hQ 2 (2 * j + 1),
        show nsmul 2 Q = Ed25519.add Q Q by rw [nsmul_succ, nsmul_one Q hQ]]
    rw [hs] at ha
    have hon := nsmul_on G Q hQ (2 * (j + 1) + 1)
    exact F.niels d2 _ _ hd2 hd2v hon (F.ext _ _ hon ha)

/-- One digit's step adds `sval b` times `Q`. -/
theorem dig_rep (T : Nat → Pt) (Q : Nat × Nat) (hQ : OnCurve Q) (hT : ∀ j, NRep (T j) (nsmul (2 * j + 1) Q))
    (b : BitVec 8) (hb : b = 0 ∨ b.toNat % 2 = 1) (hr : b.toNat ≤ 15 ∨ 241 ≤ b.toNat) (t : Pt) (X : Nat × Nat)
    (hX : OnCurve X) (ht : CRep t X) : CRep (digStep T b t) (Ed25519.add X (zs (sval b) Q)) := by
  unfold digStep
  by_cases h0 : b.toNat = 0
  · have e : b = 0 := BitVec.eq_of_toNat_eq h0
    subst e
    rw [ite_eq_left h0, sval_zero, show zs (0 : Int) Q = Ed25519.zero from rfl, add_zero' X hX]
    exact ht
  · have hodd : b.toNat % 2 = 1 := hb.resolve_left fun e => h0 (by rw [e]; rfl)
    rw [ite_eq_right h0]
    by_cases h15 : b.toNat ≤ 15
    · rw [ite_eq_left h15]
      have e : 2 * (b.toNat / 2) + 1 = b.toNat := by omega
      have hs : sval b = ((b.toNat : Nat) : Int) := by unfold sval; rw [ite_eq_left (by omega)]
      rw [hs, zs_ofNat]
      have := F.addN _ _ _ _ hX (nsmul_on G Q hQ _) (F.ext _ _ hX ht) (hT (b.toNat / 2))
      rwa [e] at this
    · rw [ite_eq_right h15]
      have h241 : 241 ≤ b.toNat := hr.resolve_left h15
      have hlt : b.toNat < 256 := b.isLt
      have e : 2 * ((256 - b.toNat) / 2) + 1 = 256 - b.toNat := by omega
      have hs : sval b = -((256 - b.toNat : Nat) : Int) := by unfold sval; rw [ite_eq_right (by omega)]; omega
      rw [hs, zs_negPt]
      have := F.subN _ _ _ _ hX (nsmul_on G Q hQ _) (F.ext _ _ hX ht) (hT ((256 - b.toNat) / 2))
      rwa [e] at this

omit F in
theorem add_right_swap (a b c : Nat × Nat) (ha : OnCurve a) (hb : OnCurve b) (hc : OnCurve c) :
    Ed25519.add (Ed25519.add a b) c = Ed25519.add (Ed25519.add a c) b := by
  rw [G.assoc _ _ _ ha hb hc, add_comm' b c, ← G.assoc _ _ _ ha hc hb]

omit F in
theorem add_add_add (a b c d : Nat × Nat) (ha : OnCurve a) (hb : OnCurve b) (hc : OnCurve c) (hd : OnCurve d) :
    Ed25519.add (Ed25519.add a b) (Ed25519.add c d) = Ed25519.add (Ed25519.add a c) (Ed25519.add b d) := by
  rw [← G.assoc _ _ _ (G.closed _ _ ha hb) hc hd, add_right_swap G _ _ _ ha hb hc,
    G.assoc _ _ _ (G.closed _ _ ha hc) hb hd]

/-- One pass of the loop: `r ↦ 2r + a QA + b QB`. -/
theorem step_rep (TA TB : Nat → Pt) (QA QB : Nat × Nat) (hA : OnCurve QA) (hB : OnCurve QB)
    (hTA : ∀ j, NRep (TA j) (nsmul (2 * j + 1) QA)) (hTB : ∀ j, NRep (TB j) (nsmul (2 * j + 1) QB))
    (a b : BitVec 8) (ha : a = 0 ∨ a.toNat % 2 = 1) (ha' : a.toNat ≤ 15 ∨ 241 ≤ a.toNat)
    (hb : b = 0 ∨ b.toNat % 2 = 1) (hb' : b.toNat ≤ 15 ∨ 241 ≤ b.toNat) (r : Pr) (u v : Int)
    (hr : PRep r (Ed25519.add (zs u QA) (zs v QB))) :
    PRep (ladStep TA TB a b r) (Ed25519.add (zs (2 * u + sval a) QA) (zs (2 * v + sval b) QB)) := by
  have hu := zs_on G QA hA u
  have hv := zs_on G QB hB v
  have hX := G.closed _ _ hu hv
  have hXX := G.closed _ _ hX hX
  have c1 := F.dbl r _ hX hr
  have c2 := dig_rep G F TA QA hA hTA a ha ha' _ _ hXX c1
  have hsa := zs_on G QA hA (sval a)
  have c3 := dig_rep G F TB QB hB hTB b hb hb' _ _ (G.closed _ _ hXX hsa) c2
  have hsb := zs_on G QB hB (sval b)
  have e : Ed25519.add (Ed25519.add (Ed25519.add (Ed25519.add (zs u QA) (zs v QB))
      (Ed25519.add (zs u QA) (zs v QB))) (zs (sval a) QA)) (zs (sval b) QB) =
      Ed25519.add (zs (2 * u + sval a) QA) (zs (2 * v + sval b) QB) := by
    rw [add_add_add G _ _ _ _ hu hv hu hv, ← zs_add G QA hA, ← zs_add G QB hB,
      add_right_swap G _ _ _ (zs_on G QA hA _) (zs_on G QB hB _) hsa,
      G.assoc _ _ _ (G.closed _ _ (zs_on G QA hA _) hsa) (zs_on G QB hB _) hsb, ← zs_add G QA hA,
      ← zs_add G QB hB, show u + u = 2 * u by omega, show v + v = 2 * v by omega]
  rw [e] at c3
  exact F.proj _ _ (G.closed _ _ (zs_on G QA hA _) (zs_on G QB hB _)) c3

omit G F in
theorem pow_succ_int (k : Nat) : ((2 ^ (k + 1) : Nat) : Int) = 2 * ((2 ^ k : Nat) : Int) := by
  rw [Nat.pow_succ, Nat.mul_comm, Int.natCast_mul]; rfl

/-- The passes for digit indices `k - 1` down to 0. -/
theorem ladder_rep (TA TB : Nat → Pt) (QA QB : Nat × Nat) (hA : OnCurve QA) (hB : OnCurve QB)
    (hTA : ∀ j, NRep (TA j) (nsmul (2 * j + 1) QA)) (hTB : ∀ j, NRep (TB j) (nsmul (2 * j + 1) QB))
    (aN bN : Nat → BitVec 8) (ha : ∀ k, aN k = 0 ∨ (aN k).toNat % 2 = 1) (ha' : ∀ k, (aN k).toNat ≤ 15 ∨ 241 ≤ (aN k).toNat)
    (hb : ∀ k, bN k = 0 ∨ (bN k).toNat % 2 = 1) (hb' : ∀ k, (bN k).toNat ≤ 15 ∨ 241 ≤ (bN k).toNat) :
    ∀ k (r : Pr) (u v : Int), PRep r (Ed25519.add (zs u QA) (zs v QB)) →
      PRep (ladder TA TB aN bN k r)
        (Ed25519.add (zs (u * ((2 ^ k : Nat) : Int) + nafVal aN k) QA) (zs (v * ((2 ^ k : Nat) : Int) + nafVal bN k) QB))
  | 0, r, u, v, hr => by
    simp only [ladder, Nat.pow_zero, Int.natCast_one, Int.mul_one, nafVal, Int.add_zero]; exact hr
  | k + 1, r, u, v, hr => by
    have h := ladder_rep TA TB QA QB hA hB hTA hTB aN bN ha ha' hb hb' k _ _ _
      (step_rep G F TA TB QA QB hA hB hTA hTB (aN k) (bN k) (ha k) (ha' k) (hb k) (hb' k) r u v hr)
    have e : ∀ (w s N : Int), (2 * w + s) * ((2 ^ k : Nat) : Int) + N =
        w * ((2 ^ (k + 1) : Nat) : Int) + (N + s * ((2 ^ k : Nat) : Int)) := by
      intro w s N
      rw [pow_succ_int, Int.add_mul, Int.mul_assoc, Int.mul_left_comm w 2]
      omega
    rw [e, e] at h
    exact h

end

/-- Digits above `nafTop`'s index are zero, below the bound `k`. -/
theorem nafTop_zero (a b : Nat → BitVec 8) : ∀ k j, nafTop a b k < j → j < k → a j = 0 ∧ b j = 0
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j, h1, h2 => by
    unfold nafTop at h1
    split at h1
    · omega
    · rename_i hk
      by_cases e : j = k
      · subst e
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hk
        exact hk
      · exact nafTop_zero a b k j h1 (by omega)

theorem nafVal_zero_above (d : Nat → BitVec 8) (m : Nat) :
    ∀ n, m ≤ n → (∀ j, m ≤ j → j < n → d j = 0) → nafVal d n = nafVal d m
  | 0, h, _ => by rw [show m = 0 by omega]
  | n + 1, h, hz => by
    by_cases e : m = n + 1
    · rw [e]
    · simp only [nafVal]
      rw [hz n (by omega) (by omega), sval_zero, Int.zero_mul, Int.add_zero,
        nafVal_zero_above d m n (by omega) fun j h1 h2 => hz j h1 (by omega)]

end C3.RV32.EdM
