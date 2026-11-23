import C3BootProofs.Proofs.SvExtLink
import C3BootProofs.Proofs.CheckpointLine
import C3BootProofs.Proofs.Pair64
import C3BootProofs.Spec.Checkpoint

/-!
# The checkpoint the code read, as `verifyCheckpoint` reads it

Its lines (`splitLine` from the code's newline scan) and its tree size
(`treeSize` from the code's digit loop).
-/

namespace C3.RV32.Sv

open C3.Image

theorem nlScan_bound {M : Word → BitVec 8} {p : Word} : ∀ {k f ix : Nat}, nlScan M p k f = some ix → k ≤ ix ∧ ix < k + f
  | _, 0, _, h => by cases h
  | k, f + 1, ix, h => by
    unfold nlScan at h
    by_cases hc : M (p + BitVec.ofNat 32 k) = 0x0A
    · rw [ite_eq_left hc] at h; cases h; exact ⟨Nat.le_refl _, by omega⟩
    · rw [ite_eq_right hc] at h
      have := nlScan_bound h
      exact ⟨by omega, by omega⟩

theorem splitLine_cons_ne {b : Nat} {rest : Bytes} (hb : b ≠ 10) :
    splitLine (b :: rest) = (do let (l, r) ← splitLine rest; pure (b :: l, r)) := by
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | b
  all_goals first | exact absurd rfl hb | rfl

/-- `checkpoint::line`'s newline scan as `splitLine`. -/
theorem splitLine_scan {M : Word → BitVec 8} {p : Word} : ∀ {k f ix : Nat}, nlScan M p k f = some ix →
    splitLine (memBytes M (p + BitVec.ofNat 32 k) f) =
      some (memBytes M (p + BitVec.ofNat 32 k) (ix - k), memBytes M (p + BitVec.ofNat 32 (ix + 1)) (k + f - (ix + 1)))
  | _, 0, _, h => by cases h
  | k, f + 1, ix, h => by
    have hb := nlScan_bound h
    unfold nlScan at h
    rw [memBytes_succ]
    by_cases hc : M (p + BitVec.ofNat 32 k) = 0x0A
    · rw [ite_eq_left hc] at h
      cases h
      rw [hc, Nat.sub_self, show (0x0A : BitVec 8).toNat = 10 from rfl, ← add_ofNat_assoc,
        show k + (f + 1) - (k + 1) = f by omega]
      rfl
    · rw [ite_eq_right hc] at h
      have hne : (M (p + BitVec.ofNat 32 k)).toNat ≠ 10 := fun e => hc (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      rw [splitLine_cons_ne hne, show p + BitVec.ofNat 32 k + 1 = p + BitVec.ofNat 32 (k + 1) by rw [← add_ofNat_assoc]; rfl,
        splitLine_scan h]
      have hb' := nlScan_bound h
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [show ix - k = (ix - (k + 1)) + 1 by omega, memBytes_succ,
        show p + BitVec.ofNat 32 k + 1 = p + BitVec.ofNat 32 (k + 1) by rw [← add_ofNat_assoc]; rfl,
        show k + 1 + f - (ix + 1) = k + (f + 1) - (ix + 1) by omega]
      rfl

theorem splitLine_scan0 {M : Word → BitVec 8} {p : Word} {n ix : Nat} (h : nlScan M p 0 n = some ix) :
    splitLine (memBytes M p n) = some (memBytes M p ix, memBytes M (p + BitVec.ofNat 32 (ix + 1)) (n - (ix + 1))) := by
  have := splitLine_scan h
  rw [add_ofNat_zero, Nat.sub_zero, Nat.zero_add] at this
  exact this

/-- The digit a byte is, as the code computes it. -/
abbrev ckDigit (b : BitVec 8) : Word := ((b.zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF

set_option maxRecDepth 100000 in
theorem ckDigit_ok : ∀ b : BitVec 8, (ckDigit b).toNat < (BitVec.ofNat 32 0xA).toNat →
    48 ≤ b.toNat ∧ b.toNat ≤ 57 ∧ (ckDigit b).toNat = b.toNat - 48 := by decide

theorem svSltu_tn (a b : Word) : (aluEval .sltu a b).toNat = if a.toNat < b.toNat then 1 else 0 := by
  simp only [aluEval, BitVec.ult]
  by_cases h : a.toNat < b.toNat
  · rw [ite_eq_left (decide_eq_true h), ite_eq_left h]; rfl
  · rw [ite_eq_right (by simpa using h), ite_eq_right h]; rfl

theorem sltu01 (a b : Word) : aluEval .sltu a b = 0 ∨ aluEval .sltu a b = 1 := by
  simp only [aluEval]
  by_cases h : a.ult b = true
  · rw [ite_eq_left h]; exact .inr rfl
  · rw [ite_eq_right h]; exact .inl rfl

theorem and01 {x y : Word} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (h : x &&& y = 0) : x = 0 ∨ y = 0 := by
  rcases hx with rfl | rfl
  · exact .inl rfl
  · rcases hy with rfl | rfl
    · exact .inr rfl
    · exact absurd h (by decide)

theorem sltu_zero {a b : Word} (h : aluEval .sltu a b = 0) : ¬ a.toNat < b.toNat := by
  intro hl
  have := svSltu_tn a b
  rw [h, ite_eq_left hl] at this
  exact absurd this (by decide)

theorem mul_div_lt (a k : Nat) (ha : a < 2 ^ 32) (hk : k < 2 ^ 32) : a * k / 2 ^ 32 < 2 ^ 32 :=
  (Nat.div_lt_iff_lt_mul (by decide)).mpr (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hk) (by decide))

theorem mulhu_toNat (a : Word) (k : Nat) (hk : k < 2 ^ 32) :
    (aluEval .mulhu a (BitVec.ofNat 32 k)).toNat = a.toNat * k / 2 ^ 32 := by
  simp only [aluEval]
  rw [ofNat_toNat_lt hk, ofNat_toNat_lt (mul_div_lt _ _ a.isLt hk)]

theorem ckd_nat (x y z A lo' c hi' : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hz : z < 10)
    (hA : A = (y * 10 % 2 ^ 32 + x * 10 / 2 ^ 32) % 2 ^ 32) (nH : ¬ 0 < y * 10 / 2 ^ 32)
    (nA : ¬ A < x * 10 / 2 ^ 32) (hlo : lo' = (z + x * 10 % 2 ^ 32) % 2 ^ 32)
    (hc : c = if lo' < x * 10 % 2 ^ 32 then 1 else 0) (hhi : hi' = (A + c) % 2 ^ 32) (h3 : c = 0 ∨ ¬ hi' < A) :
    hi' * 2 ^ 32 + lo' = (y * 2 ^ 32 + x) * 10 + z := by
  have e10 : x * 10 = x * 10 / 2 ^ 32 * 2 ^ 32 + x * 10 % 2 ^ 32 := by
    rw [Nat.mul_comm (x * 10 / 2 ^ 32)]; exact (Nat.div_add_mod _ _).symm
  have hc0 : x * 10 / 2 ^ 32 < 10 := by omega
  have hl0 : x * 10 % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hy10 : y * 10 < 2 ^ 32 := by
    rcases Nat.lt_or_ge (y * 10) (2 ^ 32) with h | h
    · exact h
    · exact absurd (Nat.div_pos h (by decide)) nH
  rw [Nat.mod_eq_of_lt hy10] at hA
  have hA' : A = y * 10 + x * 10 / 2 ^ 32 := by
    rcases Nat.lt_or_ge (y * 10 + x * 10 / 2 ^ 32) (2 ^ 32) with h | h
    · rw [hA, Nat.mod_eq_of_lt h]
    · have : A = y * 10 + x * 10 / 2 ^ 32 - 2 ^ 32 := by
        rw [hA, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      exact absurd (by omega) nA
  subst hA'
  rcases Nat.lt_or_ge (z + x * 10 % 2 ^ 32) (2 ^ 32) with h | h
  · have hl : lo' = z + x * 10 % 2 ^ 32 := by rw [hlo, Nat.mod_eq_of_lt h]
    rw [ite_eq_right (by omega)] at hc
    subst hc
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at hhi
    subst hhi hl
    omega
  · have hl : lo' = z + x * 10 % 2 ^ 32 - 2 ^ 32 := by
      rw [hlo, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [ite_eq_left (by omega)] at hc
    subst hc
    have hn : y * 10 + x * 10 / 2 ^ 32 + 1 < 2 ^ 32 := by
      rcases h3 with h3 | h3
      · exact absurd h3 (by decide)
      · rcases Nat.lt_or_ge (y * 10 + x * 10 / 2 ^ 32 + 1) (2 ^ 32) with h' | h'
        · exact h'
        · have : hi' = y * 10 + x * 10 / 2 ^ 32 + 1 - 2 ^ 32 := by
            rw [hhi, Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]
          exact absurd (by omega) h3
    rw [Nat.mod_eq_of_lt hn] at hhi
    have hr : (y * 2 ^ 32 + x) * 10 = y * 10 * 2 ^ 32 + (x * 10 / 2 ^ 32 * 2 ^ 32 + x * 10 % 2 ^ 32) := by
      rw [Nat.add_mul, Nat.mul_right_comm, ← e10]
    rw [hhi, hl, hr]
    generalize x * 10 / 2 ^ 32 = C at *
    generalize x * 10 % 2 ^ 32 = Lw at *
    omega

/-- One digit of the tree size: the byte is a digit, and the 64-bit value
becomes ten times itself plus the digit, without overflow. -/
theorem ckd_step {b : BitVec 8} {lo hi : Word}
    (h1 : (ckDigit b).toNat < (BitVec.ofNat 32 0xA).toNat)
    (h2 : (aluEval .sltu ((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA)))
      (aluEval .mulhu lo (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu hi (BitVec.ofNat 32 0xA))) = 0)
    (h3 : (aluEval .sltu (ckDigit b + (aluEval .mul lo (BitVec.ofNat 32 0xA))) (aluEval .mul lo (BitVec.ofNat 32 0xA))) &&&
      (aluEval .sltu (((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA))) +
        (aluEval .sltu (ckDigit b + (aluEval .mul lo (BitVec.ofNat 32 0xA))) (aluEval .mul lo (BitVec.ofNat 32 0xA))))
        ((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA)))) = 0) :
    48 ≤ b.toNat ∧ b.toNat ≤ 57 ∧
      pair64 (ckDigit b + aluEval .mul lo (BitVec.ofNat 32 0xA))
        (((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA))) +
          (aluEval .sltu (ckDigit b + (aluEval .mul lo (BitVec.ofNat 32 0xA))) (aluEval .mul lo (BitVec.ofNat 32 0xA)))) =
      pair64 lo hi * 10 + (b.toNat - 48) := by
  obtain ⟨d1, d2, dd⟩ := ckDigit_ok b h1
  refine ⟨d1, d2, ?_⟩
  obtain ⟨h2a, h2b⟩ := is_or0.mp h2
  have h3' := and01 (sltu01 _ _) (sltu01 _ _) h3
  have hlo := lo.isLt
  have hhi := hi.isLt
  have eml : (aluEval .mul lo (BitVec.ofNat 32 0xA)).toNat = lo.toNat * 10 % 2 ^ 32 := by
    simp only [aluEval]; rw [BitVec.toNat_mul, ofNat_toNat_lt (by decide)]
  have emh : (aluEval .mul hi (BitVec.ofNat 32 0xA)).toNat = hi.toNat * 10 % 2 ^ 32 := by
    simp only [aluEval]; rw [BitVec.toNat_mul, ofNat_toNat_lt (by decide)]
  have mhl := mulhu_toNat lo 0xA (by decide)
  have mhh := mulhu_toNat hi 0xA (by decide)
  have eA : ((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA))).toNat =
      (hi.toNat * 10 % 2 ^ 32 + lo.toNat * 10 / 2 ^ 32) % 2 ^ 32 := by
    rw [BitVec.toNat_add, emh, mhl]
  have eL : (ckDigit b + aluEval .mul lo (BitVec.ofNat 32 0xA)).toNat = ((b.toNat - 48) + lo.toNat * 10 % 2 ^ 32) % 2 ^ 32 := by
    rw [BitVec.toNat_add, eml, dd]
  have ec := svSltu_tn (ckDigit b + aluEval .mul lo (BitVec.ofNat 32 0xA)) (aluEval .mul lo (BitVec.ofNat 32 0xA))
  rw [eL, eml] at ec
  have nA := sltu_zero h2a
  rw [eA, mhl] at nA
  have nH := sltu_zero h2b
  rw [mhh, show (BitVec.ofNat 32 0x0).toNat = 0 from rfl] at nH
  have nC : aluEval .sltu (ckDigit b + aluEval .mul lo (BitVec.ofNat 32 0xA)) (aluEval .mul lo (BitVec.ofNat 32 0xA)) = 0 ∨
      ¬ (((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA))) +
        (aluEval .sltu (ckDigit b + (aluEval .mul lo (BitVec.ofNat 32 0xA))) (aluEval .mul lo (BitVec.ofNat 32 0xA)))).toNat <
        ((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA))).toNat :=
    h3'.imp id sltu_zero
  have nC' : (aluEval .sltu (ckDigit b + aluEval .mul lo (BitVec.ofNat 32 0xA)) (aluEval .mul lo (BitVec.ofNat 32 0xA))).toNat = 0 ∨
      ¬ (((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA))) +
        (aluEval .sltu (ckDigit b + (aluEval .mul lo (BitVec.ofNat 32 0xA))) (aluEval .mul lo (BitVec.ofNat 32 0xA)))).toNat <
        ((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA))).toNat :=
    nC.imp (fun h => by rw [h]; rfl) id
  unfold pair64
  exact ckd_nat lo.toNat hi.toNat (b.toNat - 48) _ _ _ _ hlo hhi (by omega) eA nH (by rw [eA]; exact nA) eL (by rw [svSltu_tn, eml])
    (BitVec.toNat_add _ _) nC'

/-- One step of the code's digit loop over `(count, pointer, x21, low, high)`. -/
abbrev ckF (M : Word → BitVec 8) : Word × Word × Word × Word × Word → Word × Word × Word × Word × Word :=
  fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFFF, s.2.1 + BitVec.ofNat 32 0x1, s.2.2.2.2,
    ckDigit (M s.2.1) + aluEval .mul s.2.2.2.1 (BitVec.ofNat 32 0xA),
    ((aluEval .mul s.2.2.2.2 (BitVec.ofNat 32 0xA)) + (aluEval .mulhu s.2.2.2.1 (BitVec.ofNat 32 0xA))) +
      aluEval .sltu (ckDigit (M s.2.1) + aluEval .mul s.2.2.2.1 (BitVec.ofNat 32 0xA)) (aluEval .mul s.2.2.2.1 (BitVec.ofNat 32 0xA)))

/-- What the code checks of one digit at `p` with the value `(lo, hi)` so far. -/
abbrev ckOk (M : Word → BitVec 8) (p lo hi : Word) : Prop :=
  (ckDigit (M p)).toNat < (BitVec.ofNat 32 0xA).toNat ∧
  (aluEval .sltu ((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA)))
    (aluEval .mulhu lo (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu hi (BitVec.ofNat 32 0xA))) = 0 ∧
  (aluEval .sltu (ckDigit (M p) + (aluEval .mul lo (BitVec.ofNat 32 0xA))) (aluEval .mul lo (BitVec.ofNat 32 0xA))) &&&
    (aluEval .sltu (((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA))) +
      (aluEval .sltu (ckDigit (M p) + (aluEval .mul lo (BitVec.ofNat 32 0xA))) (aluEval .mul lo (BitVec.ofNat 32 0xA))))
      ((aluEval .mul hi (BitVec.ofNat 32 0xA)) + (aluEval .mulhu lo (BitVec.ofNat 32 0xA)))) = 0

/-- The digit loop over `N` bytes: they are digits, and the value is their
decimal number after the value it started from. -/
theorem ckd_fold {M : Word → BitVec 8} : ∀ (N : Nat) {s s' : Word × Word × Word × Word × Word},
    (∀ i, i < N → ∀ s1, s1 = svIter (ckF M) i s → ckOk M s1.2.1 s1.2.2.2.1 s1.2.2.2.2) →
    s' = svIter (ckF M) N s →
    (memBytes M s.2.1 N).all (fun d => 48 ≤ d && d ≤ 57) = true ∧
      pair64 s'.2.2.2.1 s'.2.2.2.2 = (memBytes M s.2.1 N).foldl (fun acc d => acc * 10 + (d - 48)) (pair64 s.2.2.2.1 s.2.2.2.2) := by
  intro N
  induction N with
  | zero =>
    intro s s' _ e
    subst e
    exact ⟨rfl, rfl⟩
  | succ N ih =>
    intro s s' H e
    obtain ⟨k1, k2, k3⟩ := H 0 (Nat.succ_pos N) s rfl
    obtain ⟨d1, d2, hstep⟩ := ckd_step k1 k2 k3
    rw [svIter_succ] at e
    obtain ⟨ha, hf⟩ := ih (s := ckF M s) (fun i hi' s1 e1 => H (i + 1) (Nat.succ_lt_succ hi') s1 (e1.trans (svIter_succ _ i s).symm)) e
    rw [memBytes_succ]
    refine ⟨?_, ?_⟩
    · rw [List.all_cons]
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true d1, decide_eq_true d2⟩, ha⟩
    · rw [List.foldl_cons, ← hstep]
      exact hf

/-- A group of four characters whose last isn't padding, that decodes, and
non-empty text after it that decodes. -/
theorem base64Decode_append {c0 c1 c2 c3 : Nat} {rest : Bytes} (h3 : c3 ≠ 61)
    (hd : (base64Decode [c0, c1, c2, c3]).isSome = true) (hr : (base64Decode rest).isSome = true) (hne : rest ≠ []) :
    (base64Decode ([c0, c1, c2, c3] ++ rest)).isSome = true := by
  have h3' : ¬ c3 = b64Pad := h3
  rw [base64Decode.eq_2, ite_eq_right (fun h => h3' h.2), ite_eq_right h3'] at hd
  obtain ⟨g, hg'⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp hr
  cases rest with
  | nil => exact absurd rfl hne
  | cons x xs =>
    rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append, base64Decode.eq_3, hg', hr']
    rfl

/-- What the code checks of one base64 group at `pg`, the `gi`th of `wc`. -/
abbrev cgOk (M : Word → BitVec 8) (pg gi wc : Word) : Prop :=
  ((M pg = 0x3D) ∧ (gi + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq, base64Decode (memBytes M pg 4) = some bq ∧ (bq.length ≤ 3)) ∨
  ((¬ (M pg = 0x3D)) ∧ (M (pg + BitVec.ofNat 32 0x1) = 0x3D) ∧ (gi + BitVec.ofNat 32 0x1 = wc) ∧
    ∃ bq, base64Decode (memBytes M pg 4) = some bq ∧ (bq.length ≤ 3)) ∨
  ((¬ (M pg = 0x3D)) ∧ (¬ (M (pg + BitVec.ofNat 32 0x1) = 0x3D)) ∧
    (M ((pg + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ (gi + BitVec.ofNat 32 0x1 = wc) ∧
    ∃ bq, base64Decode (memBytes M pg 4) = some bq ∧ (bq.length ≤ 3)) ∨
  ((¬ (M pg = 0x3D)) ∧ (¬ (M (pg + BitVec.ofNat 32 0x1) = 0x3D)) ∧
    (¬ (M ((pg + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧
    (M (((pg + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧
    (gi + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq, base64Decode (memBytes M pg 4) = some bq ∧ (bq.length ≤ 3)) ∨
  ((¬ (M pg = 0x3D)) ∧ (¬ (M (pg + BitVec.ofNat 32 0x1) = 0x3D)) ∧
    (¬ (M ((pg + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧
    (¬ (M (((pg + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧
    ∃ bq, base64Decode (memBytes M pg 4) = some bq ∧ (bq.length ≤ 3))

theorem cgOk_decodes {M : Word → BitVec 8} {pg gi wc : Word} (h : cgOk M pg gi wc) :
    (base64Decode (memBytes M pg 4)).isSome = true := by
  rcases h with ⟨-, -, bq, hb, -⟩ | ⟨-, -, -, bq, hb, -⟩ | ⟨-, -, -, -, bq, hb, -⟩ | ⟨-, -, -, -, -, bq, hb, -⟩ |
    ⟨-, -, -, -, bq, hb, -⟩ <;> rw [hb] <;> rfl

/-- A group that isn't the last: no padding at its end. -/
theorem cgOk_mid {M : Word → BitVec 8} {pg gi wc : Word} (h : cgOk M pg gi wc) (hl : gi + BitVec.ofNat 32 0x1 ≠ wc) :
    ¬ M (((pg + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D := by
  rcases h with ⟨-, e, -⟩ | ⟨-, -, e, -⟩ | ⟨-, -, -, e, -⟩ | ⟨-, -, -, -, e, -⟩ | ⟨-, -, -, h3, -⟩
  · exact absurd e hl
  · exact absurd e hl
  · exact absurd e hl
  · exact absurd e hl
  · exact h3

theorem memBytes_four (M : Word → BitVec 8) (p : Word) :
    memBytes M p 4 = [(M p).toNat, (M (p + BitVec.ofNat 32 0x1)).toNat,
      (M ((p + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1)).toNat,
      (M (((p + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1)).toNat] := by
  rw [memBytes_succ, memBytes_succ, memBytes_succ, memBytes_succ, memBytes_zero]
  rfl

/-- `N` base64 groups from `p`, the `k`th to the `(k + N - 1)`th of `k + N`,
each as the code checks it: the text decodes. -/
theorem base64_groups {M : Word → BitVec 8} : ∀ (N k : Nat) {p : Word}, 1 ≤ N → k + N < 2 ^ 32 →
    (∀ i, i < N → cgOk M (p + BitVec.ofNat 32 (4 * i)) (BitVec.ofNat 32 (k + i)) (BitVec.ofNat 32 (k + N))) →
    (base64Decode (memBytes M p (4 * N))).isSome = true
  | 0, _, _, h1, _, _ => absurd h1 (by decide)
  | 1, k, p, _, _, H => by
    have := cgOk_decodes (H 0 (by decide))
    rwa [show 4 * 0 = 0 from rfl, add_ofNat_zero] at this
  | N + 2, k, p, _, hk, H => by
    have h0 := H 0 (by omega)
    rw [show 4 * 0 = 0 from rfl, add_ofNat_zero, Nat.add_zero] at h0
    have hmid := cgOk_mid h0 (by
      intro e
      have := congrArg BitVec.toNat e
      rw [show (BitVec.ofNat 32 k + BitVec.ofNat 32 0x1) = BitVec.ofNat 32 (k + 1) by rw [BitVec.ofNat_add_ofNat],
        ofNat_toNat_lt (k := k + 1) (by omega), ofNat_toNat_lt (k := k + (N + 2)) hk] at this
      omega)
    have hrest := base64_groups (N + 1) (k + 1) (p := p + BitVec.ofNat 32 4) (by omega) (by omega) (fun i hi => by
      have := H (i + 1) (by omega)
      rw [show p + BitVec.ofNat 32 (4 * (i + 1)) = p + BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * i) by
        rw [add_ofNat_assoc]; congr 2; omega, show k + (i + 1) = k + 1 + i by omega,
        show k + (N + 2) = k + 1 + (N + 1) by omega] at this
      exact this)
    rw [show 4 * (N + 2) = 4 + 4 * (N + 1) by omega, memBytes_split, memBytes_four]
    have hd := cgOk_decodes h0
    rw [memBytes_four] at hd
    refine base64Decode_append (fun e => hmid (BitVec.eq_of_toNat_eq (by rw [e]; rfl))) hd hrest ?_
    intro e
    have := congrArg List.length e
    rw [memBytes_length, List.length_nil] at this
    omega

/-- A tree size the code accepted, as `treeSize`. -/
theorem treeSize_code {M : Word → BitVec 8} {p lo hi : Word} {n : Nat} (hn1 : 1 ≤ n) (hn19 : n ≤ 19)
    (hlead : 1 < n → M p ≠ 0x30)
    (hdig : (memBytes M p n).all (fun d => 48 ≤ d && d ≤ 57) = true)
    (hval : pair64 lo hi = (memBytes M p n).foldl (fun acc d => acc * 10 + (d - 48)) 0)
    (hhi : hi.toNat < 2 ^ 31) :
    treeSize (memBytes M p n) = some (pair64 lo hi) := by
  have hlen := memBytes_length M p n
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hne : (memBytes M p (n' + 1)).isEmpty = false := by rw [memBytes_succ]; rfl
  have hl19 : decide ((memBytes M p (n' + 1)).length ≤ 19) = true := decide_eq_true (by rw [hlen]; exact hn19)
  have hz : (!(decide ((memBytes M p (n' + 1)).length > 1) && (memBytes M p (n' + 1)).head? == some 48)) = true := by
    rw [hlen, memBytes_succ, List.head?_cons]
    by_cases h1 : n' + 1 > 1
    · have h0 := hlead h1
      have : ((M p).toNat == 48) = false := by
        apply Bool.eq_false_iff.mpr
        intro e
        exact h0 (BitVec.eq_of_toNat_eq (by rw [of_decide_eq_true e]; rfl))
      show (!(decide (n' + 1 > 1) && (some (M p).toNat == some 48))) = true
      rw [show (some (M p).toNat == some 48) = ((M p).toNat == 48) from rfl, this, Bool.and_false]
      rfl
    · rw [decide_eq_false h1]
      rfl
  have h63 : decide (pair64 lo hi < 2 ^ 63) = true := by
    apply decide_eq_true
    unfold pair64
    have := lo.isLt
    omega
  unfold treeSize
  rw [hne, hl19, hz, hdig]
  simp only [Bool.not_false, Bool.true_and, require_true, Option.bind_eq_bind, Option.bind_some]
  rw [← hval, h63, require_true]
  rfl

end C3.RV32.Sv
