import C3BootProofs.Spec.Tuf

/-!
# Bounds from the specification

An RFC 3339 time that `rfc3339` reads has a four-digit year, so it is below
2^64 seconds, and `trusted_root.json` in a TUF part that decodes is at most
`maxDocLen` bytes.
-/

namespace C3

theorem acs_readDigits_lt : ∀ (n : Nat) (b : Bytes) (v : Nat) (r : Bytes), readDigits n b = some (v, r) → v < 10 ^ n
  | 0, b, v, r, h => by
    unfold readDigits at h; cases h; exact Nat.one_pos
  | n + 1, [], v, r, h => by unfold readDigits at h; cases h
  | n + 1, x :: rest, v, r, h => by
    unfold readDigits at h
    cases hc : (48 ≤ x && x ≤ 57) with
    | false => simp only [hc, require, Bool.false_eq_true, ite_false, Option.bind_eq_bind, Option.bind_none] at h; cases h
    | true =>
      simp only [hc, require, ite_true, Option.bind_eq_bind, Option.bind_some] at h
      cases hd : readDigits n rest with
      | none => rw [hd] at h; cases h
      | some p =>
        obtain ⟨v', r'⟩ := p
        rw [hd] at h
        simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have ih := acs_readDigits_lt n rest v' r' hd
        have hx : x ≤ 57 := by
          have := hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
        have : (x - 48) * 10 ^ n ≤ 9 * 10 ^ n := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.pow_succ]; omega

theorem acs_dt_lt {year : Nat} {b r : Bytes} {t : Nat} (hy : year < 10000)
    (h : readDateTime year b = some (t, r)) : t < 2 ^ 64 := by
  unfold readDateTime at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  cases h1 : readDigits 2 b with
  | none => rw [h1] at h; cases h
  | some p1 =>
  obtain ⟨mo, b1⟩ := p1
  rw [h1] at h; simp only [Option.bind_some] at h
  cases h2 : readDigits 2 b1 with
  | none => rw [h2] at h; cases h
  | some p2 =>
  obtain ⟨d, b2⟩ := p2
  rw [h2] at h; simp only [Option.bind_some] at h
  cases h3 : readDigits 2 b2 with
  | none => rw [h3] at h; cases h
  | some p3 =>
  obtain ⟨hh, b3⟩ := p3
  rw [h3] at h; simp only [Option.bind_some] at h
  cases h4 : readDigits 2 b3 with
  | none => rw [h4] at h; cases h
  | some p4 =>
  obtain ⟨mi, b4⟩ := p4
  rw [h4] at h; simp only [Option.bind_some] at h
  cases h5 : readDigits 2 b4 with
  | none => rw [h5] at h; cases h
  | some p5 =>
  obtain ⟨se, b5⟩ := p5
  rw [h5] at h; simp only [Option.bind_some] at h
  have l1 := acs_readDigits_lt 2 _ _ _ h1
  have l2 := acs_readDigits_lt 2 _ _ _ h2
  have l3 := acs_readDigits_lt 2 _ _ _ h3
  have l4 := acs_readDigits_lt 2 _ _ _ h4
  have l5 := acs_readDigits_lt 2 _ _ _ h5
  cases hc : (year ≥ 1970 && 1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ daysInMonth year mo && hh ≤ 23 && mi ≤ 59 && se ≤ 59) with
  | false => rw [hc] at h; simp only [require, Bool.false_eq_true, ite_false, Option.bind_none] at h; cases h
  | true =>
    rw [hc] at h; simp only [require, ite_true, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hdc : daysFromCivil year mo d ≤ 10000 * 366 := by
      unfold daysFromCivil; dsimp only
      split <;> split <;> omega
    simp only [Nat.reducePow] at l1 l2 l3 l4 l5 ⊢
    omega

theorem acs_rfc_lt {text : Bytes} {x : Nat} (h : rfc3339 text = some x) : x < 2 ^ 64 := by
  unfold rfc3339 at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  cases hy : readDigits 4 text with
  | none => rw [hy] at h; cases h
  | some p =>
  obtain ⟨year, rest⟩ := p
  have hyl := acs_readDigits_lt 4 text year rest hy
  rw [hy] at h; simp only [Option.bind_some] at h
  split at h
  · rename_i zone
    cases hd : readDateTime year _ with
    | none => rw [hd] at h; cases h
    | some q =>
      obtain ⟨t, r'⟩ := q
      have ht := acs_dt_lt (by simpa using hyl) hd
      rw [hd] at h; simp only [Option.bind_some] at h
      split at h
      · cases h; exact ht
      · split at h
        · cases hc : (!_ && _) with
          | false => rw [hc] at h; simp only [require, Bool.false_eq_true, ite_false, Option.bind_none] at h; cases h
          | true => rw [hc] at h; simp only [require, ite_true, Option.bind_some, Option.some.injEq] at h; cases h; exact ht
        · cases h
      · cases h
  · cases h

theorem acs_expires_lt {md : Meta} {x : Nat} (h : expires md = some x) : x < 2 ^ 64 := by
  unfold expires at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : md.signed.field (ascii!"expires") with
  | none => rw [h1] at h; cases h
  | some j =>
    rw [h1] at h; simp only [Option.bind_some] at h
    cases h2 : j.asStr with
    | none => rw [h2] at h; cases h
    | some s => rw [h2] at h; simp only [Option.bind_some] at h; exact acs_rfc_lt h


theorem acs_readLengths_le : ∀ (n : Nat) (b : Bytes) (lens : List Nat) (r : Bytes),
    readLengths n b = some (lens, r) → ∀ l ∈ lens, l ≤ maxDocLen
  | 0, b, lens, r, h => by
    unfold readLengths at h; cases h; intro l hl; cases hl
  | n + 1, b, lens, r, h => by
    unfold readLengths at h
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    cases h1 : readU32 b with
    | none => rw [h1] at h; cases h
    | some p =>
      obtain ⟨len, rest⟩ := p
      rw [h1] at h; simp only [Option.bind_some] at h
      cases hc : (1 ≤ len && len ≤ maxDocLen) with
      | false => rw [hc] at h; simp only [require, Bool.false_eq_true, ite_false, Option.bind_none] at h; cases h
      | true =>
        rw [hc] at h; simp only [require, ite_true, Option.bind_some] at h
        cases h2 : readLengths n rest with
        | none => rw [h2] at h; cases h
        | some q =>
          obtain ⟨lens', r'⟩ := q
          rw [h2] at h; simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          intro l hl
          cases hl with
          | head => have := hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
          | tail _ hl => exact acs_readLengths_le n rest lens' r' h2 l hl

theorem acs_splitDocs_le : ∀ (lens : List Nat) (b : Bytes) (docs : List Bytes) (r : Bytes),
    splitDocs lens b = some (docs, r) → ∀ d ∈ docs, ∃ l ∈ lens, d.length ≤ l
  | [], b, docs, r, h => by
    unfold splitDocs at h; cases h; intro d hd; cases hd
  | len :: lens, b, docs, r, h => by
    unfold splitDocs at h
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    cases hc : decide (len ≤ b.length) with
    | false => rw [hc] at h; simp only [require, Bool.false_eq_true, ite_false, Option.bind_none] at h; cases h
    | true =>
      rw [hc] at h; simp only [require, ite_true, Option.bind_some] at h
      cases h2 : splitDocs lens (b.drop len) with
      | none => rw [h2] at h; cases h
      | some q =>
        obtain ⟨docs', r'⟩ := q
        rw [h2] at h; simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        intro d hd
        cases hd with
        | head => exact ⟨len, List.mem_cons_self, List.length_take_le _ _⟩
        | tail _ hd =>
          obtain ⟨l, hl, hle⟩ := acs_splitDocs_le lens _ docs' r' h2 d hd
          exact ⟨l, List.mem_cons_of_mem _ hl, hle⟩

theorem acs_parts_le {b : Bytes} {parts : TufParts} (h : decodeTufParts b = some parts) :
    parts.trustedRoot.length ≤ maxDocLen := by
  unfold decodeTufParts at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  cases c1 : decide (b.length ≤ maxTufLen) with
  | false => rw [c1] at h; simp only [require, Bool.false_eq_true, ite_false, Option.bind_none] at h; cases h
  | true =>
  rw [c1] at h; simp only [require, ite_true, Option.bind_some] at h
  cases h1 : readExpect (ascii!"C3TU") b with
  | none => rw [h1] at h; cases h
  | some rest =>
  rw [h1] at h; simp only [Option.bind_some] at h
  cases h2 : readU16 rest with
  | none => rw [h2] at h; cases h
  | some p =>
  obtain ⟨ver, rest⟩ := p
  rw [h2] at h; simp only [Option.bind_some] at h
  cases c2 : (ver == 2) with
  | false => rw [c2] at h; simp only [Bool.false_eq_true, ite_false, Option.bind_none] at h; cases h
  | true =>
  rw [c2] at h; simp only [ite_true, Option.bind_some] at h
  cases h3 : readU16 rest with
  | none => rw [h3] at h; cases h
  | some p =>
  obtain ⟨cnt, rest⟩ := p
  rw [h3] at h; simp only [Option.bind_some] at h
  cases c3 : decide (cnt ≤ maxRoots) with
  | false => rw [c3] at h; simp only [Bool.false_eq_true, ite_false, Option.bind_none] at h; cases h
  | true =>
  rw [c3] at h; simp only [ite_true, Option.bind_some] at h
  cases h4 : readLengths (cnt + 2) rest with
  | none => rw [h4] at h; cases h
  | some p =>
  obtain ⟨lens, rest⟩ := p
  rw [h4] at h; simp only [Option.bind_some] at h
  cases h5 : splitDocs lens rest with
  | none => rw [h5] at h; cases h
  | some p =>
  obtain ⟨docs, rest⟩ := p
  rw [h5] at h; simp only [Option.bind_some] at h
  cases c4 : rest.isEmpty with
  | false => rw [c4] at h; simp only [Bool.false_eq_true, ite_false, Option.bind_none] at h; cases h
  | true =>
  rw [c4] at h; simp only [ite_true, Option.bind_some] at h
  cases hd : docs.reverse with
  | nil => rw [hd] at h; cases h
  | cons tr tl =>
    cases tl with
    | nil => rw [hd] at h; cases h
    | cons tg roots =>
      rw [hd] at h; simp only [Option.some.injEq] at h
      subst h
      have hm : tr ∈ docs := List.mem_reverse.mp (hd ▸ List.mem_cons_self)
      obtain ⟨l, hl, hle⟩ := acs_splitDocs_le lens _ docs _ h5 tr hm
      exact Nat.le_trans hle (acs_readLengths_le _ _ lens _ h4 l hl)

end C3
