import C3BootProofs.Spec.Merkle

/-!
# Lemmas about the Merkle inclusion specification

`hashes32` splits a proof into 32-byte hashes. `chunks32` does the same
for a length known to be a multiple of 32, so the machine proof can take one
hash at a time.
-/

namespace C3

/-- The first `k` 32-byte chunks of `b`. -/
def chunks32 : Nat → Bytes → List Bytes
  | 0, _ => []
  | k + 1, b => b.take 32 :: chunks32 k (b.drop 32)

theorem chunks32_length : ∀ k (b : Bytes), (chunks32 k b).length = k
  | 0, _ => rfl
  | k + 1, b => by simp only [chunks32, List.length_cons, chunks32_length k]

theorem hashes32_chunks : ∀ k (b : Bytes) (fuel : Nat), b.length = 32 * k → k ≤ fuel →
    hashes32 fuel b = some (chunks32 k b)
  | 0, b, fuel, hl, _ => by
    have : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases fuel <;> rfl
  | k + 1, b, fuel, hl, hk => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    match b, hl with
    | x :: xs, hl =>
      have hlen : ¬ (x :: xs).length < 32 := by omega
      have ih := hashes32_chunks k ((x :: xs).drop 32) f (by rw [List.length_drop]; omega) (by omega)
      simp only [hashes32, hlen, ite_false, ih, chunks32]
      rfl

theorem hashes32_none : ∀ (fuel : Nat) (b : Bytes), b.length ≤ fuel → b.length % 32 ≠ 0 → hashes32 fuel b = none
  | 0, b, hl, hm => by
    have : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; exact absurd rfl hm
  | f + 1, [], _, hm => absurd rfl hm
  | f + 1, x :: xs, hl, hm => by
    by_cases h : (x :: xs).length < 32
    · simp only [hashes32, h, ite_true]
    · have ih := hashes32_none f ((x :: xs).drop 32) (by rw [List.length_drop]; omega)
        (by rw [List.length_drop]; omega)
      simp only [hashes32, h, ite_false, ih]
      rfl

/-- `shiftEven` stops at an odd or zero `f`, and in between halves both. -/
theorem shiftEven_eq (f s : Nat) :
    shiftEven f s = if f % 2 = 0 ∧ f ≠ 0 then shiftEven (f / 2) (s / 2) else (f, s) := by
  rw [shiftEven]
  by_cases h : f % 2 = 0 ∧ f ≠ 0
  · rw [dite_eq_left h, ite_eq_left h]
  · rw [dite_eq_right h, ite_eq_right h]

/-- `inclusionPath`'s step for a hash `p` before the rest `ps`. -/
theorem inclusionPath_cons (f s : Nat) (r p : Bytes) (ps : List Bytes) :
    inclusionPath f s r (p :: ps) =
      if s = 0 then none
      else if f % 2 = 1 ∨ f = s then
        inclusionPath ((shiftEven f s).1 / 2) ((shiftEven f s).2 / 2) (nodeHash p r) ps
      else inclusionPath (f / 2) (s / 2) (nodeHash r p) ps := by
  rfl

/-- `rootFromInclusion` with the hashes split by `chunks32`: the checks
`root_from_inclusion` makes before its loop, then the loop, then the final
check that `sn` reached 0. -/
theorem rootFromInclusion_eq (index size : Nat) (leaf proof : Bytes) :
    rootFromInclusion index size leaf proof =
      if proof.length % 32 = 0 ∧ proof.length / 32 ≤ maxProofHashes ∧ index < size then
        match inclusionPath index (size - 1) leaf (chunks32 (proof.length / 32) proof) with
        | some (s, r) => if s = 0 then some r else none
        | none => none
      else none := by
  unfold rootFromInclusion
  by_cases h1 : proof.length % 32 = 0
  · rw [hashes32_chunks (proof.length / 32) proof proof.length (by omega) (by omega)]
    show ((require (decide ((chunks32 (proof.length / 32) proof).length ≤ maxProofHashes) &&
      decide (index < size))).bind fun _ => (inclusionPath index (size - 1) leaf
        (chunks32 (proof.length / 32) proof)).bind fun x => (require (x.fst == 0)).bind fun _ => pure x.snd) = _
    rw [chunks32_length]
    by_cases h2 : proof.length / 32 ≤ maxProofHashes ∧ index < size
    · rw [ite_eq_left ⟨h1, h2⟩]
      have hr : require (decide (proof.length / 32 ≤ maxProofHashes) && decide (index < size)) = some () := by
        rw [decide_eq_true h2.1, decide_eq_true h2.2]; rfl
      rw [hr]
      show ((inclusionPath index (size - 1) leaf (chunks32 (proof.length / 32) proof)).bind fun x =>
        (require (x.fst == 0)).bind fun _ => pure x.snd) = _
      cases inclusionPath index (size - 1) leaf (chunks32 (proof.length / 32) proof) with
      | none => rfl
      | some p =>
        obtain ⟨s, r⟩ := p
        by_cases hs : s = 0
        · subst hs; rfl
        · show ((require (s == 0)).bind fun _ => pure r) = if s = 0 then some r else none
          rw [ite_eq_right hs, show (s == 0) = false from by simp [hs]]; rfl
    · rw [ite_eq_right (fun h => h2 ⟨h.2.1, h.2.2⟩)]
      by_cases h3 : proof.length / 32 ≤ maxProofHashes
      · have h4 : ¬ index < size := fun h => h2 ⟨h3, h⟩
        rw [decide_eq_true h3, decide_eq_false h4]; rfl
      · rw [decide_eq_false h3]; rfl
  · rw [hashes32_none proof.length proof (Nat.le_refl _) h1]
    rw [ite_eq_right (fun h => h1 h.1)]; rfl

end C3
