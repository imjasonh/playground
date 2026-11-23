import C3BootProofs.Models.EcdsaLoop
import C3BootProofs.Proofs.Pv384Lib4

/-!
# wNAF digits sum to the scalar

`wnafGo N L (L + 1) 0 0` is the window-5 NAF of `N < 2^L`: its digits are
zero or odd with magnitude below 16 (`wnafGo_dig`), and `Σ dᵢ 2ⁱ = N`
(`wnafGo_val`). Stored as bytes by `wnafBytes`, the loop's signed digit sum
`dsum` over the first `k` positions is that sum once `k` covers every
digit (`dsum_wnafBytes`).
-/

namespace C3.Models

open C3.RV32 C3.RV32.Pv

/-- `Σ dᵢ 2ⁱ` for the digits `ds`, least significant first. -/
def wval : List Int → Int
  | [] => 0
  | d :: ds => d + 2 * wval ds

theorem wval_append : ∀ (l1 l2 : List Int), wval (l1 ++ l2) = wval l1 + 2 ^ l1.length * wval l2
  | [], l2 => by simp [wval]
  | d :: l1, l2 => by
    simp only [List.cons_append, wval, wval_append l1 l2, List.length_cons, Int.pow_succ]
    rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm 2 (2 ^ l1.length), Int.add_assoc]

theorem wval_replicate : ∀ n, wval (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, wval, wval_replicate n]; rfl

theorem div_pow_add (N a b : Nat) : N / 2 ^ (a + b) = N / 2 ^ a / 2 ^ b := by
  rw [Nat.pow_add, Nat.div_div_eq_div_mul]

theorem wnafGo_val {N L : Nat} (hN : N < 2 ^ L) :
    ∀ fuel pos carry, carry ≤ 1 → pos ≤ L → L + 1 ≤ pos + fuel →
      wval (wnafGo N L fuel pos carry) = ((N / 2 ^ pos + carry : Nat) : Int) := by
  intro fuel
  induction fuel with
  | zero => intro pos carry _ hp hf; omega
  | succ fuel ih =>
    intro pos carry hc hp hf
    simp only [wnafGo]
    by_cases hlt : pos < L
    · rw [ite_eq_left hlt]
      have ha : N / 2 ^ pos < 2 ^ (L - pos) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos pos), ← Nat.pow_add, Nat.sub_add_cancel hp]; exact hN
      by_cases he : (carry + N / 2 ^ pos % 32) % 2 = 0
      · rw [ite_eq_left he]
        simp only [wval]
        rw [ih (pos + 1) carry hc hlt (by omega), div_pow_add N pos 1]
        generalize N / 2 ^ pos = a at he ha
        clear ih
        omega
      · rw [ite_eq_right he]
        by_cases hw : carry + N / 2 ^ pos % 32 < 16
        · simp only [hw, ↓reduceIte, Nat.sub_zero]
          have hk1 : 1 ≤ min 5 (L - pos) := by omega
          rw [wval_append, ih _ 0 (Nat.zero_le _) (by omega) (by omega)]
          simp only [List.length_cons, List.length_replicate, wval, wval_replicate]
          rw [show min 5 (L - pos) - 1 + 1 = min 5 (L - pos) by omega, div_pow_add N pos]
          have hk5 : min 5 (L - pos) < 5 → L - pos = min 5 (L - pos) := fun h => by omega
          have hk6 : min 5 (L - pos) ≤ 5 := Nat.min_le_left _ _
          generalize min 5 (L - pos) = k at hk1 hk5 hk6
          generalize N / 2 ^ pos = a at he hw ha
          have hb : k = 5 ∨ a < 2 ^ k := by
            by_cases h : k < 5
            · rw [hk5 h] at ha; exact Or.inr ha
            · exact Or.inl (by omega)
          clear ih hk5 ha
          rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl <;>
            simp only [Nat.reducePow] at hb ⊢ <;> omega
        · simp only [hw, ↓reduceIte]
          have h15 : 15 ≤ N / 2 ^ pos := by have := Nat.mod_le (N / 2 ^ pos) 32; omega
          have h4 : 4 ≤ L - pos := by
            refine Nat.le_of_not_lt fun h => ?_
            have : 2 ^ (L - pos) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
            have : (2 : Nat) ^ 3 = 8 := rfl
            omega
          have hk1 : 1 ≤ min 5 (L - 1 - pos) := by omega
          rw [wval_append, ih _ 1 (Nat.le_refl _) (by omega) (by omega)]
          simp only [List.length_cons, List.length_replicate, wval, wval_replicate]
          rw [show min 5 (L - 1 - pos) - 1 + 1 = min 5 (L - 1 - pos) by omega, div_pow_add N pos]
          have hk5 : min 5 (L - 1 - pos) < 5 → L - pos = min 5 (L - 1 - pos) + 1 := fun h => by omega
          have hk6 : min 5 (L - 1 - pos) ≤ 5 := Nat.min_le_left _ _
          generalize min 5 (L - 1 - pos) = k at hk1 hk5 hk6
          generalize N / 2 ^ pos = a at he hw ha
          have hb : k = 5 ∨ a < 2 ^ (k + 1) := by
            by_cases h : k < 5
            · rw [hk5 h] at ha; exact Or.inr ha
            · exact Or.inl (by omega)
          clear ih hk5 ha
          rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl <;>
            simp only [Nat.reducePow, Nat.reduceAdd] at hb ⊢ <;> omega
    · rw [ite_eq_right hlt]
      have h0 : N / 2 ^ pos = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [h0]
      split
      · simp only [wval]; omega
      · simp only [wval]; omega

/-- A wNAF digit: zero, or odd with magnitude below 16. -/
def WDig (d : Int) : Prop := d = 0 ∨ (d.natAbs % 2 = 1 ∧ d.natAbs < 16)

theorem wnafGo_dig {N L : Nat} : ∀ fuel pos carry, carry ≤ 1 → ∀ d ∈ wnafGo N L fuel pos carry, WDig d := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ d hd; simp [wnafGo] at hd
  | succ fuel ih =>
    intro pos carry hc d hd
    simp only [wnafGo] at hd
    by_cases hlt : pos < L
    · rw [ite_eq_left hlt] at hd
      by_cases he : (carry + N / 2 ^ pos % 32) % 2 = 0
      · rw [ite_eq_left he, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inl rfl
        · exact ih _ _ hc d hd
      · rw [ite_eq_right he] at hd
        have hm := Nat.mod_lt (N / 2 ^ pos) (show 32 > 0 by decide)
        by_cases hw : carry + N / 2 ^ pos % 32 < 16
        · simp only [hw, ↓reduceIte, List.cons_append, List.mem_cons, List.mem_append, List.mem_replicate] at hd
          rcases hd with rfl | ⟨_, rfl⟩ | hd
          · exact Or.inr ⟨by omega, by omega⟩
          · exact Or.inl rfl
          · exact ih _ _ (Nat.zero_le _) d hd
        · simp only [hw, ↓reduceIte, List.cons_append, List.mem_cons, List.mem_append, List.mem_replicate] at hd
          rcases hd with rfl | ⟨_, rfl⟩ | hd
          · exact Or.inr ⟨by omega, by omega⟩
          · exact Or.inl rfl
          · exact ih _ _ (Nat.le_refl _) d hd
    · rw [ite_eq_right hlt] at hd
      split at hd
      · simp at hd
      · rw [List.mem_singleton] at hd; subst hd; exact Or.inr ⟨by omega, by omega⟩

theorem digOk_digB {d : Int} (h : WDig d) : DigOk (digB d) := by
  unfold DigOk digB
  rcases h with rfl | ⟨h1, h2⟩
  · exact Or.inl rfl
  · rcases Int.lt_or_le d 0 with hd | hd
    · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)

theorem dval_digB {d : Int} (h : WDig d) : dval (digB d) = d := by
  unfold dval digB
  rcases h with rfl | ⟨h1, h2⟩
  · rfl
  · split <;> omega

theorem getD_wdig {ds : List Int} (h : ∀ d ∈ ds, WDig d) (i : Nat) : WDig (ds.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < ds.length
  · rw [List.getElem?_eq_getElem hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (by omega)]; exact Or.inl rfl

theorem wnafBytes_getD (ds : List Int) {n i : Nat} (hi : i < n) : (wnafBytes ds n).getD i 0 = digB (ds.getD i 0) := by
  unfold wnafBytes
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  split
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- `Σ_{i<k} dsᵢ 2ⁱ`. -/
def gsum (ds : List Int) : Nat → Int
  | 0 => 0
  | k + 1 => ds.getD k 0 * 2 ^ k + gsum ds k

theorem gsum_cons (d : Int) (ds : List Int) : ∀ m, gsum (d :: ds) (m + 1) = d + 2 * gsum ds m
  | 0 => by simp [gsum]
  | m + 1 => by
    rw [gsum, gsum_cons d ds m, gsum, List.getD_cons_succ, Int.pow_succ, Int.mul_add]
    rw [show ds.getD m 0 * (2 ^ m * 2) = 2 * (ds.getD m 0 * 2 ^ m) by
      rw [Int.mul_comm (2 ^ m), ← Int.mul_assoc, Int.mul_comm _ 2, Int.mul_assoc]]
    omega

theorem gsum_nil : ∀ m, gsum [] m = 0
  | 0 => rfl
  | m + 1 => by rw [gsum, gsum_nil m, List.getD_nil, Int.zero_mul, Int.add_zero]

theorem gsum_wval : ∀ (ds : List Int) (m : Nat), ds.length ≤ m → gsum ds m = wval ds
  | [], m, _ => gsum_nil m
  | d :: ds, m + 1, h => by
    rw [gsum_cons, wval, gsum_wval ds m (by simp at h; omega)]
  | _ :: _, 0, h => by simp at h

theorem dsum_wnafBytes {ds : List Int} (h : ∀ d ∈ ds, WDig d) {n : Nat} :
    ∀ k, k ≤ n → dsum (wnafBytes ds n) k = gsum ds k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [dsum, gsum, dsum_wnafBytes h k (by omega), wnafBytes_getD ds (by omega), dval_digB (getD_wdig h k)]

theorem wnafBytes_digOk {ds : List Int} (h : ∀ d ∈ ds, WDig d) (n : Nat) (k : Nat) :
    DigOk ((wnafBytes ds n).getD k 0) := by
  by_cases hk : k < n
  · rw [wnafBytes_getD ds hk]; exact digOk_digB (getD_wdig h k)
  · unfold wnafBytes
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    exact Or.inl rfl

/-- The digits of `N < 2^L`, as bytes, sum to `N` over any `k` positions
that cover them. -/
theorem wnaf_dsum {N L k : Nat} (hN : N < 2 ^ L) (hk : (wnafGo N L (L + 1) 0 0).length ≤ k) (hkn : k ≤ L + 1) :
    dsum (wnafBytes (wnafGo N L (L + 1) 0 0) (L + 1)) k = N := by
  rw [dsum_wnafBytes (wnafGo_dig _ _ _ (Nat.zero_le _)) k hkn, gsum_wval _ _ hk,
    wnafGo_val hN _ _ _ (Nat.zero_le _) (Nat.zero_le _) (by omega)]
  simp

end C3.Models
