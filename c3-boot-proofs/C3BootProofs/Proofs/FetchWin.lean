import C3BootProofs.Proof.Code

/-!
# `fetchRel` on a window of a function's bytes

`decide` on a `fetchRel` lemma walks the code list from its start, which for
a function of several kilobytes costs minutes and gigabytes over all its
instructions. These lemmas move the lookup to a short slice of the code, so
each instruction's lemma decides over the slice.
-/

namespace C3.RV32

theorem fetchRel_congr {c1 c2 : List Nat} {o1 o2 : Nat}
    (h2 : o1 + 2 ≤ c1.length ↔ o2 + 2 ≤ c2.length) (h4 : o1 + 4 ≤ c1.length ↔ o2 + 4 ≤ c2.length)
    (hb : ∀ j, j < 4 → o1 + j < c1.length → byteAt c1 (o1 + j) = byteAt c2 (o2 + j)) :
    fetchRel c1 o1 = fetchRel c2 o2 := by
  unfold fetchRel
  by_cases e2 : o1 + 2 ≤ c1.length
  · have e2' := h2.1 e2
    have b0 := hb 0 (by omega) (by omega)
    have b1 := hb 1 (by omega) (by omega)
    simp only [Nat.add_zero] at b0
    rw [ite_eq_left e2, ite_eq_left e2', b0, b1]
    by_cases e4 : o1 + 4 ≤ c1.length
    · rw [ite_eq_left e4, ite_eq_left (h4.1 e4), hb 2 (by omega) (by omega), hb 3 (by omega) (by omega)]
    · rw [ite_eq_right e4, ite_eq_right (fun h => e4 (h4.2 h))]
  · rw [ite_eq_right e2, ite_eq_right (fun h => e2 (h2.2 h))]

theorem fetchRel_win {code w : List Nat} {k m off : Nat} (hw : (code.drop k).take m = w)
    (hl : k + m ≤ code.length) (hk : k ≤ off) (hf : off + 4 ≤ k + m) :
    fetchRel code off = fetchRel w (off - k) := by
  subst hw
  have hlen : ((code.drop k).take m).length = m := by rw [List.length_take, List.length_drop]; omega
  apply fetchRel_congr (by rw [hlen]; exact ⟨fun _ => by omega, fun _ => by omega⟩)
    (by rw [hlen]; exact ⟨fun _ => by omega, fun _ => by omega⟩)
  intro j hj _
  unfold byteAt; congr 1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
    List.getElem?_drop, show k + (off - k + j) = off + j by omega]

theorem fetchRel_tail {code w : List Nat} {k off : Nat} (hw : code.drop k = w) (hk : k ≤ off) :
    fetchRel code off = fetchRel w (off - k) := by
  subst hw
  apply fetchRel_congr (by rw [List.length_drop]; exact ⟨fun _ => by omega, fun _ => by omega⟩)
    (by rw [List.length_drop]; exact ⟨fun _ => by omega, fun _ => by omega⟩)
  intro j hj _
  unfold byteAt; congr 1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
    show k + (off - k + j) = off + j by omega]
end C3.RV32
