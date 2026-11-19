import C3BootProofs.Proof.Code

/-!
# Decoding from a chunk of a long function

`fetchRel` reads the whole byte list, so `decide` on a fetch near the end of
a function of several thousand instructions walks thousands of list cells.
`fetchRel_chunk` moves the fetch to a short list that the function's bytes
from some offset start with, and the kernel decodes from that.
-/

namespace C3.RV32

theorem byteAt_drop (code : List Nat) (k i : Nat) : byteAt (code.drop k) i = byteAt code (k + i) := by
  unfold byteAt; rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem byteAt_append {c : List Nat} (d : List Nat) {i : Nat} (h : i < c.length) :
    byteAt (c ++ d) i = byteAt c i := by
  unfold byteAt; rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem fetchRel_drop (code : List Nat) {k off : Nat} (hk : k ≤ off) :
    fetchRel code off = fetchRel (code.drop k) (off - k) := by
  have e : ∀ j, byteAt (code.drop k) (off - k + j) = byteAt code (off + j) := fun j => by
    rw [byteAt_drop]; congr 1; omega
  have e0 := e 0
  simp only [Nat.add_zero] at e0
  have c2 : (off - k + 2 ≤ code.length - k) = (off + 2 ≤ code.length) :=
    propext ⟨fun h => by omega, fun h => by omega⟩
  have c4 : (off - k + 4 ≤ code.length - k) = (off + 4 ≤ code.length) :=
    propext ⟨fun h => by omega, fun h => by omega⟩
  unfold fetchRel
  rw [e0, e 1, e 2, e 3, List.length_drop]
  simp only [c2, c4]

theorem fetchRel_prefix {c : List Nat} (d : List Nat) {o : Nat} (h : o + 4 ≤ c.length) :
    fetchRel (c ++ d) o = fetchRel c o := by
  have c2 : (o + 2 ≤ (c ++ d).length) = (o + 2 ≤ c.length) :=
    propext ⟨fun _ => by omega, fun _ => by rw [List.length_append]; omega⟩
  have c4 : (o + 4 ≤ (c ++ d).length) = (o + 4 ≤ c.length) :=
    propext ⟨fun _ => by omega, fun _ => by rw [List.length_append]; omega⟩
  unfold fetchRel
  rw [byteAt_append d (by omega), byteAt_append d (by omega), byteAt_append d (by omega),
    byteAt_append d (by omega)]
  simp only [c2, c4]

/-- A fetch at `off` of `code` is the fetch at `off - k` of a list `c` that
the bytes of `code` from `k` start with, when `c` holds the four bytes from
`off` or all of the bytes from `k`. -/
theorem fetchRel_chunk {code c : List Nat} {k off : Nat} (hc : c <+: code.drop k) (hk : k ≤ off)
    (h4 : off - k + 4 ≤ c.length ∨ (code.drop k).length ≤ c.length) :
    fetchRel code off = fetchRel c (off - k) := by
  rw [fetchRel_drop code hk]
  obtain ⟨d, hd⟩ := hc
  rw [← hd]
  rcases h4 with h4 | h4
  · exact fetchRel_prefix d h4
  · have : d = [] := by
      rw [← hd, List.length_append] at h4
      exact List.eq_nil_of_length_eq_zero (by omega)
    rw [this, List.append_nil]

end C3.RV32
