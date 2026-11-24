import C3BootProofs.Proofs.SvPvModel
import C3BootProofs.Proofs.SvEd
import C3BootProofs.Proofs.EcdsaSig

/-!
# `sigstore::verify`: a memory that `SvPvAt` describes

`SvP384Model'` assumes a memory that holds the prehash, `r`, and `s` where
`p384_verify_prehash` reads them, and the key and the scalar range's bound
as in the caller's memory. `svPvAt_frame` builds one from the caller's
memory by writing the three into their stack slots. The rest of this file
states the lengths and byte ranges of the hashes and scalars that the
witness and `SvP384Model'`'s result need.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.Pv

theorem svBytes_self {l : Bytes} {n : Nat} (hl : l.length = n) (hb : ∀ b ∈ l, b < 256) : svBytes l n = l := by
  unfold svBytes
  apply List.ext_getElem
  · rw [hl, List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [BitVec.toNat_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    exact Nat.mod_eq_of_lt (hb _ (List.getElem_mem h2))

theorem round512_length (w : Array Sha512.W64) (v : List Sha512.W64) (t : Nat) :
    (Sha512.round w v t).length = v.length := by
  unfold Sha512.round
  split <;> rfl

theorem foldl512_length {β : Type} {f : List Sha512.W64 → β → List Sha512.W64}
    (hf : ∀ v t, (f v t).length = v.length) : ∀ (l : List β) (v : List Sha512.W64), (l.foldl f v).length = v.length
  | [], _ => rfl
  | t :: l, v => by rw [List.foldl_cons, foldl512_length hf l, hf]

theorem compress512_length (hv : List Sha512.W64) (block : Bytes) : (Sha512.compress hv block).length = hv.length := by
  unfold Sha512.compress
  rw [List.length_zipWith, foldl512_length (round512_length _), Nat.min_self]

theorem wordBytes512_length : ∀ l : List Sha512.W64, (l.flatMap Sha512.wordBytes).length = 8 * l.length
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, wordBytes512_length l, List.length_cons]
    show 8 + 8 * l.length = 8 * (l.length + 1)
    omega

theorem sha384_length (msg : Bytes) : (sha384 msg).length = 48 := by
  unfold sha384
  rw [List.length_take, wordBytes512_length, foldl512_length compress512_length]
  rfl

theorem sha384_lt (msg : Bytes) : ∀ b ∈ sha384 msg, b < 256 := by
  intro b hb
  unfold sha384 at hb
  obtain ⟨w, -, hw⟩ := List.mem_flatMap.mp (List.mem_of_mem_take hb)
  unfold Sha512.wordBytes at hw
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hw
  exact Nat.mod_lt _ (by decide)

/-- `der::scalar::<N>`'s value has `N` bytes. -/
theorem derScalarOf_bytes {N : Nat} {L : Bytes} {rp : Word} {r : Except DerError DerTlv} {bs : Bytes}
    (hL : ∀ b ∈ L, b < 256) (h : derScalarOf N L rp r = .ok bs) : bs.length = N ∧ ∀ b ∈ bs, b < 256 := by
  unfold derScalarOf at h
  split at h
  next t _ _ =>
    generalize hc : (if (t.content L).head? = some 0 then (t.content L).drop 1 else t.content L) = c at h
    have hm : ∀ b ∈ c, b ∈ L := by
      intro b hb
      subst hc
      split at hb
      · exact List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_drop hb))
      · exact List.mem_of_mem_drop (List.mem_of_mem_take hb)
    by_cases hn : N < c.length
    · rw [ite_eq_left hn] at h; cases h
    · rw [ite_eq_right hn] at h
      cases h
      have hle := Nat.le_of_not_lt hn
      refine ⟨?_, fun b hb => ?_⟩
      · rw [List.length_append, List.length_replicate]; omega
      · rcases List.mem_append.mp hb with h1 | h1
        · rw [List.eq_of_mem_replicate h1]; decide
        · exact hL b (hm b h1)
  next => cases h
  next => cases h

/-- `der::ecdsa_signature::<N>`'s `r` and `s` have `N` bytes each. -/
theorem ecdsaSigOf_bytes {N : Nat} {M : Word → BitVec 8} {p : Word} {n : Nat} {r s : Bytes}
    (h : ecdsaSigOf N M p n = .ok (r, s)) :
    (r.length = N ∧ ∀ b ∈ r, b < 256) ∧ (s.length = N ∧ ∀ b ∈ s, b < 256) := by
  unfold ecdsaSigOf at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · next r' hr =>
        split at h
        · cases h
        · next s' hs =>
          split at h
          · cases h
            exact ⟨derScalarOf_bytes memBytes_mem_lt hr, derScalarOf_bytes memBytes_mem_lt hs⟩
          · cases h
    · cases h

/-- An address `n` bytes from `a` lies past the 0x1690 bytes from `B + 0x21A0`
when the `n` bytes at `a` lie outside the stack. -/
theorem off_of_sep {B a : Word} {n : Nat} (hs : Sep a n (B + 0xFFFFFE60) 0x39D0) :
    ∀ i, i < n → 0x1690 ≤ (a + BitVec.ofNat 32 i - (B + 0x21A0)).toNat := by
  intro i hi
  refine Nat.le_of_not_lt fun hlt => hs i hi (0x2340 + (a + BitVec.ofNat 32 i - (B + 0x21A0)).toNat) (by omega) ?_
  generalize a + BitVec.ofNat 32 i = x at hlt ⊢
  bv_omega

theorem isrn_off {B : Word} (RS : SvRoSep B) :
    ∀ i, i < 48 → 0x1690 ≤ (ISRN + BitVec.ofNat 32 i - (B + 0x21A0)).toNat :=
  off_of_sep fun i hi j hj e => RS.symm (0x470 + i) (by omega) j hj (by rw [← e]; unfold ISRN; bv_omega)

/-- The caller's memory with the prehash `h`, `r`, and `s` in three stack
slots that don't overlap, at `e1`, `e2`, and `e3` from `B + 0x21A0`, is a
memory that `SvPvAt` describes. -/
theorem svPvAt_frame {M : Word → BitVec 8} {B pk : Word} {len e1 e2 e3 : Nat} {h sr ss : Bytes}
    (hk : ∀ i, i < 0x61 → 0x1690 ≤ (pk + BitVec.ofNat 32 i - (B + 0x21A0)).toNat)
    (hn : ∀ i, i < 48 → 0x1690 ≤ (ISRN + BitVec.ofNat 32 i - (B + 0x21A0)).toNat)
    (hl : h.length = min len 48) (hb : ∀ b ∈ h, b < 256)
    (b1 : e1 + 48 ≤ 0x1690) (b2 : e2 + 48 ≤ 0x1690) (b3 : e3 + 48 ≤ 0x1690)
    (d12 : e1 + 48 ≤ e2 ∨ e2 + 48 ≤ e1) (d13 : e1 + 48 ≤ e3 ∨ e3 + 48 ≤ e1) (d23 : e2 + 48 ≤ e3 ∨ e3 + 48 ≤ e2) :
    ∃ M', SvPvAt M M' pk (B + 0x21A0 + BitVec.ofNat 32 e1) len h (B + 0x21A0 + BitVec.ofNat 32 e2)
      (B + 0x21A0 + BitVec.ofNat 32 e3) sr ss := by
  have hoff : ∀ e j, e + j < 2 ^ 32 →
      (B + 0x21A0 + BitVec.ofNat 32 e + BitVec.ofNat 32 j - (B + 0x21A0)).toNat = e + j := fun e j hej => by
    rw [BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hej]
  have n12 : ∀ j, j < 48 → ¬ (e1 ≤ e2 + j ∧ e2 + j < e1 + 48) := by
    intro j hj ⟨x1, x2⟩; rcases d12 with d | d <;> omega
  have n13 : ∀ j, j < 48 → ¬ (e1 ≤ e3 + j ∧ e3 + j < e1 + 48) := by
    intro j hj ⟨x1, x2⟩; rcases d13 with d | d <;> omega
  have n23 : ∀ j, j < 48 → ¬ (e2 ≤ e3 + j ∧ e3 + j < e2 + 48) := by
    intro j hj ⟨x1, x2⟩; rcases d23 with d | d <;> omega
  let M' : Word → BitVec 8 := fun x =>
    if e1 ≤ (x - (B + 0x21A0)).toNat ∧ (x - (B + 0x21A0)).toNat < e1 + 48 then
      BitVec.ofNat 8 (h.getD ((x - (B + 0x21A0)).toNat - e1) 0)
    else if e2 ≤ (x - (B + 0x21A0)).toNat ∧ (x - (B + 0x21A0)).toNat < e2 + 48 then
      BitVec.ofNat 8 (sr.getD ((x - (B + 0x21A0)).toNat - e2) 0)
    else if e3 ≤ (x - (B + 0x21A0)).toNat ∧ (x - (B + 0x21A0)).toNat < e3 + 48 then
      BitVec.ofNat 8 (ss.getD ((x - (B + 0x21A0)).toNat - e3) 0)
    else M x
  have hout : ∀ x : Word, 0x1690 ≤ (x - (B + 0x21A0)).toNat → M' x = M x := fun x hx => by
    have c1 : ¬ (e1 ≤ (x - (B + 0x21A0)).toNat ∧ (x - (B + 0x21A0)).toNat < e1 + 48) := fun ⟨_, h2⟩ => by omega
    have c2 : ¬ (e2 ≤ (x - (B + 0x21A0)).toNat ∧ (x - (B + 0x21A0)).toNat < e2 + 48) := fun ⟨_, h2⟩ => by omega
    have c3 : ¬ (e3 ≤ (x - (B + 0x21A0)).toNat ∧ (x - (B + 0x21A0)).toNat < e3 + 48) := fun ⟨_, h2⟩ => by omega
    show (if _ then _ else _) = _
    rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right c3]
  refine ⟨M', ?_, ?_, ?_, ?_, ?_⟩
  · unfold memBytes
    exact List.map_congr_left fun i hi => by rw [hout _ (hk i (List.mem_range.mp hi))]
  · unfold memBytes
    exact List.map_congr_left fun i hi => by rw [hout _ (hn i (List.mem_range.mp hi))]
  · have hm : min len 48 ≤ 48 := Nat.min_le_right _ _
    rw [memBytes_svBytes (l := h) fun j hj => ?_, svBytes_self hl hb]
    have ho := hoff e1 j (by omega)
    have c1 : e1 ≤ e1 + j ∧ e1 + j < e1 + 48 := ⟨Nat.le_add_right _ _, by omega⟩
    show (if _ then _ else _) = _
    rw [ho, ite_eq_left c1, Nat.add_sub_cancel_left]
  · refine memBytes_svBytes fun j hj => ?_
    have ho := hoff e2 j (by omega)
    have c2 : e2 ≤ e2 + j ∧ e2 + j < e2 + 48 := ⟨Nat.le_add_right _ _, by omega⟩
    show (if _ then _ else _) = _
    rw [ho, ite_eq_right (n12 j hj), ite_eq_left c2, Nat.add_sub_cancel_left]
  · refine memBytes_svBytes fun j hj => ?_
    have ho := hoff e3 j (by omega)
    have c3 : e3 ≤ e3 + j ∧ e3 + j < e3 + 48 := ⟨Nat.le_add_right _ _, by omega⟩
    show (if _ then _ else _) = _
    rw [ho, ite_eq_right (n13 j hj), ite_eq_right (n23 j hj), ite_eq_left c3, Nat.add_sub_cancel_left]

end C3.RV32.Sv
