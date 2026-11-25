import C3BootProofs.Proofs.AcceptSpecPin

/-!
# Where `decodeTufParts` finds each document

A part that decodes holds its documents, the roots and then `targets.json`
and `trusted_root.json`, one after another after the 8-byte header and the
index of their lengths. `acs_doc_at` turns the index stage's lengths into
the documents' places in flash.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.Json

theorem acs_readExpect {w b r : Bytes} (h : readExpect w b = some r) : r = b.drop w.length := by
  revert h
  unfold readExpect
  cases (b.take w.length == w && decide (w.length ≤ b.length)) <;> intro h
  · exact nomatch h
  · have e : some (b.drop w.length) = some r := h
    cases e; rfl

theorem acs_readU16 {b r : Bytes} {v : Nat} (h : readU16 b = some (v, r)) : r = b.drop 2 := by
  rcases b with _ | ⟨a, _ | ⟨c, rest⟩⟩
  · exact nomatch h
  · exact nomatch h
  · have e : some (a + 256 * c, rest) = some (v, r) := h
    cases e; rfl

theorem acs_readU32 {b r : Bytes} {v : Nat} (h : readU32 b = some (v, r)) : 4 ≤ b.length ∧ r = b.drop 4 := by
  rcases b with _ | ⟨a, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩
  · exact nomatch h
  · exact nomatch h
  · exact nomatch h
  · exact nomatch h
  · have e' : some (a + 256 * (c + 256 * (d + 256 * e)), rest) = some (v, r) := h
    cases e'; exact ⟨by simp only [List.length_cons]; omega, rfl⟩

theorem acs_readLengths : ∀ {n : Nat} {b r : Bytes} {lens : List Nat}, readLengths n b = some (lens, r) →
    lens.length = n ∧ 4 * n ≤ b.length ∧ r = b.drop (4 * n)
  | 0, b, r, lens, h => by
    have e : some ([], b) = some (lens, r) := h
    cases e; exact ⟨rfl, Nat.zero_le _, rfl⟩
  | n + 1, b, r, lens, h => by
    obtain ⟨⟨len, rest⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨lens', rest'⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    obtain ⟨hl, hle, hr⟩ := acs_readLengths h2
    obtain ⟨h4, hd⟩ := acs_readU32 h1
    rw [hd, List.drop_drop] at hr
    rw [hd, List.length_drop] at hle
    exact ⟨by rw [List.length_cons, hl], by omega, by rw [hr]; congr 1; omega⟩

theorem acs_splitDocs : ∀ {lens : List Nat} {b r : Bytes} {docs : List Bytes}, splitDocs lens b = some (docs, r) →
    docs.map List.length = lens ∧ lens.sum ≤ b.length ∧ r = b.drop lens.sum
  | [], b, r, docs, h => by
    have e : some ([], b) = some (docs, r) := h
    cases e; exact ⟨rfl, Nat.zero_le _, rfl⟩
  | len :: lens, b, r, docs, h => by
    obtain ⟨_, hq, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ds, rest⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    have hl : len ≤ b.length := of_decide_eq_true (require_eq_some.mp hq)
    obtain ⟨hm, hs, hr⟩ := acs_splitDocs h2
    rw [List.length_drop] at hs
    rw [List.drop_drop] at hr
    refine ⟨?_, by rw [List.sum_cons]; omega, by rw [hr, List.sum_cons]⟩
    rw [List.map_cons, hm, List.length_take, Nat.min_eq_left hl]

/-- **The documents of a part that decodes**: the roots number at most
`maxRoots`, the documents fill the part after the header and the index,
and each one starts after those before it. -/
theorem acs_decode_docs {b : Bytes} {parts : TufParts} (h : decodeTufParts b = some parts) :
    parts.roots.length ≤ maxRoots ∧
    8 + 4 * (parts.roots.length + 2) +
      ((parts.roots ++ [parts.targets, parts.trustedRoot]).map List.length).sum = b.length ∧
    ∀ i, i < parts.roots.length + 2 → (parts.roots ++ [parts.targets, parts.trustedRoot]).getD i [] =
      (b.drop (8 + 4 * (parts.roots.length + 2) +
        (((parts.roots ++ [parts.targets, parts.trustedRoot]).map List.length).take i).sum)).take
        ((parts.roots ++ [parts.targets, parts.trustedRoot]).getD i []).length := by
  unfold decodeTufParts at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨ver, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨cnt, r3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, hc, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨lens, r4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨docs, r5⟩, h5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, he, h⟩ := Option.bind_eq_some_iff.mp h
  have hcm : cnt ≤ maxRoots := of_decide_eq_true (require_eq_some.mp hc)
  have hemp : r5.isEmpty = true := require_eq_some.mp he
  obtain ⟨hll, hle, hr4⟩ := acs_readLengths h4
  rw [acs_readU16 h3, acs_readU16 h2, acs_readExpect h1] at hle
  simp only [List.length_drop, List.length_cons, List.length_nil] at hle
  replace hr4 : r4 = b.drop (8 + 4 * (cnt + 2)) := by
    rw [hr4, acs_readU16 h3, acs_readU16 h2, acs_readExpect h1]
    simp only [List.drop_drop, List.length_cons, List.length_nil]
  obtain ⟨hm, hs, hr5⟩ := acs_splitDocs h5
  have hdl : docs.length = cnt + 2 := by rw [← List.length_map (f := List.length), hm, hll]
  obtain ⟨tr, tg, rs, hr⟩ := acx_rev2 docs hdl
  have hdocs : docs = rs.reverse ++ [tg, tr] := by
    rw [← List.reverse_reverse docs, hr]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
  rw [hr] at h
  have e : some (TufParts.mk rs.reverse tg tr) = some parts := h
  cases e
  show rs.reverse.length ≤ maxRoots ∧ 8 + 4 * (rs.reverse.length + 2) + ((rs.reverse ++ [tg, tr]).map List.length).sum =
      b.length ∧ ∀ i, i < rs.reverse.length + 2 → (rs.reverse ++ [tg, tr]).getD i [] =
      (b.drop (8 + 4 * (rs.reverse.length + 2) + (((rs.reverse ++ [tg, tr]).map List.length).take i).sum)).take
        ((rs.reverse ++ [tg, tr]).getD i []).length
  have hrl : rs.reverse.length = cnt := by
    have := congrArg List.length hdocs
    rw [List.length_append, hdl] at this
    simp only [List.length_cons, List.length_nil] at this; omega
  rw [← hdocs, hrl, hm]
  have hb := List.isEmpty_iff.mp hemp
  rw [hr5, hr4, List.drop_drop, List.drop_eq_nil_iff] at hb
  rw [hr4, List.length_drop] at hs
  refine ⟨hcm, by omega, fun i hi => ?_⟩
  have hli : (docs.getD i []).length = lens.getD i 0 := by
    rw [← hm, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases docs[i]? with _ | d <;> rfl
  rw [hli, splitDocs_getD h5 i (by rw [hll]; exact hi), hr4, List.drop_drop]

end C3.RV32.Ac
