import C3BootProofs.Proofs.ParseSpec
import C3BootProofs.Spec.Tuf

/-!
# `boot_main`'s first closure: the TUF part's header and index

The index stage reads the TUF part's 8-byte header and its index of
lengths from flash. `acx_decode` says what `decodeTufParts` makes of the
part's bytes when the header and the index pass the checks that the
compiled code makes, and the documents end where the part does.
-/

namespace C3.RV32.Ac

open C3

/-- The little-endian word at `k` in `bs`. -/
abbrev acxW (bs : Bytes) (k : Nat) : Nat :=
  le32 (bs.getD k 0) (bs.getD (k + 1) 0) (bs.getD (k + 2) 0) (bs.getD (k + 3) 0)

/-- The `n` little-endian words from `k` in `bs`. -/
def acxLens (bs : Bytes) : Nat → Nat → List Nat
  | _, 0 => []
  | k, n + 1 => acxW bs k :: acxLens bs (k + 4) n

theorem acx_dropc {bs : Bytes} {k : Nat} (h : k < bs.length) :
    bs.drop k = bs.getD k 0 :: bs.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons h]
  congr 1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem acx_u16 {bs : Bytes} {k : Nat} (h : k + 2 ≤ bs.length) :
    readU16 (bs.drop k) = some (bs.getD k 0 + 256 * bs.getD (k + 1) 0, bs.drop (k + 2)) := by
  rw [acx_dropc (by omega), acx_dropc (k := k + 1) (by omega)]; rfl

theorem acx_u32 {bs : Bytes} {k : Nat} (h : k + 4 ≤ bs.length) :
    readU32 (bs.drop k) = some (acxW bs k, bs.drop (k + 4)) := by
  rw [acx_dropc (by omega), acx_dropc (k := k + 1) (by omega), acx_dropc (k := k + 2) (by omega),
    acx_dropc (k := k + 3) (by omega)]; rfl

theorem acx_expect {bs : Bytes} (h : 4 ≤ bs.length) (h0 : bs.getD 0 0 = 0x43) (h1 : bs.getD 1 0 = 0x33)
    (h2 : bs.getD 2 0 = 0x54) (h3 : bs.getD 3 0 = 0x55) :
    readExpect (ascii!"C3TU") bs = some (bs.drop 4) := by
  have e : bs.drop 0 = bs.getD 0 0 :: bs.getD 1 0 :: bs.getD 2 0 :: bs.getD 3 0 :: bs.drop 4 := by
    rw [acx_dropc (k := 0) (by omega), acx_dropc (k := 1) (by omega), acx_dropc (k := 2) (by omega),
      acx_dropc (k := 3) (by omega)]
  rw [List.drop_zero] at e
  rw [e, h0, h1, h2, h3]
  rfl

theorem acx_lens_length (bs : Bytes) : ∀ (k n : Nat), (acxLens bs k n).length = n
  | _, 0 => rfl
  | k, n + 1 => by rw [acxLens, List.length_cons, acx_lens_length bs (k + 4) n]

theorem acx_lens_getD (bs : Bytes) : ∀ (k n j : Nat), j < n → (acxLens bs k n).getD j 0 = acxW bs (k + 4 * j)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | k, n + 1, 0, _ => rfl
  | k, n + 1, j + 1, h => by
    rw [acxLens, List.getD_cons_succ, acx_lens_getD bs (k + 4) n j (by omega),
      show k + 4 + 4 * j = k + 4 * (j + 1) by omega]

theorem acx_lens_sum (bs : Bytes) {c : Nat} : ∀ (k n : Nat), (∀ j, j < n → acxW bs (k + 4 * j) ≤ c) →
    (acxLens bs k n).sum ≤ n * c
  | _, 0, _ => by simp [acxLens]
  | k, n + 1, h => by
    have h0 := h 0 (by omega)
    have ih := acx_lens_sum bs (k + 4) n fun j hj => by
      have := h (j + 1) (by omega); rwa [show k + 4 * (j + 1) = k + 4 + 4 * j by omega] at this
    rw [acxLens, List.sum_cons, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_zero] at h0
    omega

theorem acx_rl (bs : Bytes) : ∀ (n k : Nat), k + 4 * n ≤ bs.length →
    (∀ j, j < n → 1 ≤ acxW bs (k + 4 * j) ∧ acxW bs (k + 4 * j) ≤ maxDocLen) →
    readLengths n (bs.drop k) = some (acxLens bs k n, bs.drop (k + 4 * n))
  | 0, k, _, _ => by simp [readLengths, acxLens]
  | n + 1, k, h, hw => by
    obtain ⟨w1, w2⟩ := hw 0 (by omega)
    rw [Nat.mul_zero, Nat.add_zero] at w1 w2
    have ih := acx_rl bs n (k + 4) (by omega) fun j hj => by
      have := hw (j + 1) (by omega); rwa [show k + 4 * (j + 1) = k + 4 + 4 * j by omega] at this
    rw [show k + 4 * (n + 1) = k + 4 + 4 * n by omega]
    simp only [readLengths, acx_u32 (show k + 4 ≤ bs.length by omega), acxLens]
    simp [require, w1, w2]
    rw [ih]; rfl

theorem acx_sd : ∀ (lens : List Nat) (bs : Bytes), lens.sum ≤ bs.length →
    ∃ docs, splitDocs lens bs = some (docs, bs.drop lens.sum) ∧ docs.length = lens.length ∧
      ∀ i, i < lens.length → docs.getD i [] = (bs.drop (lens.take i).sum).take (lens.getD i 0)
  | [], bs, _ => ⟨[], by simp [splitDocs], rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | l :: ls, bs, h => by
    rw [List.sum_cons] at h
    have hl : l ≤ bs.length := by omega
    obtain ⟨docs, hd, hlen, hget⟩ := acx_sd ls (bs.drop l) (by rw [List.length_drop]; omega)
    refine ⟨bs.take l :: docs, ?_, by rw [List.length_cons, List.length_cons, hlen], fun i hi => ?_⟩
    · simp [splitDocs, require, hl, hd, List.drop_drop, List.sum_cons]
    · cases i with
      | zero => simp
      | succ i =>
        rw [List.length_cons] at hi
        rw [List.getD_cons_succ, hget i (by omega), List.take_succ_cons, List.sum_cons, List.getD_cons_succ,
          List.drop_drop]

theorem acx_rev2 {α : Type} (docs : List α) {count : Nat} (hdl : docs.length = count + 2) :
    ∃ tr tg rs, docs.reverse = tr :: tg :: rs := by
  have h2 : docs.reverse.length = count + 2 := by rw [List.length_reverse, hdl]
  revert h2
  cases docs.reverse with
  | nil => intro h; exact absurd h (Nat.succ_ne_zero _).symm
  | cons tr t => cases t with
    | nil => intro h; exact absurd (Nat.succ.inj h).symm (Nat.succ_ne_zero _)
    | cons tg rs => intro _; exact ⟨tr, tg, rs, rfl⟩

/-- **What `decodeTufParts` makes of a part** whose header has the magic,
version 2, and `count` roots, whose `count + 2` lengths are each from 1 to
`maxDocLen`, and whose documents end where the part does. -/
theorem acx_decode {bs : Bytes} {count : Nat} (hL : bs.length ≤ maxTufLen)
    (h0 : bs.getD 0 0 = 0x43) (h1 : bs.getD 1 0 = 0x33) (h2 : bs.getD 2 0 = 0x54) (h3 : bs.getD 3 0 = 0x55)
    (hv : bs.getD 4 0 + 256 * bs.getD 5 0 = 2) (hc : bs.getD 6 0 + 256 * bs.getD 7 0 = count)
    (hc64 : count ≤ maxRoots)
    (hw : ∀ j, j < count + 2 → 1 ≤ acxW bs (8 + 4 * j) ∧ acxW bs (8 + 4 * j) ≤ maxDocLen)
    (hend : 8 + 4 * (count + 2) + (acxLens bs 8 (count + 2)).sum = bs.length) :
    ∃ parts, decodeTufParts bs = some parts ∧ parts.roots.length = count ∧
      ∀ i, i < count + 2 → (parts.roots ++ [parts.targets, parts.trustedRoot]).getD i [] =
        (bs.drop (8 + 4 * (count + 2) + ((acxLens bs 8 (count + 2)).take i).sum)).take
          ((acxLens bs 8 (count + 2)).getD i 0) := by
  have hlen : 8 ≤ bs.length := by omega
  obtain ⟨docs, hd, hdl, hget⟩ := acx_sd (acxLens bs 8 (count + 2)) (bs.drop (8 + 4 * (count + 2)))
    (by rw [List.length_drop]; omega)
  rw [acx_lens_length] at hdl
  have hrest : (bs.drop (8 + 4 * (count + 2))).drop (acxLens bs 8 (count + 2)).sum = [] := by
    rw [List.drop_drop]; exact List.drop_eq_nil_of_le (by omega)
  have hrev := acx_rev2 docs (count := count) hdl
  obtain ⟨tr, tg, rs, hr⟩ := hrev
  have hdocs : docs = rs.reverse ++ [tg, tr] := by
    rw [← List.reverse_reverse docs, hr]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
  refine ⟨⟨rs.reverse, tg, tr⟩, ?_, ?_, fun i hi => ?_⟩
  · have e4 := acx_u16 (bs := bs) (k := 4) (Nat.le_trans (by decide) hlen)
    have e6 := acx_u16 (bs := bs) (k := 6) hlen
    rw [hv] at e4
    rw [hc] at e6
    have e8 := acx_rl bs (count + 2) 8 (hend ▸ Nat.le_add_right _ _) hw
    have hexp := acx_expect (Nat.le_trans (by decide) hlen) h0 h1 h2 h3
    have hLd : decide (bs.length ≤ maxTufLen) = true := decide_eq_true hL
    have hcd : decide (count ≤ maxRoots) = true := decide_eq_true hc64
    unfold decodeTufParts
    simp only [require, hLd, hexp, e4, e6, e8, hd, hrest, hcd, Option.bind_eq_bind, Option.bind_some]
    rw [hr]; rfl
  · show rs.reverse.length = count
    have := congrArg List.length hdocs
    rw [List.length_append, List.length_reverse] at this
    rw [List.length_reverse]; simp only [List.length_cons, List.length_nil] at this; omega
  · rw [← hdocs, hget i (by rw [acx_lens_length]; exact hi), List.drop_drop, Nat.add_comm]

end C3.RV32.Ac
