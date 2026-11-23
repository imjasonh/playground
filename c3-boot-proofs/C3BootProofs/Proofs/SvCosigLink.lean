import C3BootProofs.Proofs.SvCosigLoop
import C3BootProofs.Proofs.SvExtListLink

/-!
# The checkpoint's signature lines the code read, as `checkpointSigs`

The code's loop over the signature lines (`sv_cosigStep`): each pass splits
off a line, checks its em dash and space, checks that the text after the
space is canonical base64 a group at a time, and, for a line from the log's
origin, decodes it and keeps the signature whose key hint matches.
-/

namespace C3.RV32.Sv

open C3.Image

theorem splitSpace_cons_ne {b : Nat} {rest : Bytes} (hb : b ≠ 0x20) :
    splitSpace (b :: rest) = (do let (l, r) ← splitSpace rest; pure (b :: l, r)) := by
  rcases b with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | b
  all_goals first | exact absurd rfl hb | rfl

/-- The code's search for the first space as `splitSpace`. -/
theorem splitSpace_search {M : Word → BitVec 8} : ∀ {p : Word} {k n : Nat}, k < n →
    (∀ i, i < k → M (p + BitVec.ofNat 32 i) ≠ 0x20) → M (p + BitVec.ofNat 32 k) = 0x20 →
    splitSpace (memBytes M p n) = some (memBytes M p k, memBytes M (p + BitVec.ofNat 32 (k + 1)) (n - (k + 1)))
  | p, 0, n, hk, _, hs => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [add_ofNat_zero] at hs
    rw [memBytes_succ, hs, show (0x20 : BitVec 8).toNat = 0x20 from rfl, ← add_ofNat_zero p, add_ofNat_assoc,
      add_ofNat_zero, show n' + 1 - (0 + 1) = n' by omega]
    rfl
  | p, k + 1, n, hk, hne, hs => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h0 := hne 0 (by omega)
    rw [add_ofNat_zero] at h0
    have hb : (M p).toNat ≠ 0x20 := fun e => h0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    have hp1 : p + 1 = p + BitVec.ofNat 32 1 := rfl
    rw [memBytes_succ, splitSpace_cons_ne hb, hp1,
      splitSpace_search (p := p + BitVec.ofNat 32 1) (k := k) (n := n') (by omega)
        (fun i hi => by rw [add_ofNat_assoc, Nat.add_comm 1 i]; exact hne (i + 1) (by omega))
        (by rw [add_ofNat_assoc, Nat.add_comm 1 k]; exact hs)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [memBytes_succ M p k, hp1, add_ofNat_assoc, show 1 + (k + 1) = k + 1 + 1 by omega,
      show n' - (k + 1) = n' + 1 - (k + 1 + 1) by omega]
    rfl

theorem readExpect_prefix {M : Word → BitVec 8} {p : Word} {n : Nat} {pre : Bytes} (hl : pre.length ≤ n)
    (h : memBytes M p pre.length = pre) :
    readExpect pre (memBytes M p n) = some (memBytes M (p + BitVec.ofNat 32 pre.length) (n - pre.length)) := by
  unfold readExpect
  rw [memBytes_take M p hl, h, beq_iff_eq.mpr rfl, memBytes_length]
  simp only [Bool.true_and, decide_eq_true hl, ↓reduceIte]
  rw [memBytes_dropK' M p hl]

theorem byte_eq {a b : Nat} (ha : a < 256) (hb : b < 256) (h : BitVec.ofNat 8 a = BitVec.ofNat 8 b) : a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem app4_inj {a b c d e f g h : BitVec 8} (H : a ++ b ++ c ++ d = e ++ f ++ g ++ h) :
    a = e ∧ b = f ∧ c = g ∧ d = h := by
  have h1 := congrArg (fun x => x.extractLsb' 0 8) H
  have h2 := congrArg (fun x => x.extractLsb' 8 24) H
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h1 h2
  have h3 := congrArg (fun x => x.extractLsb' 0 8) h2
  have h4 := congrArg (fun x => x.extractLsb' 8 16) h2
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h3 h4
  have h5 := congrArg (fun x => x.extractLsb' 0 8) h4
  have h6 := congrArg (fun x => x.extractLsb' 8 8) h4
  simp only [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left] at h5 h6
  exact ⟨h6, h5, h3, h1⟩

theorem sha256_lt (msg : Bytes) : ∀ b ∈ sha256 msg, b < 256 := by
  intro b hb
  unfold sha256 at hb
  obtain ⟨w, -, hw⟩ := List.mem_flatMap.mp hb
  have := w.isLt
  simp only [Sha256.wordBytes, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact Nat.div_lt_of_lt_mul (by omega)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)

theorem bind_some_lt {α : Type} {x : Option α} {f : α → Option Bytes} {g : Bytes} (h : x.bind f = some g)
    (hf : ∀ a, f a = some g → ∀ b ∈ g, b < 256) : ∀ b ∈ g, b < 256 := by
  cases x with
  | none => cases h
  | some a => exact hf a h

theorem b64Group_lt {c0 c1 c2 c3 pad : Nat} {g : Bytes} (h : b64Group c0 c1 c2 c3 pad = some g) : ∀ b ∈ g, b < 256 := by
  unfold b64Group at h
  simp only [Option.bind_eq_bind] at h
  refine bind_some_lt h fun _ h => bind_some_lt h fun _ h => ?_
  have fin : ∀ (bits : Nat) (u : Option Unit), (u.bind fun _ => pure (List.take (3 - pad)
      [bits / 2 ^ 16 % 256, bits / 2 ^ 8 % 256, bits % 256])) = some g → ∀ b ∈ g, b < 256 := by
    intro bits u hu
    refine bind_some_lt hu fun _ hu => ?_
    rw [Option.pure_def] at hu
    have hu := Option.some.inj hu
    subst hu
    intro b hb
    have := List.mem_of_mem_take hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl <;> exact Nat.mod_lt _ (by decide)
  split at h <;> refine bind_some_lt h fun _ h => ?_ <;> split at h <;> refine bind_some_lt h fun _ h => ?_ <;>
    exact fin _ _ h

theorem base64Decode_lt : ∀ {x bs : Bytes}, base64Decode x = some bs → ∀ b ∈ bs, b < 256
  | [], bs, h => by
    rw [base64Decode.eq_1] at h
    cases h; intro b hb; cases hb
  | [c0, c1, c2, c3], bs, h => by
    rw [base64Decode.eq_2] at h
    exact b64Group_lt h
  | c0 :: c1 :: c2 :: c3 :: hd :: tl, bs, h => by
    rw [base64Decode.eq_3] at h
    cases hg : b64Group c0 c1 c2 c3 0 with
    | none => rw [hg] at h; cases h
    | some g =>
      cases hr : base64Decode (hd :: tl) with
      | none => rw [hg, hr] at h; cases h
      | some r =>
        rw [hg, hr] at h
        cases h
        intro b hb
        rcases List.mem_append.mp hb with h1 | h1
        · exact b64Group_lt hg b h1
        · exact base64Decode_lt hr b h1
  | [a], _, h => by
    rw [base64Decode.eq_4 [a] (by intro e; cases e) (by intro _ _ _ _ e; cases e) (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h
  | [a, b], _, h => by
    rw [base64Decode.eq_4 [a, b] (by intro e; cases e) (by intro _ _ _ _ e; cases e) (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h
  | [a, b, c], _, h => by
    rw [base64Decode.eq_4 [a, b, c] (by intro e; cases e) (by intro _ _ _ _ e; cases e) (by intro _ _ _ _ _ _ e; cases e)] at h
    cases h

theorem le4_take {l l' : Bytes} (hl : 4 ≤ l.length) (hl' : 4 ≤ l'.length) (hb : ∀ x ∈ l, x < 256)
    (hb' : ∀ x ∈ l', x < 256) (h : le4 l 0 = le4 l' 0) : l.take 4 = l'.take 4 := by
  unfold le4 at h
  obtain ⟨e3, e2, e1, e0⟩ := app4_inj h
  match l, l', hl, hl' with
  | a0 :: a1 :: a2 :: a3 :: _, b0 :: b1 :: b2 :: b3 :: _, _, _ =>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3
    simp only [List.take_succ_cons, List.take_zero]
    rw [byte_eq (hb _ (by simp)) (hb' _ (by simp)) e0, byte_eq (hb _ (by simp)) (hb' _ (by simp)) e1,
      byte_eq (hb _ (by simp)) (hb' _ (by simp)) e2, byte_eq (hb _ (by simp)) (hb' _ (by simp)) e3]

theorem sub4_toNat {n : Nat} (h4 : 4 ≤ n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n + BitVec.ofNat 32 0xFFFFFFFC).toNat = n - 4 := by
  rw [BitVec.toNat_add, ofNat_toNat_lt hn, ofNat_toNat_lt (by decide)]; omega

theorem zero_add_mul1 (k : Nat) : BitVec.ofNat 32 0x0 + BitVec.ofNat 32 (k * 1) = BitVec.ofNat 32 k := by
  rw [Nat.mul_one, BitVec.zero_add]

theorem add_succ_ofNat (p : Word) (k : Nat) : p + (BitVec.ofNat 32 k + BitVec.ofNat 32 0x1) = p + BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add_ofNat]

theorem enc_len {n k : Nat} (h4 : 4 ≤ n) (hn : n < 2 ^ 32) (hk : k + 1 ≤ n - 4) :
    ((BitVec.ofNat 32 n + BitVec.ofNat 32 0xFFFFFFFC) - (BitVec.ofNat 32 k + BitVec.ofNat 32 0x1)).toNat = n - 4 - (k + 1) := by
  rw [show BitVec.ofNat 32 k + BitVec.ofNat 32 0x1 = BitVec.ofNat 32 (k + 1) from BitVec.ofNat_add_ofNat .., BitVec.toNat_sub,
    sub4_toNat h4 hn, ofNat_toNat_lt (k := k + 1) (by omega)]; omega

theorem and3_shr2 {x : Word} (h : x &&& BitVec.ofNat 32 0x3 = 0) : x.toNat = 4 * (x >>> 2).toNat := by
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, ofNat_toNat_lt (by decide), show (0 : Word).toNat = 0 from rfl,
    show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at h1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem le4_take4 (l : Bytes) : le4 l 0 = le4 (l.take 4) 0 := by
  unfold le4
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  rfl

end C3.RV32.Sv
