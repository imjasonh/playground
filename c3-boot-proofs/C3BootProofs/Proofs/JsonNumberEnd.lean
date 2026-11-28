import C3BootProofs.Proofs.JsonWp
import C3BootProofs.Proofs.JsonModel

/-!
# `json::number_end`, as compiled

`number_end(doc, pos)` stores `Ok` of the position after the number at
`pos`, or `Err(Json)`, at `out`. It is a leaf with no frame.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem nen_at_0 : fetchRel jsonNumberEndCode 0x0 = some (.branch .bltu a2 a3 0x58, 4) := by decide
theorem nen_at_4 : fetchRel jsonNumberEndCode 0x4 = some (.aluImm .add a5 x0 0x0, 2) := by decide
theorem nen_at_6 : fetchRel jsonNumberEndCode 0x6 = some (.alu .add a6 a1 a3, 4) := by decide
theorem nen_at_a : fetchRel jsonNumberEndCode 0xA = some (.alu .sub (5 : Fin 32) a2 a3, 4) := by decide
theorem nen_at_e : fetchRel jsonNumberEndCode 0xE = some (.aluImm .add (17 : Fin 32) x0 0x9, 2) := by decide
theorem nen_at_10 : fetchRel jsonNumberEndCode 0x10 = some (.alu .add a4 x0 a6, 2) := by decide
theorem nen_at_12 : fetchRel jsonNumberEndCode 0x12 = some (.branch .beq (5 : Fin 32) x0 0x18, 4) := by decide
theorem nen_at_16 : fetchRel jsonNumberEndCode 0x16 = some (.load .lbu a1 a4 0x0, 4) := by decide
theorem nen_at_1a : fetchRel jsonNumberEndCode 0x1A = some (.aluImm .add a1 a1 0xFFFFFFD0, 4) := by decide
theorem nen_at_1e : fetchRel jsonNumberEndCode 0x1E = some (.branch .bltu (17 : Fin 32) a1 0x12, 4) := by decide
theorem nen_at_22 : fetchRel jsonNumberEndCode 0x22 = some (.aluImm .add a4 a4 0x1, 2) := by decide
theorem nen_at_24 : fetchRel jsonNumberEndCode 0x24 = some (.aluImm .add a5 a5 0x1, 2) := by decide
theorem nen_at_26 : fetchRel jsonNumberEndCode 0x26 = some (.branch .bne (5 : Fin 32) a5 0xFFFFFFF0, 4) := by decide
theorem nen_at_2a : fetchRel jsonNumberEndCode 0x2A = some (.branch .bltu a3 a2 0xC, 4) := by decide
theorem nen_at_2e : fetchRel jsonNumberEndCode 0x2E = some (.jal x0 0x1A, 2) := by decide
theorem nen_at_30 : fetchRel jsonNumberEndCode 0x30 = some (.alu .add (5 : Fin 32) x0 a5, 2) := by decide
theorem nen_at_32 : fetchRel jsonNumberEndCode 0x32 = some (.branch .bgeu a3 a2 0x16, 4) := by decide
theorem nen_at_36 : fetchRel jsonNumberEndCode 0x36 = some (.load .lbu a1 a6 0x0, 4) := by decide
theorem nen_at_3a : fetchRel jsonNumberEndCode 0x3A = some (.aluImm .add a1 a1 0xFFFFFFD0, 4) := by decide
theorem nen_at_3e : fetchRel jsonNumberEndCode 0x3E = some (.branch .bne a1 x0 0xA, 2) := by decide
theorem nen_at_40 : fetchRel jsonNumberEndCode 0x40 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem nen_at_42 : fetchRel jsonNumberEndCode 0x42 = some (.branch .beq (5 : Fin 32) a1 0x10, 4) := by decide
theorem nen_at_46 : fetchRel jsonNumberEndCode 0x46 = some (.jal x0 0x12, 2) := by decide
theorem nen_at_48 : fetchRel jsonNumberEndCode 0x48 = some (.aluImm .add a1 (5 : Fin 32) 0xFFFFFFEC, 4) := by decide
theorem nen_at_4c : fetchRel jsonNumberEndCode 0x4C = some (.aluImm .add a2 x0 0xFFFFFFED, 2) := by decide
theorem nen_at_4e : fetchRel jsonNumberEndCode 0x4E = some (.branch .bltu a1 a2 0xA, 4) := by decide
theorem nen_at_52 : fetchRel jsonNumberEndCode 0x52 = some (.alu .add a3 a3 (5 : Fin 32), 2) := by decide
theorem nen_at_54 : fetchRel jsonNumberEndCode 0x54 = some (.branch .bgeu a3 (5 : Fin 32) 0x14, 4) := by decide
theorem nen_at_58 : fetchRel jsonNumberEndCode 0x58 = some (.aluImm .add a1 x0 0x20, 4) := by decide
theorem nen_at_5c : fetchRel jsonNumberEndCode 0x5C = some (.store .sb a0 a1 0x1, 4) := by decide
theorem nen_at_60 : fetchRel jsonNumberEndCode 0x60 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem nen_at_62 : fetchRel jsonNumberEndCode 0x62 = some (.store .sb a0 a1 0x0, 4) := by decide
theorem nen_at_66 : fetchRel jsonNumberEndCode 0x66 = some (.jalr x0 ra 0x0, 2) := by decide
theorem nen_at_68 : fetchRel jsonNumberEndCode 0x68 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem nen_at_6a : fetchRel jsonNumberEndCode 0x6A = some (.store .sw a0 a3 0x4, 2) := by decide
theorem nen_at_6c : fetchRel jsonNumberEndCode 0x6C = some (.jal x0 0xFFFFFFF6, 2) := by decide

theorem nen_dig : ∀ b : BitVec 8,
    branchTaken .bltu 9 (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) = !isDigit b.toNat := by decide

theorem nen_zero : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 0 = !(b.toNat == 48) := by decide

theorem nen_range_small : ∀ k, k < 20 →
    branchTaken .bltu (aluEval .add (BitVec.ofNat 32 k) 0xFFFFFFEC) (aluEval .add 0 0xFFFFFFED) = decide (k = 0) := by decide

theorem nen_range_big {k : Nat} (h : 19 < k) (hk : k < 2 ^ 32) :
    branchTaken .bltu (aluEval .add (BitVec.ofNat 32 k) 0xFFFFFFEC) (aluEval .add 0 0xFFFFFFED) = true := by
  have e : aluEval .add (BitVec.ofNat 32 k) 0xFFFFFFEC = BitVec.ofNat 32 (k - 20) := by
    apply BitVec.eq_of_toNat_eq
    rw [ev_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    show (k % 4294967296 + 4294967276) % 4294967296 = (k - 20) % 4294967296
    omega
  rw [e, show aluEval .add 0 (0xFFFFFFED : Word) = BitVec.ofNat 32 4294967277 from rfl, br_bltu (by omega) (by omega)]
  exact decide_eq_true (by omega)

/-- The registers `number_end` may change. -/
abbrev neClob : List (Fin 32) := [a1, a2, a3, a4, a5, a6, t0, a7]

section
variable {M : Word → BitVec 8} {base ret out : Word} {f g0 : Fin 32 → Word}

theorem nen_err (h0 : f a0 = out) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret)
    (hsep : Sep out 8 base jsonNumberEndCode.length) (hfr : ∀ x, x ∉ neClob → f x = g0 x) :
    WP jsonNumberEndCode base (ResPost neClob ret M out none g0) M 0x58 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm nen_at_58 ?_; wn
  refine WP.sb nen_at_5c (by rsimp; rw [h0]; exact hsep.shift (c := 1) (by decide)) ?_; wn
  refine WP.aluImm nen_at_60 ?_; wn
  refine WP.sb nen_at_62 (by rsimp; rw [h0]; exact hsep.shift (c := 0) (by decide)) ?_; wn
  refine WP.ret nen_at_66 ⟨?_, ?_, ?_⟩
  · rsimp; rw [hra, add_lit_zero, hret]
  · rw [h0, hz, add_lit_zero]; exact usizeRes_err M out
  · keep hz

theorem nen_ok {pos k : Nat} (h0 : f a0 = out) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret)
    (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonNumberEndCode.length)
    (hfr : ∀ x, x ∉ neClob → f x = g0 x) (h3 : f a3 = BitVec.ofNat 32 pos) (ht0 : f t0 = BitVec.ofNat 32 k)
    (hlt : pos + k < 2 ^ 32) :
    WP jsonNumberEndCode base (ResPost neClob ret M out (some (pos + k)) g0) M 0x52 f := by
  refine WP.zero fun hz => ?_
  have hv : aluEval .add (f a3) (f 5) = BitVec.ofNat 32 (pos + k) := by
    rw [h3, ht0, ev_add, ofNat_add_ofNat]
  refine WP.alu nen_at_52 ?_; wn
  refine WP.branch nen_at_54 (fun _ => ?_) (fun e => ?_) <;> wn
  · refine WP.aluImm nen_at_68 ?_; wn
    refine WP.sw nen_at_6a (by rsimp; rw [h0]; exact aligned_add hal (k := 4) (by decide))
      (by rsimp; rw [h0]; exact hsep.sub (c := 4) (by decide)) ?_; wn
    refine WP.jal nen_at_6c (by decide) ?_; wn
    refine WP.sb nen_at_62 (by rsimp; rw [h0]; exact hsep.shift (c := 0) (by decide)) ?_; wn
    refine WP.ret nen_at_66 ⟨?_, ?_, ?_⟩
    · rsimp; rw [hra, add_lit_zero, hret]
    · rw [h0, add_lit_zero, hv]; exact usizeRes_ok M out _
    · keep hz
  · rsimp at e
    rw [hv, ht0, br_bgeu (by omega) (by omega)] at e
    exact absurd (not_dec_false e) (by omega)

theorem nen_48 {pos k : Nat} {r : Option Nat} (h0 : f a0 = out) (hra : f ra = ret)
    (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonNumberEndCode.length)
    (hfr : ∀ x, x ∉ neClob → f x = g0 x) (h3 : f a3 = BitVec.ofNat 32 pos) (ht0 : f t0 = BitVec.ofNat 32 k)
    (hlt : pos + k < 2 ^ 32) (hr : r = if k = 0 then none else if 19 < k then none else some (pos + k)) :
    WP jsonNumberEndCode base (ResPost neClob ret M out r g0) M 0x48 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm nen_at_48 ?_; wn
  refine WP.aluImm nen_at_4c ?_; wn
  refine WP.branch nen_at_4e (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [ht0] at e
    have hr' : r = none := by
      rw [hr]
      by_cases h20 : k < 20
      · rw [nen_range_small k h20] at e
        simp only [of_decide_eq_true e, ↓reduceIte]
      · simp only [show ¬k = 0 by omega, show 19 < k by omega, ↓reduceIte]
    rw [hr']
    exact nen_err (by rsimp; exact h0) (by rsimp; exact hra) hret hsep (by keep hz)
  · rsimp at e
    rw [ht0] at e
    have h20 : k < 20 := by
      refine Nat.lt_of_not_le fun h => ?_
      rw [nen_range_big (by omega) (by omega)] at e
      cases e
    rw [nen_range_small k h20] at e
    have hk0 := of_decide_eq_false e
    have hr' : r = some (pos + k) := by
      rw [hr]; simp only [hk0, show ¬19 < k by omega, ↓reduceIte]
    rw [hr']
    exact nen_ok (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz) (by rsimp; exact h3)
      (by rsimp; exact ht0) hlt

theorem nen_36 {p : Word} {n pos k : Nat} (h0 : f a0 = out) (hra : f ra = ret)
    (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonNumberEndCode.length)
    (hfr : ∀ x, x ∉ neClob → f x = g0 x) (h3 : f a3 = BitVec.ofNat 32 pos)
    (h6 : f a6 = p + BitVec.ofNat 32 pos) (ht0 : f t0 = BitVec.ofNat 32 k)
    (hk : k = digLen ((memBytes M p n).drop pos)) (hlt : pos < n) (hn : n < 2 ^ 32) :
    WP jsonNumberEndCode base (ResPost neClob ret M out (numberEnd (memBytes M p n) pos) g0) M 0x36 f := by
  refine WP.zero fun hz => ?_
  have hd : (memBytes M p n).drop pos =
      (M (p + BitVec.ofNat 32 pos)).toNat :: memBytes M (p + BitVec.ofNat 32 pos + 1) (n - (pos + 1)) := by
    rw [jmemBytes_drop, show n - pos = (n - (pos + 1)) + 1 by omega, memBytes_succ]
  have hlen : ¬(memBytes M p n).length < pos := by rw [memBytes_length]; omega
  have hkle : k ≤ n - pos := by
    have := digLen_le ((memBytes M p n).drop pos)
    rw [List.length_drop, memBytes_length] at this; omega
  rw [numberEnd_cons hlen hd, ← hd, ← hk]
  refine WP.lbu nen_at_36 ?_; wn
  refine WP.aluImm nen_at_3a ?_; wn
  rw [h6, add_lit_zero]
  refine WP.branch nen_at_3e (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [nen_zero, Bool.not_eq_true', beq_eq_false_iff_ne] at e
    simp only [e, ↓reduceIte]
    exact nen_48 (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz) (by rsimp; exact h3)
      (by rsimp; exact ht0) (by omega) rfl
  · rsimp at e
    rw [nen_zero, Bool.not_eq_false', beq_iff_eq] at e
    have hk1 : 1 ≤ k := by
      rw [hk, hd]; simp only [digLen, e, show isDigit 48 = true from rfl, ↓reduceIte]; omega
    simp only [e, ↓reduceIte, show ¬k = 0 by omega]
    refine WP.aluImm nen_at_40 ?_; wn
    refine WP.branch nen_at_42 (fun e2 => ?_) (fun e2 => ?_) <;> wn
    · rsimp at e2
      rw [ht0, show aluEval .add (0 : Word) 1 = BitVec.ofNat 32 1 from rfl, br_beq (by omega) (by decide)] at e2
      have := of_decide_eq_true e2
      simp only [this, show ¬19 < 1 by decide, ↓reduceIte]
      exact nen_ok (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz)
        (by rsimp; exact h3) (by rsimp; rw [ht0, this]) (by omega)
    · rsimp at e2
      rw [ht0, show aluEval .add (0 : Word) 1 = BitVec.ofNat 32 1 from rfl, br_beq (by omega) (by decide)] at e2
      have := of_decide_eq_false e2
      have hr : (if 19 < k then none else if k = 1 then some (pos + 1) else none) = none := by
        by_cases h : 19 < k
        · simp only [h, ↓reduceIte]
        · simp only [h, this, ↓reduceIte]
      rw [hr]
      refine WP.jal nen_at_46 (by decide) ?_; wn
      exact nen_err (by rsimp; exact h0) (by rsimp; exact hra) hret hsep (by keep hz)

theorem nen_2a {p : Word} {n pos k : Nat} (h0 : f a0 = out) (hra : f ra = ret)
    (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonNumberEndCode.length)
    (hfr : ∀ x, x ∉ neClob → f x = g0 x) (h2 : f a2 = BitVec.ofNat 32 n) (h3 : f a3 = BitVec.ofNat 32 pos)
    (h6 : f a6 = p + BitVec.ofNat 32 pos) (ht0 : f t0 = BitVec.ofNat 32 k)
    (hk : k = digLen ((memBytes M p n).drop pos)) (hle : pos ≤ n) (hn : n < 2 ^ 32) :
    WP jsonNumberEndCode base (ResPost neClob ret M out (numberEnd (memBytes M p n) pos) g0) M 0x2A f := by
  refine WP.zero fun hz => ?_
  refine WP.branch nen_at_2a (fun e => ?_) (fun e => ?_) <;> wn
  · rw [h3, h2, br_bltu (by omega) hn] at e
    exact nen_36 h0 hra hret hal hsep hfr h3 h6 ht0 hk (of_decide_eq_true e) hn
  · rw [h3, h2, br_bltu (by omega) hn] at e
    have hpn : pos = n := by have := of_decide_eq_false e; omega
    have hd : (memBytes M p n).drop pos = [] := List.drop_eq_nil_of_le (by rw [memBytes_length]; omega)
    rw [hd] at hk
    rw [numberEnd_nil hd]
    refine WP.jal nen_at_2e (by decide) ?_; wn
    exact nen_48 (k := k) h0 hra hret hal hsep hfr h3 ht0 (by rw [hk, digLen]; omega)
      (by rw [hk]; rfl)
theorem nen_30 {p : Word} {n pos k : Nat} (h0 : f a0 = out) (hra : f ra = ret)
    (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonNumberEndCode.length)
    (hfr : ∀ x, x ∉ neClob → f x = g0 x) (h2 : f a2 = BitVec.ofNat 32 n) (h3 : f a3 = BitVec.ofNat 32 pos)
    (h6 : f a6 = p + BitVec.ofNat 32 pos) (h5 : f a5 = BitVec.ofNat 32 k)
    (hk : k = digLen ((memBytes M p n).drop pos)) (hlt : pos < n) (hn : n < 2 ^ 32) :
    WP jsonNumberEndCode base (ResPost neClob ret M out (numberEnd (memBytes M p n) pos) g0) M 0x30 f := by
  refine WP.zero fun hz => ?_
  refine WP.alu nen_at_30 ?_; wn
  refine WP.branch nen_at_32 (fun e => ?_) (fun _ => ?_) <;> wn
  · rsimp at e
    rw [h3, h2, br_bgeu (by omega) hn] at e
    exact absurd hlt (not_dec_true e)
  · exact nen_36 (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz) (by rsimp; exact h3)
      (by rsimp; exact h6) (by rsimp; rw [hz, h5, ev_add, zw]) hk hlt hn

theorem nen_loop {Q : Post} {F : Fin 32 → Word} {R : Nat} (hR : R < 2 ^ 32) :
    ∀ (j i : Nat) (f : Fin 32 → Word) (q : Word), i + j = R → 0 < j → f a4 = q →
      f a5 = BitVec.ofNat 32 i → f t0 = BitVec.ofNat 32 R → f a7 = 9 →
      (∀ x, x ∉ ([a1, a4, a5] : List (Fin 32)) → f x = F x) →
      (∀ g : Fin 32 → Word, g a5 = BitVec.ofNat 32 (i + digLen (memBytes M q j)) →
        (∀ x, x ∉ ([a1, a4, a5] : List (Fin 32)) → g x = F x) → WP jsonNumberEndCode base Q M 0x30 g) →
      (∀ g : Fin 32 → Word, g t0 = BitVec.ofNat 32 (i + digLen (memBytes M q j)) →
        (∀ x, x ∉ ([a1, a4, a5] : List (Fin 32)) → g x = F x) → WP jsonNumberEndCode base Q M 0x2A g) →
      WP jsonNumberEndCode base Q M 0x16 f
  | 0, _, _, _, _, hj, _, _, _, _, _, _, _ => absurd hj (Nat.lt_irrefl 0)
  | j + 1, i, f, q, hij, _, h4, h5, ht0, h7, hfr, K30, K2a => by
    refine WP.zero fun hz => ?_
    refine WP.lbu nen_at_16 ?_; wn
    refine WP.aluImm nen_at_1a ?_; wn
    rw [h4, add_lit_zero]
    rw [memBytes_succ] at K30 K2a
    refine WP.branch nen_at_1e (fun e => ?_) (fun e => ?_) <;> wn
    · rsimp at e
      rw [h7, nen_dig, Bool.not_eq_true'] at e
      refine K30 _ ?_ (by keep hz)
      rsimp; rw [h5]; simp only [digLen, e, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rsimp at e
    rw [h7, nen_dig, Bool.not_eq_false'] at e
    have hd : ∀ l, digLen ((M q).toNat :: l) = digLen l + 1 := fun l => by
      simp only [digLen, e, ↓reduceIte]
    refine WP.aluImm nen_at_22 ?_; wn
    refine WP.aluImm nen_at_24 ?_; wn
    have hi1 : aluEval .add (BitVec.ofNat 32 i) 1 = BitVec.ofNat 32 (i + 1) := cl_succ i
    refine WP.branch nen_at_26 (fun e2 => ?_) (fun e2 => ?_) <;> wn
    · rsimp at e2
      rw [ht0, h5, hi1, br_bne (by omega) (by omega)] at e2
      have hj : j ≠ 0 := fun hj0 => not_dec_true e2 (by omega)
      refine nen_loop hR j (i + 1) _ (q + 1) (by omega) (by omega) (by rsimp; rw [h4]; rfl)
        (by rsimp; rw [h5]; exact hi1) (by rsimp; exact ht0) (by rsimp; exact h7) (by keep hz)
        (fun g hg hfg => K30 g ?_ hfg) (fun g hg hfg => K2a g ?_ hfg)
      · rw [hg, hd, Nat.add_assoc, Nat.add_comm 1]
      · rw [hg, hd, Nat.add_assoc, Nat.add_comm 1]
    · rsimp at e2
      rw [ht0, h5, hi1, br_bne (by omega) (by omega)] at e2
      have hj : j = 0 := by have := not_dec_false e2; omega
      subst hj
      refine K2a _ ?_ (by keep hz)
      rsimp; rw [ht0, hd, memBytes_zero, digLen]; congr 1; omega

theorem nen_wp {p : Word} {n pos : Nat} (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n) (h3 : f a3 = BitVec.ofNat 32 pos)
    (hra : f ra = ret) (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0)
    (hsep : Sep out 8 base jsonNumberEndCode.length) :
    WP jsonNumberEndCode base (ResPost neClob ret M out (numberEnd (memBytes M p n) pos) f) M 0 f := by
  refine WP.zero fun hz => ?_
  refine WP.branch nen_at_0 (fun e => ?_) (fun e => ?_) <;> wn
  · rw [h2, h3, br_bltu hn hpos] at e
    have hlen : (memBytes M p n).length < pos := by rw [memBytes_length]; exact of_decide_eq_true e
    simp only [numberEnd, hlen, ↓reduceIte]
    exact nen_err h0 hra hret hsep fun _ _ => rfl
  rw [h2, h3, br_bltu hn hpos] at e
  have hle : pos ≤ n := Nat.le_of_not_lt (of_decide_eq_false e)
  have hs : aluEval .sub (BitVec.ofNat 32 n) (BitVec.ofNat 32 pos) = BitVec.ofNat 32 (n - pos) :=
    sub_ofNat_le hle hn
  have hd : (memBytes M p n).drop pos = memBytes M (p + BitVec.ofNat 32 pos) (n - pos) :=
    jmemBytes_drop M pos p n
  refine WP.aluImm nen_at_4 ?_; wn
  refine WP.alu nen_at_6 ?_; wn
  refine WP.alu nen_at_a ?_; wn
  refine WP.aluImm nen_at_e ?_; wn
  refine WP.alu nen_at_10 ?_; wn
  refine WP.branch nen_at_12 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h2, h3, hs, br_beq0 (by omega)] at e
    have h0p : n - pos = 0 := of_decide_eq_true e
    refine nen_2a (k := 0) (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz)
      (by rsimp; exact h2) (by rsimp; exact h3) (by rsimp; rw [h1, h3]; rfl) (by rsimp; rw [h2, h3, hs, h0p])
      (by rw [hd, h0p, memBytes_zero]; rfl) hle hn
  rsimp at e
  rw [h2, h3, hs, br_beq0 (by omega)] at e
  have h0p : n - pos ≠ 0 := of_decide_eq_false e
  refine nen_loop (by omega : n - pos < 2 ^ 32) (n - pos) 0 _ (p + BitVec.ofNat 32 pos) (by omega)
    (by omega) (by rsimp; simp only [ev_add, zw, h1, h3]) (by rsimp; rw [hz]; rfl) (by rsimp; rw [h2, h3, hs])
    (by rsimp) (fun _ _ => rfl) (fun g hg hfg => ?_) (fun g hg hfg => ?_)
  · exact nen_30 (by rw [hfg a0 (by decide)]; rsimp; exact h0) (by rw [hfg ra (by decide)]; rsimp; exact hra)
      hret hal hsep (frame_trans (by decide) hfg (by keep hz)) (by rw [hfg a2 (by decide)]; rsimp; exact h2)
      (by rw [hfg a3 (by decide)]; rsimp; exact h3)
      (by rw [hfg a6 (by decide)]; rsimp; simp only [ev_add, h1, h3]) hg (by rw [hd, Nat.zero_add])
      (by omega) hn
  · exact nen_2a (by rw [hfg a0 (by decide)]; rsimp; exact h0) (by rw [hfg ra (by decide)]; rsimp; exact hra)
      hret hal hsep (frame_trans (by decide) hfg (by keep hz)) (by rw [hfg a2 (by decide)]; rsimp; exact h2)
      (by rw [hfg a3 (by decide)]; rsimp; exact h3)
      (by rw [hfg a6 (by decide)]; rsimp; simp only [ev_add, h1, h3]) hg (by rw [hd, Nat.zero_add]) hle hn

/-- `number_end(doc, pos)` with `doc` the `n` bytes at `p` and `pos` in
`a3`: stores `numberEnd` of them at `out` as a `Result<usize, TufError>`,
changes no other memory, and keeps every register outside `neClob`. -/
theorem jsonNumberEnd_correct (m : Machine) {base retAddr out p : Word} {n pos : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonNumberEndCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (ha3 : reg m a3 = BitVec.ofNat 32 pos) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonNumberEndCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ UsizeRes m.mem m'.mem out (numberEnd (memBytes m.mem p n) pos) ∧
      ∀ r, r ∉ neClob → reg m' r = reg m r :=
  WP.run (nen_wp hn hpos ha0 ha1 ha2 ha3 hra hret hal hsep) hb hc hpc

end

end C3.RV32
