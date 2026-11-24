import C3BootProofs.Proofs.JsonWp
import C3BootProofs.Proofs.JsonModel

/-!
# `json::skip_ws`, as compiled

`skip_ws(bytes, pos)` returns the position after the whitespace at `pos`:
`pos` itself when `pos` is at or past the end. It is a leaf with no frame
and writes no memory.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem skw_at_0 : fetchRel jsonSkipWsCode 0x0 = some (.branch .bgeu a1 a2 0x8, 4) := by decide
theorem skw_at_4 : fetchRel jsonSkipWsCode 0x4 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem skw_at_6 : fetchRel jsonSkipWsCode 0x6 = some (.jal x0 0x6, 2) := by decide
theorem skw_at_8 : fetchRel jsonSkipWsCode 0x8 = some (.alu .add a3 a0 a2, 4) := by decide
theorem skw_at_c : fetchRel jsonSkipWsCode 0xC = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem skw_at_e : fetchRel jsonSkipWsCode 0xE = some (.alu .sub a4 a1 a2, 4) := by decide
theorem skw_at_12 : fetchRel jsonSkipWsCode 0x12 = some (.alu .sltu a1 a1 a4, 4) := by decide
theorem skw_at_16 : fetchRel jsonSkipWsCode 0x16 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem skw_at_18 : fetchRel jsonSkipWsCode 0x18 = some (.lui a5 0x800000, 4) := by decide
theorem skw_at_1c : fetchRel jsonSkipWsCode 0x1C = some (.alu .and a1 a1 a4, 2) := by decide
theorem skw_at_1e : fetchRel jsonSkipWsCode 0x1E = some (.aluImm .add a6 x0 0x17, 2) := by decide
theorem skw_at_20 : fetchRel jsonSkipWsCode 0x20 = some (.aluImm .add a5 a5 0x13, 2) := by decide
theorem skw_at_22 : fetchRel jsonSkipWsCode 0x22 = some (.branch .beq a1 x0 0x1C, 2) := by decide
theorem skw_at_24 : fetchRel jsonSkipWsCode 0x24 = some (.load .lbu a4 a3 0x0, 4) := by decide
theorem skw_at_28 : fetchRel jsonSkipWsCode 0x28 = some (.aluImm .add a4 a4 0xFFFFFFF7, 2) := by decide
theorem skw_at_2a : fetchRel jsonSkipWsCode 0x2A = some (.branch .bltu a6 a4 0x16, 4) := by decide
theorem skw_at_2e : fetchRel jsonSkipWsCode 0x2E = some (.alu .srl a4 a5 a4, 4) := by decide
theorem skw_at_32 : fetchRel jsonSkipWsCode 0x32 = some (.aluImm .and a4 a4 0x1, 2) := by decide
theorem skw_at_34 : fetchRel jsonSkipWsCode 0x34 = some (.branch .beq a4 x0 0xC, 2) := by decide
theorem skw_at_36 : fetchRel jsonSkipWsCode 0x36 = some (.aluImm .add a3 a3 0x1, 2) := by decide
theorem skw_at_38 : fetchRel jsonSkipWsCode 0x38 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem skw_at_3a : fetchRel jsonSkipWsCode 0x3A = some (.branch .bne a1 a0 0xFFFFFFEA, 4) := by decide
theorem skw_at_3e : fetchRel jsonSkipWsCode 0x3E = some (.alu .add a0 x0 a1, 2) := by decide
theorem skw_at_40 : fetchRel jsonSkipWsCode 0x40 = some (.alu .add a0 a0 a2, 2) := by decide
theorem skw_at_42 : fetchRel jsonSkipWsCode 0x42 = some (.alu .sltu a1 a0 a2, 4) := by decide
theorem skw_at_46 : fetchRel jsonSkipWsCode 0x46 = some (.alu .sub a1 x0 a1, 4) := by decide
theorem skw_at_4a : fetchRel jsonSkipWsCode 0x4A = some (.alu .or a0 a0 a1, 2) := by decide
theorem skw_at_4c : fetchRel jsonSkipWsCode 0x4C = some (.jalr x0 ra 0x0, 2) := by decide

theorem skw_far : ∀ b : BitVec 8,
    branchTaken .bltu 0x17 (aluEval .add (b.zeroExtend 32) 0xFFFFFFF7) = true → isWs b.toNat = false := by
  decide

theorem skw_bit : ∀ b : BitVec 8,
    branchTaken .bltu 0x17 (aluEval .add (b.zeroExtend 32) 0xFFFFFFF7) = false →
    branchTaken .beq (aluEval .and (aluEval .srl 0x800013 (aluEval .add (b.zeroExtend 32) 0xFFFFFFF7)) 1) 0 =
      !isWs b.toNat := by
  decide

/-- `skip_ws` returned `V` to `ret` with memory `M0`, and kept every
register but the scratch ones. -/
def skwPost (ret : Word) (M0 : Word → BitVec 8) (V : Nat) (g0 : Fin 32 → Word) : Post :=
  fun pc M g => pc = ret ∧ M = M0 ∧ g a0 = BitVec.ofNat 32 V ∧
    ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → g r = g0 r

theorem skw_tail {M : Word → BitVec 8} {base ret : Word} {g0 f : Fin 32 → Word} {x pos V : Nat}
    (hV : pos + x = V) (hV32 : V < 2 ^ 32) (h0 : f a0 = BitVec.ofNat 32 x) (h2 : f a2 = BitVec.ofNat 32 pos)
    (hra : f ra = ret) (hret : ret &&& ~~~1 = ret)
    (hfr : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → f r = g0 r) :
    WP jsonSkipWsCode base (skwPost ret M V g0) M 0x40 f := by
  refine WP.zero fun hz => ?_
  refine WP.alu skw_at_40 ?_; wn
  refine WP.alu skw_at_42 ?_; wn
  refine WP.alu skw_at_46 ?_; wn
  refine WP.alu skw_at_4a ?_; wn
  refine WP.ret skw_at_4c ?_
  have hv : aluEval .add (f a0) (f a2) = BitVec.ofNat 32 V := by
    rw [h0, h2, ev_add, ofNat_add_ofNat, Nat.add_comm, hV]
  have hs : aluEval .sltu (BitVec.ofNat 32 V) (BitVec.ofNat 32 pos) = 0 := by
    have : ¬ V < pos := by omega
    simp only [aluEval, BitVec.ult, ofNat_tn hV32, ofNat_tn (show pos < 2 ^ 32 by omega), this,
      decide_false, Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, rfl, ?_, ?_⟩
  · rsimp; rw [hra, add_lit_zero, hret]
  · rsimp; rw [hv, h2, hs]
    show BitVec.ofNat 32 V ||| (0 - 0) = _
    rw [BitVec.sub_self, BitVec.or_zero]
  · intro r h0' h1' h3' h4' h5' h6'
    rsimp
    by_cases hr0 : r.val = 0
    · have : r = 0 := Fin.ext hr0
      subst this
      rw [← hfr 0 h0' h1' h3' h4' h5' h6']
      rsimp
      exact hz.symm
    · simp only [hr0, h0', h1', ↓reduceIte]
      exact hfr r h0' h1' h3' h4' h5' h6'

theorem skw_loop {M : Word → BitVec 8} {Q : Post} {base : Word} {R : Nat} (hR : R < 2 ^ 32) :
    ∀ (j k : Nat) (f : Fin 32 → Word) (q : Word), k + j = R → 0 < j →
      f a0 = BitVec.ofNat 32 k → f a1 = BitVec.ofNat 32 R → f a3 = q → f a5 = 0x800013 → f a6 = 0x17 →
      (∀ g : Fin 32 → Word, g a0 = BitVec.ofNat 32 (k + wsLen (memBytes M q j)) →
        (∀ r, r ≠ a0 → r ≠ a3 → r ≠ a4 → g r = f r) → WP jsonSkipWsCode base Q M 0x40 g) →
      WP jsonSkipWsCode base Q M 0x24 f
  | 0, _, _, _, _, hj, _, _, _, _, _, _ => absurd hj (Nat.lt_irrefl 0)
  | j + 1, k, f, q, hkj, _, h0, h1, h3, h5, h6, K => by
    refine WP.zero fun hz => ?_
    refine WP.lbu skw_at_24 ?_; wn
    refine WP.aluImm skw_at_28 ?_; wn
    rw [h3, add_lit_zero]
    refine WP.branch skw_at_2a (fun e => ?_) (fun e => ?_) <;> wn
    · rsimp at e
      rw [h6] at e
      refine K _ ?_ ?_
      · rsimp; rw [memBytes_succ, wsLen_cons_not (skw_far _ e), h0, Nat.add_zero]
      · intro r h0' h3' h4'; simp only [upd_app, h0', h3', h4', ↓reduceIte, ite_val_zero hz]
    · rsimp at e
      rw [h6] at e
      refine WP.alu skw_at_2e ?_; wn
      refine WP.aluImm skw_at_32 ?_; wn
      refine WP.branch skw_at_34 (fun e2 => ?_) (fun e2 => ?_) <;> wn
      · rsimp at e2
        rw [h5, skw_bit _ e, Bool.not_eq_true'] at e2
        refine K _ ?_ ?_
        · rsimp; rw [memBytes_succ, wsLen_cons_not e2, h0, Nat.add_zero]
        · intro r h0' h3' h4'; simp only [upd_app, h0', h3', h4', ↓reduceIte, ite_val_zero hz]
      · rsimp at e2
        rw [h5, skw_bit _ e, Bool.not_eq_false'] at e2
        refine WP.aluImm skw_at_36 ?_; wn
        refine WP.aluImm skw_at_38 ?_; wn
        have hk1 : aluEval .add (BitVec.ofNat 32 k) 1 = BitVec.ofNat 32 (k + 1) := cl_succ k
        refine WP.branch skw_at_3a (fun e3 => ?_) (fun e3 => ?_) <;> wn
        · rsimp at e3
          rw [h1, h0, hk1, br_bne hR (by omega)] at e3
          rw [Bool.not_eq_true'] at e3
          have hj : j ≠ 0 := fun hj => of_decide_eq_false e3 (by omega)
          refine skw_loop hR j (k + 1) _ (q + 1) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
          · rsimp; rw [h0, hk1]
          · rsimp; exact h1
          · rsimp; rw [h3]; rfl
          · rsimp; exact h5
          · rsimp; exact h6
          · intro g hg hfr
            refine K g ?_ fun r h0' h3' h4' => ?_
            · rw [hg, memBytes_succ, wsLen_cons_ws e2, Nat.add_assoc, Nat.add_comm 1]
            · rw [hfr r h0' h3' h4']; simp only [upd_app, h0', h3', h4', ↓reduceIte, ite_val_zero hz]
        · rsimp at e3
          rw [h1, h0, hk1, br_bne hR (by omega)] at e3
          rw [Bool.not_eq_false'] at e3
          have hj : j = 0 := by have := of_decide_eq_true e3; omega
          subst hj
          refine WP.alu skw_at_3e ?_; wn
          have hw : k + wsLen (memBytes M q (0 + 1)) = R := by
            rw [memBytes_succ, memBytes_zero, wsLen_cons_ws e2, wsLen_nil]; omega
          refine K _ ?_ fun r h0' h3' h4' => ?_
          · rw [hw]; rsimp; rw [h1, ev_add, zw]
          · simp only [upd_app, h0', h3', h4', ↓reduceIte, ite_val_zero hz]

theorem skw_len_le {n pos : Nat} (h : pos ≤ n) (hn : n < 2 ^ 32) :
    aluEval .and (aluEval .add (aluEval .sltu (BitVec.ofNat 32 n) (aluEval .sub (BitVec.ofNat 32 n)
      (BitVec.ofNat 32 pos))) 0xFFFFFFFF) (aluEval .sub (BitVec.ofNat 32 n) (BitVec.ofNat 32 pos)) =
      BitVec.ofNat 32 (n - pos) := by
  have hs : aluEval .sub (BitVec.ofNat 32 n) (BitVec.ofNat 32 pos) = BitVec.ofNat 32 (n - pos) :=
    sub_ofNat_le h hn
  have hlt : ¬ n < n - pos := by omega
  have hl : aluEval .sltu (BitVec.ofNat 32 n) (BitVec.ofNat 32 (n - pos)) = 0 := by
    simp only [aluEval, BitVec.ult, ofNat_tn hn, ofNat_tn (show n - pos < 2 ^ 32 by omega), hlt,
      decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [hs, hl]
  show (0 + 0xFFFFFFFF) &&& BitVec.ofNat 32 (n - pos) = _
  rw [zw, ones_and]

theorem skw_len_gt {n pos : Nat} (h : n < pos) (hpos : pos < 2 ^ 32) :
    aluEval .and (aluEval .add (aluEval .sltu (BitVec.ofNat 32 n) (aluEval .sub (BitVec.ofNat 32 n)
      (BitVec.ofNat 32 pos))) 0xFFFFFFFF) (aluEval .sub (BitVec.ofNat 32 n) (BitVec.ofNat 32 pos)) = 0 := by
  have hs := sub_ofNat_gt h hpos
  have hlt : n < 2 ^ 32 - (pos - n) := by omega
  have hl : aluEval .sltu (BitVec.ofNat 32 n) (BitVec.ofNat 32 n - BitVec.ofNat 32 pos) = 1 := by
    simp only [aluEval, BitVec.ult, ofNat_tn (show n < 2 ^ 32 by omega), hs, hlt, decide_true, ↓reduceIte]
  show (aluEval .sltu (BitVec.ofNat 32 n) (BitVec.ofNat 32 n - BitVec.ofNat 32 pos) + 0xFFFFFFFF) &&& _ = _
  rw [hl]
  exact BitVec.zero_and

theorem skw_mid {M : Word → BitVec 8} {base ret p : Word} {f g0 : Fin 32 → Word} {n pos : Nat}
    (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32) (h1 : f a1 = BitVec.ofNat 32 n)
    (h2 : f a2 = BitVec.ofNat 32 pos) (h3 : pos ≤ n → f a3 = p + BitVec.ofNat 32 pos) (hra : f ra = ret)
    (hret : ret &&& ~~~1 = ret)
    (hfr : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → f r = g0 r) :
    WP jsonSkipWsCode base (skwPost ret M (skipWs (memBytes M p n) pos) g0) M 0xC f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm skw_at_c ?_; wn
  refine WP.alu skw_at_e ?_; wn
  refine WP.alu skw_at_12 ?_; wn
  refine WP.aluImm skw_at_16 ?_; wn
  refine WP.lui skw_at_18 ?_; wn
  refine WP.alu skw_at_1c ?_; wn
  refine WP.aluImm skw_at_1e ?_; wn
  refine WP.aluImm skw_at_20 ?_; wn
  rw [h1, h2, hz]
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  refine WP.branch skw_at_22 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    have hle : n ≤ pos := by
      by_cases h : pos ≤ n
      · rw [skw_len_le h hn, br_beq0 (by omega)] at e
        have := of_decide_eq_true e
        omega
      · omega
    have hv : aluEval .and (aluEval .add (aluEval .sltu (BitVec.ofNat 32 n) (aluEval .sub (BitVec.ofNat 32 n)
        (BitVec.ofNat 32 pos))) 0xFFFFFFFF) (aluEval .sub (BitVec.ofNat 32 n) (BitVec.ofNat 32 pos)) =
        BitVec.ofNat 32 0 := by
      by_cases h : pos ≤ n
      · rw [skw_len_le h hn, show n - pos = 0 by omega]
      · exact skw_len_gt (by omega) hpos
    refine WP.alu skw_at_3e ?_; wn
    refine skw_tail (x := 0) (pos := pos) ?_ (by rw [skipWs, List.drop_eq_nil_of_le (by omega), wsLen_nil]; omega) ?_ ?_ ?_ hret fun r h0' h1' h3' h4' h5' h6' => ?_
    · rw [skipWs, List.drop_eq_nil_of_le (by omega), wsLen_nil]
    · rsimp; rw [hv, ev_add, zw]
    · rsimp; exact h2
    · rsimp; exact hra
    · simp only [upd_app, h0', h1', h3', h4', h5', h6', ↓reduceIte, ite_val_zero hz]
      exact hfr r h0' h1' h3' h4' h5' h6'
  · rsimp at e
    have hle : pos ≤ n := by
      by_cases h : pos ≤ n
      · exact h
      · rw [skw_len_gt (by omega) hpos] at e; exact absurd e (by decide)
    rw [skw_len_le hle hn, br_beq0 (by omega)] at e
    have hR : n - pos ≠ 0 := of_decide_eq_false e
    refine skw_loop (R := n - pos) (by omega) (n - pos) 0 _ (p + BitVec.ofNat 32 pos) (by omega) (by omega)
      ?_ ?_ ?_ ?_ ?_ fun g hg hfg => ?_
    · rsimp
    · rsimp; exact skw_len_le hle hn
    · rsimp; exact h3 hle
    · rsimp
    · rsimp
    · have hd : (memBytes M p n).drop pos = memBytes M (p + BitVec.ofNat 32 pos) (n - pos) :=
        memBytes_drop M pos p n
      have hw := wsLen_le (memBytes M (p + BitVec.ofNat 32 pos) (n - pos))
      rw [memBytes_length] at hw
      refine skw_tail (pos := pos) (x := wsLen (memBytes M (p + BitVec.ofNat 32 pos) (n - pos))) ?_ (by
        rw [skipWs, hd]; omega) ?_ ?_ ?_ hret fun r h0' h1' h3' h4' h5' h6' => ?_
      · rw [skipWs, hd]
      · rw [hg, Nat.zero_add]
      · rw [hfg a2 (by decide) (by decide) (by decide)]; rsimp; exact h2
      · rw [hfg ra (by decide) (by decide) (by decide)]; rsimp; exact hra
      · rw [hfg r h0' h3' h4']
        simp only [upd_app, h0', h1', h3', h4', h5', h6', ↓reduceIte, ite_val_zero hz]
        exact hfr r h0' h1' h3' h4' h5' h6'

theorem skw_wp {M : Word → BitVec 8} {base ret p : Word} {f : Fin 32 → Word} {n pos : Nat}
    (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32) (h0 : f a0 = p) (h1 : f a1 = BitVec.ofNat 32 n)
    (h2 : f a2 = BitVec.ofNat 32 pos) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret) :
    WP jsonSkipWsCode base (skwPost ret M (skipWs (memBytes M p n) pos) f) M 0 f := by
  refine WP.zero fun hz => ?_
  refine WP.branch skw_at_0 (fun e => ?_) (fun e => ?_) <;> wn
  · rw [h1, h2, br_bgeu hn hpos, Bool.not_eq_true', decide_eq_false_iff_not] at e
    refine WP.alu skw_at_8 ?_; wn
    exact skw_mid hn hpos (by rsimp; exact h1) (by rsimp; exact h2) (fun _ => by rsimp; rw [h0, h2]; rfl)
      (by rsimp; exact hra) hret fun r h0' h1' h3' h4' h5' h6' => by
        simp only [upd_app, h3', ↓reduceIte, ite_val_zero hz]
  · rw [h1, h2, br_bgeu hn hpos, Bool.not_eq_false', decide_eq_true_iff] at e
    refine WP.aluImm skw_at_4 ?_; wn
    refine WP.jal skw_at_6 (by decide) ?_; wn
    exact skw_mid hn hpos (by rsimp; exact h1) (by rsimp; exact h2) (fun h => absurd e (by omega))
      (by rsimp; exact hra) hret fun r h0' h1' h3' h4' h5' h6' => by
        simp only [upd_app, h3', ↓reduceIte, ite_val_zero hz]

/-- `skip_ws(bytes, pos)` with `bytes` the `n` bytes at `p`: returns
`skipWs` of them at `pos`, writes no memory, and keeps every register
but `a0`, `a1`, and `a3` through `a6`. -/
theorem jsonSkipWs_correct (m : Machine) {base retAddr p : Word} {n pos : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonSkipWsCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = p) (ha1 : reg m a1 = BitVec.ofNat 32 n) (ha2 : reg m a2 = BitVec.ofNat 32 pos)
    (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = m.mem ∧
      reg m' a0 = BitVec.ofNat 32 (skipWs (memBytes m.mem p n) pos) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg m' r = reg m r :=
  WP.run (skw_wp hn hpos ha0 ha1 ha2 hra hret) hb hc hpc

end C3.RV32
