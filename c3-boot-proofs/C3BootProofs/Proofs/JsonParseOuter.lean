import C3BootProofs.Proofs.JsonParseItem

/-!
# `json::parse`: the value loop

The loop at `0x5C` that reads one value per pass: a string, literal, or
number goes to the closing loop, and `[` or `{` pushes an entry on the
stack. `pa_loop` proves the loop against `parseLoop` for any fuel `k`.
-/

namespace C3.RV32

open C3.Image C3.Json

theorem pd_q : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFDE) 0 = (b.toNat == 34) := by decide

theorem pd_ab : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFFA5) 0 = (b.toNat == 91) := by decide

theorem pd_f : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF9A) 0 = (b.toNat == 102) := by decide

theorem pd_n : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF92) 0 = (b.toNat == 110) := by decide

theorem pd_t : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF8C) 0 = (b.toNat == 116) := by decide

theorem pd_ob : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFF85) 0 = !(b.toNat == 123) := by decide

theorem pd_cb : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF83) 0 = (b.toNat == 125) := by decide

theorem pd_rb : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFA3) 0 = !(b.toNat == 93) := by decide

theorem pd_dig : ∀ b : BitVec 8,
    branchTaken .bgeu (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 10 = !isDigit b.toNat := by decide

theorem pd_flag : ∀ b : BitVec 8, (b.toNat = 91 ∨ b.toNat = 123) →
    (aluEval .sltu (aluEval .add (b.zeroExtend 32) 0xFFFFFF85) 1).extractLsb' 0 8 = flagB (b.toNat == 123) := by
  decide

theorem pd_15 {l : Nat} (hl : l < 2 ^ 32) :
    branchTaken .bltu (15 : Word) (BitVec.ofNat 32 l) = decide (15 < l) := br_bltu (by decide) hl

theorem nbeq_true' {a b : Nat} (h : (!(a == b)) = false) : a = b := by
  cases e : (a == b) with
  | true => exact beq_iff_eq.mp e
  | false => rw [e] at h; cases h

section
variable {M0 Mp : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 f : Fin 32 → Word}

/-- `wsIn` at `0xAC`, after `[` or `{`: the position in `s9` at `0xC0`. -/
theorem pa_wsAC {Q : Post} (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {q : Nat} {M : Word → BitVec 8}
    (hO : Out M0 M s 404) (hR : PRegs f g0 F p n c) (h25 : f 25 = BitVec.ofNat 32 q) (hq : q ≤ n)
    (k : ∀ g : Fin 32 → Word, g 25 = BitVec.ofNat 32 (wsIn c (memBytes M0 p n) q) →
      (∀ x, x ∉ jClob ++ [ra, 25] → g x = f x) → PRegs g g0 F p n c → WP jsonParseCode base Q M 0xC0 g) :
    WP jsonParseCode base Q M 0xAC f := by
  have hn := E.hn
  have hd : memBytes M p n = memBytes M0 p n := hO.bytes E.sP
  have hc1 : ParseCode M base := E.code.out hO E.sep
  refine WP.zero fun hz => ?_
  refine WP.branch pa_at_ac (fun eb => ?_) (fun eb => ?_) <;> wn
  · rw [hR.s3, show f x0 = 0 from hz, br_mode] at eb; subst eb
    exact k _ (by rw [h25]; rfl) (fun _ _ => rfl) hR
  rw [hR.s3, show f x0 = 0 from hz, br_mode] at eb; subst eb
  refine WP.alu pa_at_b0 ?_; wn
  refine WP.alu pa_at_b2 ?_; wn
  refine WP.alu pa_at_b4 ?_; wn
  refine WP.callSkipWs (tb := base + 0xFFFFF372 + 0xFFFFF616 + 0x288) (p := p) (n := n) (q := q)
    pa_at_b6 pa_at_ba (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) _ (by decide)) (by decide)
    hc1.get.ri.sw (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s7)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s8)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h25) (by omega) (by omega) fun m2 h0 => ?_
  refine WP.alu pa_at_be ?_; wn
  exact (fun hg => k _ (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h0, hd]; rfl) hg (hR.keep25 hg))
    (by keepz hz)

/-- `[` or `{` at `0x92`, with the byte `b` read at `pos` and `s1 = b - 123`:
the push, the whitespace after it, and an empty `[]` or `{}` or the first
key. -/
theorem pa_push (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {start k pos : Nat} {w27 : Word}
    {stk : List (Bool × Nat)} {M : Word → BitVec 8} {b : BitVec 8}
    (hnext : PNext M0 Mp base s p out F n c g0 (BitVec.ofNat 32 start) w27 (parseLoop c (memBytes M0 p n) start k))
    (hst : start ≤ n) (hFI : FInv M0 Mp s F n stk M) (hR : PRegs f g0 F p n c) (h18 : f 18 = out)
    (h20 : f 20 = BitVec.ofNat 32 (n + 1)) (h21 : f 21 = 15) (h25 : f 25 = BitVec.ofNat 32 pos) (hpos : pos < n)
    (h8 : f 8 = BitVec.ofNat 32 stk.length) (h26 : f 26 = BitVec.ofNat 32 start) (h27 : f 27 = w27)
    (h9 : f 9 = aluEval .add (b.zeroExtend 32) 0xFFFFFF85) (hbv : (memBytes M0 p n).getD pos 0 = b.toNat)
    (hb : b.toNat = 91 ∨ b.toNat = 123) :
    WP jsonParseCode base (PPost M0 s p out g0 (parseLoop c (memBytes M0 p n) start (k + 1) stk pos)) M 0x92 f := by
  have hfr := hR.fr
  have hn := E.hn
  have hdl : (memBytes M0 p n).length = n := memBytes_length _ _ _
  have hl16 := hFI.2.2.1
  rw [parseLoop.eq_2, hdl, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hbv,
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true hb)]
  refine WP.zero fun hz => ?_
  refine WP.branch pa_at_92 (fun eb => ?_) (fun eb => ?_) <;> wn
  · rw [h21, h8, pd_15 (by omega)] at eb
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by have := of_decide_eq_true eb; omega))]
    exact pa_2cc E hR.sp h18 hFI.1 hFI.2.1 hfr
  rw [h21, h8, pd_15 (by omega)] at eb
  have hl : stk.length < 16 := by have := of_decide_eq_false eb; omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  have hslot : aluEval .add (aluEval .sll (f 8) 3) (aluEval .add (f sp) 0x10) =
      F + BitVec.ofNat 32 (0x10 + 8 * stk.length) := by
    rw [h8, hR.sp]; exact pa_slot F (by omega)
  refine WP.aluImm pa_at_96 ?_; wn
  refine WP.aluImm pa_at_9a ?_; wn
  refine WP.alu pa_at_9c ?_; wn
  refine WP.aluImm pa_at_9e ?_; wn
  refine WP.sw pa_at_a2 (by (try rsimp); rw [hslot, add_lit_zero]; exact E.alF (by omega))
    (by (try rsimp); rw [hslot, add_lit_zero]; exact E.sepF E.sep.parse (by omega)) ?_; wn
  refine WP.sb pa_at_a6 (by (try rsimp); rw [hslot, pc_fa]; exact E.sepF E.sep.parse (by omega)) ?_; wn
  rw [hslot, add_lit_zero, pc_fa, h25, h9, pd_flag b hb]
  have hFI1 := FInv.push E.hF (b.toNat == 123) hFI hl hpos
  generalize memStore8 (memStore32 M (F + BitVec.ofNat 32 (0x10 + 8 * stk.length)) (BitVec.ofNat 32 pos))
    (F + BitVec.ofNat 32 (0x14 + 8 * stk.length)) (flagB (b.toNat == 123)) = M1 at hFI1 ⊢
  refine WP.aluImm pa_at_aa ?_; wn
  refine pa_wsAC E hFI1.1 (by pregs hR, E.z0) (by (try rsimp); rw [h25]; exact pc_inc pos) (by omega)
    fun g h25' hg hRg => ?_
  have hzg : g 0 = 0 := (hg 0 (by decide)).trans (by (try rsimp); try exact hz)
  have g9 : g 9 = aluEval .add (b.zeroExtend 32) 0xFFFFFF85 := (hg 9 (by decide)).trans (by (try rsimp); exact h9)
  have g8 : g 8 = BitVec.ofNat 32 stk.length := (hg 8 (by decide)).trans (by (try rsimp); exact h8)
  have g18 : g 18 = out := (hg 18 (by decide)).trans (by (try rsimp); exact h18)
  have g20 : g 20 = BitVec.ofNat 32 (n + 1) := (hg 20 (by decide)).trans (by (try rsimp); exact h20)
  have g21 : g 21 = 15 := (hg 21 (by decide)).trans (by (try rsimp); exact h21)
  have g26 : g 26 = BitVec.ofNat 32 start := (hg 26 (by decide)).trans (by (try rsimp); exact h26)
  have g27 : g 27 = w27 := (hg 27 (by decide)).trans (by (try rsimp); exact h27)
  have g8' : aluEval .add (g 8) 1 = BitVec.ofNat 32 (stk ++ [(b.toNat == 123, pos)]).length := by
    rw [g8, pc_inc, List.length_append]; rfl
  generalize hw : wsIn c (memBytes M0 p n) (pos + 1) = w at h25' ⊢
  have hwn : w ≤ n := by rw [← hw]; have := wsIn_le c (memBytes M0 p n) (pos + 1); rw [hdl] at this; omega
  refine WP.aluImm pa_at_c0 ?_; wn
  refine WP.alu pa_at_c2 ?_; wn
  refine WP.branch pa_at_c6 (fun eb => ?_) (fun eb => ?_) <;> wn
  · (try rsimp at eb); rw [g9] at eb; (try rw [show g x0 = 0 from hzg] at eb); rw [pd_ob] at eb
    have h91 : b.toNat = 91 := by
      rcases hb with h | h
      · exact h
      · rw [h] at eb; exact absurd eb (by decide)
    rw [ite_eq_left_of_eq_true _ _ (eq_true h91)]
    rw [show (b.toNat == 123) = false by rw [h91]; rfl] at hFI1 g8'
    refine WP.branch pa_at_258 (fun eb2 => ?_) (fun eb2 => ?_) <;> wn
    · (try rsimp at eb2); rw [h25', hRg.s8, br_bgeu (by omega) (by omega)] at eb2
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := not_dec_true eb2; omega))]
      exact hnext M1 _ _ w hFI1 (by pregs hRg, E.z0) (by (try rsimp); exact g18) (by (try rsimp); exact g20)
        (by (try rsimp); exact g21) (by (try rsimp); exact h25') hwn (by (try rsimp); exact g8')
        (by (try rsimp); exact g26) (by (try rsimp); exact g27)
    (try rsimp at eb2); rw [h25', hRg.s8, br_bgeu (by omega) (by omega)] at eb2
    have hwlt : w < n := not_dec_false eb2
    have hbv2 : (memBytes M0 p n).getD w 0 = (M1 (p + BitVec.ofNat 32 w)).toNat := by
      rw [← hFI1.1.bytes E.sP]; exact memBytes_getD hwlt
    rw [show p + BitVec.ofNat 32 w = aluEval .add p (BitVec.ofNat 32 w) from rfl] at hbv2
    refine WP.lbu pa_at_25c ?_; wn
    rw [hRg.s7, h25']
    refine WP.aluImm pa_at_260 ?_; wn
    refine WP.alu pa_at_264 ?_; wn
    refine WP.branch pa_at_266 (fun eb3 => ?_) (fun eb3 => ?_) <;> wn
    · (try rsimp at eb3); (try rw [show g x0 = 0 from hzg] at eb3); rw [pd_rb] at eb3; (try rw [add_lit_zero] at eb3); rw [← hbv2] at eb3
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => by rw [h.2] at eb3; exact absurd eb3 (by decide)))]
      exact hnext M1 _ _ w hFI1 (by pregs hRg, E.z0) (by (try rsimp); exact g18) (by (try rsimp); exact g20)
        (by (try rsimp); exact g21) (by (try rsimp); exact h25') hwn (by (try rsimp); exact g8')
        (by (try rsimp); exact g26) (by (try rsimp); exact g27)
    (try rsimp at eb3); (try rw [show g x0 = 0 from hzg] at eb3); rw [pd_rb] at eb3; (try rw [add_lit_zero] at eb3); rw [← hbv2] at eb3
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hwlt, nbeq_false eb3⟩)]
    refine WP.jal pa_at_26a (by decide) ?_; wn
    exact pa_126 E hnext hst hFI1 (by pregs hRg, E.z0) (by (try rsimp); exact g18) (by (try rsimp); exact h25')
      hwn (by (try rsimp); exact g8') (by (try rsimp); (try simp only [ev0]); (try rw [ev_add] at g8'); exact g8')
      (by (try rsimp); exact g26)
      (by (try rsimp); exact g27)
  (try rsimp at eb); rw [g9] at eb; (try rw [show g x0 = 0 from hzg] at eb); rw [pd_ob] at eb
  have h123 : b.toNat = 123 := nbeq_true' eb
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  rw [show (b.toNat == 123) = true by rw [h123]; rfl] at hFI1 g8'
  refine WP.branch pa_at_ca (fun eb2 => ?_) (fun eb2 => ?_) <;> wn
  · (try rsimp at eb2); rw [h25', hRg.s8, br_bgeu (by omega) (by omega)] at eb2
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := not_dec_true eb2; omega))]
    exact pa_2a0 E hnext hFI1 (by pregs hRg, E.z0) (by (try rsimp); exact g18) (by (try rsimp); exact g20)
      (by (try rsimp); exact g21) (by (try rsimp); exact h25') hwn (by (try rsimp); exact g8')
      (by (try rsimp); exact g26) (by (try rsimp); exact g27)
  (try rsimp at eb2); rw [h25', hRg.s8, br_bgeu (by omega) (by omega)] at eb2
  have hwlt : w < n := not_dec_false eb2
  have hbv2 : (memBytes M0 p n).getD w 0 = (M1 (p + BitVec.ofNat 32 w)).toNat := by
    rw [← hFI1.1.bytes E.sP]; exact memBytes_getD hwlt
  rw [show p + BitVec.ofNat 32 w = aluEval .add p (BitVec.ofNat 32 w) from rfl] at hbv2
  refine WP.lbu pa_at_ce ?_; wn
  rw [hRg.s7, h25']
  refine WP.aluImm pa_at_d2 ?_; wn
  refine WP.branch pa_at_d6 (fun eb3 => ?_) (fun eb3 => ?_) <;> wn
  · (try rsimp at eb3); (try rw [show g x0 = 0 from hzg] at eb3); rw [pd_cb] at eb3; (try rw [add_lit_zero] at eb3); rw [← hbv2] at eb3
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hwlt, beq_iff_eq.mp eb3⟩)]
    refine WP.alu pa_at_124 ?_; wn
    exact pa_126 E hnext hst hFI1 (by pregs hRg, E.z0) (by (try rsimp); exact g18) (by (try rsimp); exact h25')
      hwn (by (try rsimp); exact g8') (by (try rsimp); (try simp only [ev0]); (try rw [ev_add] at g8'); exact g8')
      (by (try rsimp); exact g26) (by (try rsimp); exact g27)
  (try rsimp at eb3); (try rw [show g x0 = 0 from hzg] at eb3); rw [pd_cb] at eb3; (try rw [add_lit_zero] at eb3); rw [← hbv2] at eb3
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => by rw [h.2] at eb3; exact absurd eb3 (by decide)))]
  refine WP.jal pa_at_d8 (by decide) ?_; wn
  exact pa_2a0 E hnext hFI1 (by pregs hRg, E.z0) (by (try rsimp); exact g18) (by (try rsimp); exact g20)
    (by (try rsimp); exact g21) (by (try rsimp); exact h25') hwn (by (try rsimp); exact g8')
    (by (try rsimp); exact g26) (by (try rsimp); exact g27)

/-- The value loop at `0x5C` with fuel `k`: `s11` counts the passes taken. -/
theorem pa_loop (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {start : Nat} (hst : start ≤ n) :
    ∀ k, k ≤ n + 1 → PNext M0 Mp base s p out F n c g0 (BitVec.ofNat 32 start) (BitVec.ofNat 32 (n + 1 - k))
      (parseLoop c (memBytes M0 p n) start k) := by
  have hn := E.hn
  have hdl : (memBytes M0 p n).length = n := memBytes_length _ _ _
  intro k
  induction k with
  | zero =>
    intro _ M g stk pos hFI hR h18 h20 h21 h25 hpos h8 h26 h27
    refine WP.zero fun hz => ?_
    refine WP.branch pa_at_5c (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact pa_2cc E hR.sp h18 hFI.1 hFI.2.1 hR.fr
    · exfalso; rw [h27, h20, Nat.sub_zero, br_beq (by omega) (by omega)] at eb
      exact absurd (of_decide_eq_false eb) (by omega)
  | succ k ih =>
    intro hk M g stk pos hFI hR h18 h20 h21 h25 hpos h8 h26 h27
    have hnext := ih (by omega)
    have hfr := hR.fr
    have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
    have hw27 : aluEval .add (BitVec.ofNat 32 (n + 1 - (k + 1))) 1 = BitVec.ofNat 32 (n + 1 - k) := by
      rw [pc_inc, show n + 1 - (k + 1) + 1 = n + 1 - k by omega]
    refine WP.zero fun hz => ?_
    refine WP.branch pa_at_5c (fun eb => ?_) (fun eb => ?_) <;> wn
    · exfalso; rw [h27, h20, br_beq (by omega) (by omega)] at eb
      exact absurd (of_decide_eq_true eb) (by omega)
    refine WP.branch pa_at_60 (fun eb => ?_) (fun eb => ?_) <;> wn
    · rw [h25, hR.s8, br_bgeu (by omega) (by omega)] at eb
      rw [parseLoop.eq_2, hdl, ite_eq_left_of_eq_true _ _ (eq_true (by have := not_dec_true eb; omega))]
      exact pa_2cc E hR.sp h18 hFI.1 hFI.2.1 hfr
    rw [h25, hR.s8, br_bgeu (by omega) (by omega)] at eb
    have hplt : pos < n := not_dec_false eb
    have hbv : (memBytes M0 p n).getD pos 0 = (M (p + BitVec.ofNat 32 pos)).toNat := by
      rw [← hFI.1.bytes E.sP]; exact memBytes_getD hplt
    refine WP.alu pa_at_64 ?_; wn
    refine WP.lbu pa_at_68 ?_; wn
    rw [hR.s7, h25, ev_add, add_lit_zero]
    generalize M (p + BitVec.ofNat 32 pos) = b at hbv
    refine WP.aluImm pa_at_6c ?_; wn
    refine WP.aluImm pa_at_70 ?_; wn
    refine WP.branch pa_at_72 (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_q] at eb
      rw [parseLoop.eq_2, hdl, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hbv,
        ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mp eb))]
      exact pa_str E hnext hst hFI (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h25) (Nat.le_of_lt hplt) (by (try rsimp); exact h8) (by (try rsimp); exact h26) (by (try rsimp); rw [h27]; exact hw27)
    (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_q] at eb
    have hq : b.toNat ≠ 34 := nbeq_true (by rw [eb]; rfl)
    refine WP.aluImm pa_at_74 ?_; wn
    refine WP.aluImm pa_at_78 ?_; wn
    refine WP.branch pa_at_7c (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_ab] at eb
      exact pa_push E hnext hst hFI (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h20) (by (try rsimp); exact h21) (by (try rsimp); exact h25) hplt (by (try rsimp); exact h8) (by (try rsimp); exact h26) (by (try rsimp); rw [h27]; exact hw27) (by (try rsimp); try rfl) hbv (Or.inl (beq_iff_eq.mp eb))
    (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_ab] at eb
    have hab : b.toNat ≠ 91 := nbeq_true (by rw [eb]; rfl)
    refine WP.aluImm pa_at_7e ?_; wn
    refine WP.branch pa_at_82 (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_f] at eb
      have hb := beq_iff_eq.mp eb
      rw [parseLoop.eq_2, hdl, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hbv, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (Or.inl hb))]
      exact pa_lit E hnext hst hFI (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h25) (Nat.le_of_lt hplt) (by (try rsimp); exact h8) (by (try rsimp); exact h26) (by (try rsimp); rw [h27]; exact hw27)
    (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_f] at eb
    have hf : b.toNat ≠ 102 := nbeq_true (by rw [eb]; rfl)
    refine WP.aluImm pa_at_84 ?_; wn
    refine WP.branch pa_at_88 (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_n] at eb
      have hb := beq_iff_eq.mp eb
      rw [parseLoop.eq_2, hdl, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hbv, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inl hb)))]
      exact pa_lit E hnext hst hFI (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h25) (Nat.le_of_lt hplt) (by (try rsimp); exact h8) (by (try rsimp); exact h26) (by (try rsimp); rw [h27]; exact hw27)
    (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_n] at eb
    have hnn : b.toNat ≠ 110 := nbeq_true (by rw [eb]; rfl)
    refine WP.aluImm pa_at_8a ?_; wn
    refine WP.branch pa_at_8e (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_t] at eb
      have hb := beq_iff_eq.mp eb
      rw [parseLoop.eq_2, hdl, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hbv, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (Or.inr (Or.inr hb)))]
      exact pa_lit E hnext hst hFI (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h25) (Nat.le_of_lt hplt) (by (try rsimp); exact h8) (by (try rsimp); exact h26) (by (try rsimp); rw [h27]; exact hw27)
    (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_t] at eb
    have ht : b.toNat ≠ 116 := nbeq_true (by rw [eb]; rfl)
    refine WP.branch pa_at_90 (fun eb => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_ob] at eb
      exact pa_push E hnext hst hFI (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h20) (by (try rsimp); exact h21) (by (try rsimp); exact h25) hplt (by (try rsimp); exact h8) (by (try rsimp); exact h26) (by (try rsimp); rw [h27]; exact hw27) (by (try rsimp); try rfl) hbv (Or.inr (nbeq_true' eb))
    (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); rw [pd_ob] at eb
    have hob : b.toNat ≠ 123 := nbeq_true eb
    refine WP.aluImm pa_at_ec ?_; wn
    refine WP.aluImm pa_at_f0 ?_; wn
    refine WP.branch pa_at_f2 (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); (try simp only [ev0] at eb); rw [pd_dig] at eb
      have hdg : isDigit b.toNat = false := by revert eb; cases isDigit b.toNat <;> decide
      rw [parseLoop.eq_2, hdl, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hbv, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by rw [hdg]; decide))]
      exact pa_2cc E (by (try rsimp); exact hR.sp) (by (try rsimp); exact h18) hFI.1 hFI.2.1 (by keepz E.z0)
    (try rsimp at eb); (try rw [show g x0 = 0 from hz] at eb); (try simp only [ev0] at eb); rw [pd_dig] at eb
    have hdg : isDigit b.toNat = true := by revert eb; cases isDigit b.toNat <;> decide
    rw [parseLoop.eq_2, hdl, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hbv, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true hdg)]
    exact pa_num E hnext hst hFI (by pregs hR, E.z0) (by (try rsimp); exact h18) (by (try rsimp); exact h25) (Nat.le_of_lt hplt) (by (try rsimp); exact h8) (by (try rsimp); exact h26) (by (try rsimp); rw [h27]; exact hw27)

end

end C3.RV32
