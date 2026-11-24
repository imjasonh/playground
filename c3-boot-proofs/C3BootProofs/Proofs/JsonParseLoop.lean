import C3BootProofs.Proofs.JsonParseClose

/-!
# `json::parse`: the closing loop

After each value, `parse` runs its closing loop at `0x12C`: it skips
whitespace, then reads a `]`, a `}`, or a comma for the innermost open array
or object, or ends the document when none is open. `pa_close` proves that
loop against `closeLoop`.
-/

namespace C3.RV32

open C3.Image C3.Json

theorem pc_fl : ∀ ob : Bool, branchTaken .beq ((flagB ob).zeroExtend 32) 0 = !ob := by decide

theorem pc_fl' : ∀ ob : Bool, branchTaken .bne ((flagB ob).zeroExtend 32) 0 = ob := by decide

theorem pc_dec (k : Nat) : aluEval .add (BitVec.ofNat 32 (k + 1)) 0xFFFFFFFF = BitVec.ofNat 32 k := by
  rw [ev_add, BitVec.ofNat_add, BitVec.add_assoc]; exact BitVec.add_zero _

theorem pc_inc (k : Nat) : aluEval .add (BitVec.ofNat 32 k) 1 = BitVec.ofNat 32 (k + 1) := by
  rw [ev_add]; exact (BitVec.ofNat_add k 1).symm

theorem pc_fa (F : Word) (k : Nat) :
    F + BitVec.ofNat 32 (0x10 + 8 * k) + 4 = F + BitVec.ofNat 32 (0x14 + 8 * k) := by
  have := add_ofNat_assoc F (0x10 + 8 * k) 4
  rw [show 0x10 + 8 * k + 4 = 0x14 + 8 * k by omega] at this
  exact this

theorem pc_ac_ck (ck : Except Nat Unit) (X : Except Nat PStep)
    (next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)) :
    afterClose (match ck with
      | .error e => .error e
      | .ok () => X) next = keysThen ck (afterClose X next) := by
  cases ck <;> rfl

theorem pc_ac_ke (k : Option Nat) (stk : List (Bool × Nat))
    (next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)) :
    afterClose (match k with
      | none => .error 0x20
      | some v => .ok (.cont stk v)) next = match k with
      | none => .error 0x20
      | some v => next stk v := by
  cases k <;> rfl

theorem pc_cl_snoc (c : Bool) (d : Bytes) (st j : Nat) (init : List (Bool × Nat)) (ob : Bool) (st' pos : Nat) :
    closeLoop c d st (j + 1) (init ++ [(ob, st')]) pos =
      if d.length ≤ wsIn c d pos then .error 0x20
      else if d.getD (wsIn c d pos) 0 = 93 then
        if ob then .error 0x20 else closeLoop c d st j init (wsIn c d pos + 1)
      else if d.getD (wsIn c d pos) 0 = 125 then
        if ob then
          if wsIn c d pos + 1 < st' then .error 0x20
          else match checkKeys c (slice d st' (wsIn c d pos + 1 - st')) with
            | .error e => .error e
            | .ok () => closeLoop c d st j init (wsIn c d pos + 1)
        else .error 0x20
      else if d.getD (wsIn c d pos) 0 = 44 then
        if ob then
          match keyEnd c d (wsIn c d (wsIn c d pos + 1)) with
          | none => .error 0x20
          | some v => .ok (.cont (init ++ [(ob, st')]) v)
        else .ok (.cont (init ++ [(ob, st')]) (wsIn c d (wsIn c d pos + 1)))
      else .error 0x20 := by
  simp only [closeLoop, List.getLast?_concat, List.dropLast_concat]
  rfl

theorem pc_sub : ∀ x : Fin 32, x ∈ jClob ++ [ra] → x ∈ paE := by decide

theorem pc_sub25 : ∀ x : Fin 32, x ∈ jClob ++ [ra, 25] → x ∈ paE := by decide

theorem PRegs.keep25 {f g g0 : Fin 32 → Word} {F p : Word} {n : Nat} {c : Bool} (hR : PRegs f g0 F p n c)
    (hg : ∀ x, x ∉ jClob ++ [ra, 25] → g x = f x) : PRegs g g0 F p n c :=
  ⟨by rw [hg _ (by decide)]; exact hR.sp, by rw [hg _ (by decide)]; exact hR.s3,
    by rw [hg _ (by decide)]; exact hR.s7, by rw [hg _ (by decide)]; exact hR.s8,
    fun x hx => by rw [hg x (fun h => hx (pc_sub25 x h))]; exact hR.fr x hx⟩

theorem PRegs.keep {f g g0 : Fin 32 → Word} {F p : Word} {n : Nat} {c : Bool} (hR : PRegs f g0 F p n c)
    (hg : ∀ x, x ∉ jClob ++ [ra] → g x = f x) : PRegs g g0 F p n c :=
  ⟨by rw [hg _ (by decide)]; exact hR.sp, by rw [hg _ (by decide)]; exact hR.s3,
    by rw [hg _ (by decide)]; exact hR.s7, by rw [hg _ (by decide)]; exact hR.s8,
    fun x hx => by rw [hg x (fun h => hx (pc_sub x h))]; exact hR.fr x hx⟩

section
variable {M0 Mp : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 f : Fin 32 → Word}

/-- `wsIn` at `0x132`: the position in `a0` at `0x146`. -/
theorem pa_ws132 {Q : Post} (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {pos : Nat} {M : Word → BitVec 8}
    (hO : Out M0 M s 404) (hR : PRegs f g0 F p n c) (h25 : f 25 = BitVec.ofNat 32 pos) (hpos : pos ≤ n)
    (k : ∀ g : Fin 32 → Word, g a0 = BitVec.ofNat 32 (wsIn c (memBytes M0 p n) pos) →
      (∀ x, x ∉ jClob ++ [ra] → g x = f x) → WP jsonParseCode base Q M 0x146 g) :
    WP jsonParseCode base Q M 0x132 f := by
  have hn := E.hn
  have hd : memBytes M p n = memBytes M0 p n := hO.bytes E.sP
  have hc1 : ParseCode M base := E.code.out hO E.sep
  refine WP.zero fun hz => ?_
  refine WP.alu jpa_at_132 ?_; wn
  refine WP.branch jpa_at_134 (fun eb => ?_) (fun eb => ?_) <;> wn
  · (try rsimp at eb); rw [hR.s3, br_mode] at eb; subst eb
    exact k _ (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h25]; rfl) (by keepz hz)
  (try rsimp at eb); rw [hR.s3, br_mode] at eb; subst eb
  refine WP.alu jpa_at_138 ?_; wn
  refine WP.alu jpa_at_13a ?_; wn
  refine WP.alu jpa_at_13c ?_; wn
  refine WP.callSkipWs (tb := base + 0xFFFFF372 + 0xFFFFF616 + 0x288) (p := p) (n := n) (q := pos)
    jpa_at_13e jpa_at_142 (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) _ (by decide)) (by decide)
    hc1.get.ri.sw (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s7)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s8)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h25) (by omega) (by omega) fun m2 h0 => ?_
  exact k _ (by (try rsimp); rw [h0, hd]; rfl) (by keepz hz)

/-- `wsIn` at `0x280`, after a comma: the position in `s9` at `0x294`. -/
theorem pa_ws280 {Q : Post} (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {q : Nat} {M : Word → BitVec 8}
    (hO : Out M0 M s 404) (hR : PRegs f g0 F p n c) (h25 : f 25 = BitVec.ofNat 32 q) (hq : q ≤ n)
    (k : ∀ g : Fin 32 → Word, g 25 = BitVec.ofNat 32 (wsIn c (memBytes M0 p n) q) →
      (∀ x, x ∉ jClob ++ [ra, 25] → g x = f x) → PRegs g g0 F p n c → WP jsonParseCode base Q M 0x294 g) :
    WP jsonParseCode base Q M 0x280 f := by
  have hn := E.hn
  have hd : memBytes M p n = memBytes M0 p n := hO.bytes E.sP
  have hc1 : ParseCode M base := E.code.out hO E.sep
  refine WP.zero fun hz => ?_
  refine WP.branch jpa_at_280 (fun eb => ?_) (fun eb => ?_) <;> wn
  · rw [hR.s3, show f x0 = 0 from hz, br_mode] at eb; subst eb
    exact k _ (by rw [h25]; rfl) (fun _ _ => rfl) hR
  rw [hR.s3, show f x0 = 0 from hz, br_mode] at eb; subst eb
  refine WP.alu jpa_at_284 ?_; wn
  refine WP.alu jpa_at_286 ?_; wn
  refine WP.alu jpa_at_288 ?_; wn
  refine WP.callSkipWs (tb := base + 0xFFFFF372 + 0xFFFFF616 + 0x288) (p := p) (n := n) (q := q)
    jpa_at_28a jpa_at_28e (by simp only [BitVec.add_assoc]; rfl)
    (even_at _ (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) _ (by decide)) (by decide)
    hc1.get.ri.sw (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s7)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact hR.s8)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h25) (by omega) (by omega) fun m2 h0 => ?_
  refine WP.alu jpa_at_292 ?_; wn
  exact (fun hg => k _ (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h0, hd]; rfl) hg (hR.keep25 hg))
    (by keepz hz)

/-- The closing loop at `0x12C`, with `17 - j` passes taken (`s5`), the open
arrays and objects `stk`, and the position `pos` after the last value. -/
theorem pa_close (E : PaEnv M0 base s p out n g0 Mp F) {c : Bool} {start d6 : Nat} {w27 : Word}
    {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hnext : PNext M0 Mp base s p out F n c g0 (BitVec.ofNat 32 start) w27 next) (hst : start ≤ n)
    (hd6 : d6 ≤ 16) :
    ∀ (j : Nat) (stk : List (Bool × Nat)) (pos : Nat) (M : Word → BitVec 8) (f : Fin 32 → Word), j ≤ 17 →
      pos ≤ n → FInv M0 Mp s F n stk M → memLoad32 M (F + 0xC) = out → PRegs f g0 F p n c →
      f 21 = BitVec.ofNat 32 (17 - j) → f 25 = BitVec.ofNat 32 pos → f 8 = BitVec.ofNat 32 stk.length →
      f 22 = BitVec.ofNat 32 d6 → f 26 = BitVec.ofNat 32 start → f 27 = w27 →
      WP jsonParseCode base (PPost M0 s p out g0 (afterClose (closeLoop c (memBytes M0 p n) start j stk pos) next))
        M 0x12C f := by
  have hn := E.hn
  have hdl : (memBytes M0 p n).length = n := memBytes_length _ _ _
  intro j
  induction j with
  | zero =>
    intro stk pos M f _ hpos hFI hC hR h21 h25 h8 h22 h26 h27
    have hfr := hR.fr
    refine WP.zero fun hz => ?_
    refine WP.aluImm jpa_at_12c ?_; wn
    refine WP.branch jpa_at_12e (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [h21] at eb; (try simp only [ev_mv hz] at eb)
      exact absurd eb (by decide)
    refine WP.lw jpa_at_26c (by (try rsimp); rw [hR.sp]; exact E.alF (d := 0xC) (by decide)) ?_; wn
    refine WP.aluImm jpa_at_26e ?_; wn
    refine WP.aluImm jpa_at_272 ?_; wn
    refine WP.jal jpa_at_274 (by decide) ?_; wn
    exact hnext M _ stk pos hFI (by pregs hR, E.z0) (by (try rsimp); rw [hR.sp, hC])
      (by (try rsimp); rw [hR.s8, pc_inc]) (by (try rsimp); (try simp only [ev0, ev_mv hz]); try rfl)
      (by (try rsimp); exact h25) hpos (by (try rsimp); exact h8) (by (try rsimp); exact h26)
      (by (try rsimp); exact h27)
  | succ j ih =>
    intro stk pos M f hj hpos hFI hC hR h21 h25 h8 h22 h26 h27
    refine WP.zero fun hz => ?_
    refine WP.aluImm jpa_at_12c ?_; wn
    have h17 : branchTaken .beq (BitVec.ofNat 32 (17 - (j + 1))) (BitVec.ofNat 32 17) = false := by
      rw [br_beq (by omega) (by omega)]; exact decide_eq_false (by omega)
    refine WP.branch jpa_at_12e (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [h21] at eb; (try simp only [ev_mv hz] at eb)
      exact absurd (h17.symm.trans eb) (by decide)
    have hR1 : PRegs (upd f a0 (aluEval .add (f x0) 17)) g0 F p n c := by pregs hR, E.z0
    refine pa_ws132 E hFI.1 hR1 (by (try rsimp); exact h25) hpos fun g ha0 hg => ?_
    have hR' := PRegs.keep hR1 hg
    have hfr := hR'.fr
    have hgz : g 0 = 0 := (hg 0 (by decide)).trans (by (try rsimp); try exact hz)
    have g21 : g 21 = BitVec.ofNat 32 (17 - (j + 1)) := (hg 21 (by decide)).trans (by (try rsimp); exact h21)
    have g25 : g 25 = BitVec.ofNat 32 pos := (hg 25 (by decide)).trans (by (try rsimp); exact h25)
    have g22 : g 22 = BitVec.ofNat 32 d6 := (hg 22 (by decide)).trans (by (try rsimp); exact h22)
    have g26 : g 26 = BitVec.ofNat 32 start := (hg 26 (by decide)).trans (by (try rsimp); exact h26)
    have g27 : g 27 = w27 := (hg 27 (by decide)).trans (by (try rsimp); exact h27)
    have g8 : g 8 = BitVec.ofNat 32 stk.length := (hg 8 (by decide)).trans (by (try rsimp); exact h8)
    generalize hw : wsIn c (memBytes M0 p n) pos = w at ha0
    have hwn : w ≤ n := by rw [← hw]; have := wsIn_le c (memBytes M0 p n) pos; rw [hdl] at this; omega
    rcases list_concat_cases stk with rfl | ⟨init, ⟨ob, st'⟩, rfl⟩
    · refine WP.branch jpa_at_146 (fun _ => ?_) (fun eb => ?_) <;> wn
      rotate_left
      · exfalso; rw [g8, show g x0 = 0 from hgz] at eb
        exact absurd eb (by decide)
      rw [show closeLoop c (memBytes M0 p n) start (j + 1) [] pos = if wsIn c (memBytes M0 p n) pos ≠
          (memBytes M0 p n).length ∨ pos < start ∨ (memBytes M0 p n).length < pos then .error 0x20
          else .ok (.done start pos) from rfl, hdl, hw]
      exact pa_top E hR' ha0 hwn g25 hpos g26 hst hC hFI.1 hFI.2.1
    obtain ⟨t1, t2, t3, t4⟩ := hFI.2.2.top
    rw [List.length_append, List.length_singleton] at g8
    refine WP.branch jpa_at_146 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rw [g8, show g x0 = 0 from hgz, br_beq0 (by omega)] at eb
      exact absurd (of_decide_eq_true eb) (by omega)
    rw [pc_cl_snoc, hdl, hw]
    refine WP.aluImm jpa_at_14a ?_; wn
    have h16 : branchTaken .bltu (BitVec.ofNat 32 16) (BitVec.ofNat 32 d6) = false := by
      rw [br_bltu (by omega) (by omega)]; exact decide_eq_false (by omega)
    refine WP.branch jpa_at_14c (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [g22] at eb; (try simp only [ev_mv hgz] at eb)
      exact absurd (h16.symm.trans eb) (by decide)
    refine WP.branch jpa_at_150 (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); rw [ha0, hR'.s8, br_bgeu (by omega) (by omega)] at eb
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by have := not_dec_true eb; omega))]
      exact pa_2ee E (by (try rsimp); exact hR'.sp) (by (try rsimp); exact hC) hFI.1 hFI.2.1 (by keepz E.z0)
    (try rsimp at eb); rw [ha0, hR'.s8, br_bgeu (by omega) (by omega)] at eb
    have hwlt : w < n := not_dec_false eb
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    have hbv : (memBytes M0 p n).getD w 0 = (M (p + BitVec.ofNat 32 w)).toNat := by
      rw [← hFI.1.bytes E.sP]; exact memBytes_getD hwlt
    refine WP.aluImm jpa_at_154 ?_; wn
    refine WP.alu jpa_at_158 ?_; wn
    refine WP.aluImm jpa_at_15c ?_; wn
    refine WP.lbu jpa_at_160 ?_; wn
    refine WP.aluImm jpa_at_164 ?_; wn
    refine WP.alu jpa_at_166 ?_; wn
    refine WP.lbu jpa_at_168 ?_; wn
    refine WP.aluImm jpa_at_16c ?_; wn
    refine WP.aluImm jpa_at_170 ?_; wn
    rw [hR'.s7, ha0, show aluEval .add p (BitVec.ofNat 32 w) + 0 = p + BitVec.ofNat 32 w by
      rw [ev_add, add_lit_zero], hR'.sp, g8, pc_dec, pa_slot' F (by omega : init.length < 17), pc_fa, t2, g21,
      hbv]
    generalize M (p + BitVec.ofNat 32 w) = b at hbv
    rw [pc_inc, show 17 - (j + 1) + 1 = 17 - j by omega]
    dsimp only at t2 t1 t3 ⊢
    have hw1 : aluEval .add (BitVec.ofNat 32 w) 1 = BitVec.ofNat 32 (w + 1) := pc_inc w
    have hFI' : FInv M0 Mp s F n init M := ⟨hFI.1, hFI.2.1, hFI.2.2.pop⟩
    refine WP.branch jpa_at_172 (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); (try rw [show g x0 = 0 from hgz] at eb); rw [pc_rb] at eb
      rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mp eb))]
      refine WP.branch jpa_at_23c (fun eb2 => ?_) (fun eb2 => ?_) <;> wn
      · (try rsimp at eb2); (try rw [show g x0 = 0 from hgz] at eb2); rw [pc_fl'] at eb2; subst eb2
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        exact pa_2ee E (by (try rsimp); exact hR'.sp) hC hFI.1 hFI.2.1 (by keepz E.z0)
      (try rsimp at eb2); (try rw [show g x0 = 0 from hgz] at eb2); rw [pc_fl'] at eb2; subst eb2
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
      refine WP.aluImm jpa_at_23e ?_; wn
      refine WP.alu jpa_at_242 ?_; wn
      refine WP.jal jpa_at_244 (by decide) ?_; wn
      exact ih init (w + 1) M _ (by omega) (by omega) hFI' hC (by pregs hR', E.z0)
        (by (try rsimp); try rfl)
        (by (try rsimp); rw [ha0, hw1]) (by (try rsimp); (try simp only [ev0]); try rfl)
        (by (try rsimp); exact g22) (by (try rsimp); exact g26) (by (try rsimp); exact g27)
    (try rsimp at eb); (try rw [show g x0 = 0 from hgz] at eb); rw [pc_rb] at eb
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => by rw [h] at eb; exact absurd eb (by decide)))]
    refine WP.aluImm jpa_at_174 ?_; wn
    refine WP.branch jpa_at_178 (fun eb => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · (try rsimp at eb); (try rw [show g x0 = 0 from hgz] at eb); rw [pc_cb] at eb
      rw [ite_eq_left_of_eq_true _ _ (eq_true (nbeq_false eb))]
      refine WP.branch jpa_at_17a (fun eb2 => ?_) (fun eb2 => ?_) <;> wn
      · (try rsimp at eb2); (try rw [show g x0 = 0 from hgz] at eb2); rw [pc_fl] at eb2
        cases ob
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
          exact pa_2ee E (by (try rsimp); exact hR'.sp) hC hFI.1 hFI.2.1 (by keepz E.z0)
        · exact absurd eb2 (by decide)
      (try rsimp at eb2); (try rw [show g x0 = 0 from hgz] at eb2); rw [pc_fl] at eb2
      cases ob
      · exact absurd eb2 (by decide)
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      refine WP.lw jpa_at_17e (by (try rsimp); (try rw [add_lit_zero]); exact aligned_add E.halF (k := 16 + 8 * init.length) (by omega)) ?_; wn
      rw [add_lit_zero, t1]
      refine WP.aluImm jpa_at_180 ?_; wn
      refine WP.branch jpa_at_184 (fun eb3 => ?_) (fun eb3 => ?_) <;> wn
      · (try rsimp at eb3); rw [ha0, hw1, br_bltu (by omega) (by omega)] at eb3
        rw [ite_eq_left_of_eq_true _ _ (eq_true (of_decide_eq_true eb3))]
        exact pa_2ee E (by (try rsimp); exact hR'.sp) hC hFI.1 hFI.2.1 (by keepz E.z0)
      (try rsimp at eb3); rw [ha0, hw1, br_bltu (by omega) (by omega)] at eb3
      have hle : st' ≤ w + 1 := by have := of_decide_eq_false eb3; omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      refine WP.alu jpa_at_188 ?_; wn
      rw [ha0, hw1, show aluEval .sub (BitVec.ofNat 32 (w + 1)) (BitVec.ofNat 32 st') = BitVec.ofNat 32 (w + 1 - st')
        from sub_ofNat_le hle (by omega), pc_ac_ck]
      refine pa_obj E (stk := init ++ [(true, st')]) (st := st') (l := w + 1 - st') (by omega)
        (fun M' g2 hFI2 h8' hC2 hR2 hg2 => ?_) hFI hC (by pregs hR', E.z0) (by (try rsimp); try rfl)
        (by (try rsimp); try rfl)
      have hfr2 := hR2.fr
      have hz2 : g2 0 = 0 := (hg2 0 (by decide)).trans (by (try rsimp); try exact hgz)
      refine WP.alu jpa_at_252 ?_; wn
      refine WP.lw jpa_at_254 (by (try rsimp); rw [hR2.sp]; exact E.alF (d := 8) (by decide)) ?_; wn
      refine WP.jal jpa_at_256 (by decide) ?_; wn
      exact ih init (w + 1) M' _ (by omega) (by omega) ⟨hFI2.1, hFI2.2.1, hFI2.2.2.pop⟩ hC2 (by pregs hR2, E.z0)
        (by (try rsimp); rw [hg2 21 (by decide)]; (try rsimp); try rfl)
        (by (try rsimp); rw [hg2 25 (by decide)]; (try rsimp); try rfl)
        (by (try rsimp); rw [hg2 20 (by decide), show g2 x0 = 0 from hz2, ev0]; (try rsimp); try rfl)
        (by (try rsimp); rw [hg2 22 (by decide)]; (try rsimp); exact g22)
        (by (try rsimp); rw [hR2.sp, h8']; (try rsimp); exact g26)
        (by (try rsimp); rw [hg2 27 (by decide)]; (try rsimp); exact g27)
    (try rsimp at eb); (try rw [show g x0 = 0 from hgz] at eb); rw [pc_cb] at eb
    rw [ite_eq_right_of_eq_false _ _ (eq_false (nbeq_true eb))]
    refine WP.aluImm jpa_at_276 ?_; wn
    refine WP.branch jpa_at_27a (fun eb => ?_) (fun eb => ?_) <;> wn
    · (try rsimp at eb); (try rw [show g x0 = 0 from hgz] at eb); rw [pc_cm] at eb
      rw [ite_eq_right_of_eq_false _ _ (eq_false (nbeq_true eb))]
      exact pa_2ee E (by (try rsimp); exact hR'.sp) hC hFI.1 hFI.2.1 (by keepz E.z0)
    (try rsimp at eb); (try rw [show g x0 = 0 from hgz] at eb); rw [pc_cm] at eb
    rw [ite_eq_left_of_eq_true _ _ (eq_true (nbeq_false eb))]
    refine WP.aluImm jpa_at_27c ?_; wn
    refine pa_ws280 E hFI.1 (by pregs hR', E.z0) (by (try rsimp); rw [ha0]; exact hw1) (by omega) fun g3 h25' hg3 hR3 => ?_
    have hz3 : g3 0 = 0 := (hg3 0 (by decide)).trans (by (try rsimp); try exact hgz)
    have h93 : g3 9 = (flagB ob).zeroExtend 32 := (hg3 9 (by decide)).trans (by (try rsimp); try rfl)
    have h83 : g3 8 = BitVec.ofNat 32 (init ++ [(ob, st')]).length := by
      rw [hg3 8 (by decide)]; (try rsimp); rw [g8, List.length_append]; rfl
    have hq : wsIn c (memBytes M0 p n) (w + 1) ≤ n := by
      have := wsIn_le c (memBytes M0 p n) (w + 1); rw [hdl] at this; omega
    refine WP.aluImm jpa_at_294 ?_; wn
    refine WP.aluImm jpa_at_298 ?_; wn
    refine WP.lw jpa_at_29a (by (try rsimp); rw [hR3.sp]; exact E.alF (d := 0xC) (by decide)) ?_; wn
    refine WP.branch jpa_at_29c (fun eb2 => ?_) (fun eb2 => ?_) <;> wn
    · (try rsimp at eb2); (try rw [h93] at eb2); (try rw [show g3 x0 = 0 from hz3] at eb2); rw [pc_fl] at eb2
      cases ob
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
        exact hnext M _ _ _ hFI (by pregs hR3, E.z0) (by (try rsimp); rw [hR3.sp]; exact hC)
          (by (try rsimp); rw [hR3.s8]; exact pc_inc n) (by (try rsimp); try rfl) (by (try rsimp); exact h25') hq
          (by (try rsimp); exact h83) (by (try rsimp); rw [hg3 26 (by decide)]; (try rsimp); exact g26)
          (by (try rsimp); rw [hg3 27 (by decide)]; (try rsimp); exact g27)
      · exact absurd eb2 (by decide)
    (try rsimp at eb2); (try rw [h93] at eb2); (try rw [show g3 x0 = 0 from hz3] at eb2); rw [pc_fl] at eb2
    cases ob
    · exact absurd eb2 (by decide)
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), pc_ac_ke]
    exact pa_2a0 E hnext hFI (by pregs hR3, E.z0) (by (try rsimp); rw [hR3.sp]; exact hC)
      (by (try rsimp); rw [hR3.s8]; exact pc_inc n) (by (try rsimp); try rfl) (by (try rsimp); exact h25') hq
      (by (try rsimp); exact h83) (by (try rsimp); rw [hg3 26 (by decide)]; (try rsimp); exact g26)
      (by (try rsimp); rw [hg3 27 (by decide)]; (try rsimp); exact g27)

end

end C3.RV32
