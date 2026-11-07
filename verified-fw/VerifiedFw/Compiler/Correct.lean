/-
The compiler correctness proof: compiled code, run on the RISC-V model, makes
exactly the device stores that the source semantics says, then stops in a
one-instruction loop that changes nothing.
-/
import VerifiedFw.Compiler.Exec

namespace VerifiedFw.Compiler

open VerifiedFw.RiscV VerifiedFw.Lang

variable {p : Platform}

theorem step_of {m m' : Machine} {pc : Word} {i : Instr} (hc : m.imem pc = encode i)
    (hpc : m.pc = pc) (ha : aligned pc) (he : exec p m i = some m') : step p m = some m' := by
  subst hpc; rw [step_at hc ha, he]

theorem code0 {imem : Word → Word} {pc : Word} {code : List Instr} (h : CodeAt imem pc code)
    (k : Nat) (hk : k < code.length) : imem (after pc k) = encode code[k] := h k hk

theorem gp_val : gp.val = 3 := rfl

theorem tmp_val {d : Nat} (h : d ≤ 26) : (tmp d).val = 5 + d := by
  simp only [tmp]; omega

theorem tmp_ne_zero {d : Nat} (h : d ≤ 26) : tmp d ≠ 0 := by
  intro he; have := congrArg Fin.val he; rw [tmp_val h] at this; simp at this

/-! ## Constants -/

theorem loadImm_correct {m : Machine} {pc : Word} {rd : Reg} {c : Word}
    (hc : CodeAt m.imem pc (loadImm rd c)) (hpc : m.pc = pc) (ha : aligned pc) (hrd : rd ≠ 0) :
    ∃ m', Star p m m' ∧ m'.pc = after pc 2 ∧ m'.reg rd = c ∧ m'.imem = m.imem ∧
      m'.dmem = m.dmem ∧ m'.trace = m.trace ∧ ∀ r, r ≠ rd → m'.reg r = m.reg r := by
  have h0 := code0 hc 0 (by simp [loadImm])
  have h1 := code0 hc 1 (by simp [loadImm])
  simp only [loadImm, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at h0 h1
  let hi : Word := (((c - sext12 (c.setWidth 12)) >>> 12).setWidth 20).setWidth 32 <<< 12
  let m1 := (m.setReg rd hi).next
  let m2 := (m1.setReg rd (m1.reg rd + sext12 (c.setWidth 12))).next
  have s1 : step p m = some m1 := step_of h0 hpc ha rfl
  have s2 : step p m1 = some m2 :=
    step_of (pc := after pc 1) (by simpa [m1] using h1) (by simp [m1, hpc]; rfl)
      (aligned_after ha 1) rfl
  refine ⟨m2, .step s1 (.single s2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [m2, m1, next_pc, setReg_pc, hpc, after_one, after_after]
  · simp only [m2, m1, next_reg, reg_setReg_self _ _ _ hrd]
    exact loadImm_val c
  · simp [m2, m1]
  · simp [m2, m1]
  · simp [m2, m1]
  · intro r hr; simp [m2, m1, reg_setReg_other _ _ _ _ hr]

/-! ## Expressions -/

/-- What code for an expression at depth `d` leaves alone: memory, the trace,
and every register below its temporaries. -/
structure ExprFrame (d : Nat) (m m' : Machine) : Prop where
  imem : m'.imem = m.imem
  dmem : m'.dmem = m.dmem
  trace : m'.trace = m.trace
  regs : ∀ r : Reg, r.val < 5 + d → m'.reg r = m.reg r

/-- Global `i` lives at `base + 4 * i`. -/
def GlobalsAt (base : Word) (g : Nat) (vars : Nat → Word) (dmem : Word → Word) : Prop :=
  ∀ i < g, dmem (after base i) = vars i

theorem binInstr_exec (op : BinOp) (m : Machine) (rd rs1 rs2 : Reg) :
    exec p m (binInstr op rd rs1 rs2) =
      some ((m.setReg rd (op.eval (m.reg rs1) (m.reg rs2))).next) := by
  cases op <;> rfl

theorem Expr.regs_pos (e : Expr) : 1 ≤ e.regs := by
  cases e <;> simp [Expr.regs]; omega

theorem expr_correct (base : Word) (g : Nat) (vars : Nat → Word) (hbase : aligned base)
    (hmmio : ∀ i < g, p.isMmio (after base i) = false) (hg : g ≤ 512) :
    ∀ (e : Expr) (d : Nat) (m : Machine) (pc : Word),
      e.varsBelow g = true → d + e.regs ≤ 27 →
      CodeAt m.imem pc (compileExpr e d) → m.pc = pc → aligned pc →
      m.reg gp = base → GlobalsAt base g vars m.dmem →
      ∃ m', Star p m m' ∧ m'.pc = after pc (compileExpr e d).length ∧
        m'.reg (tmp d) = e.eval vars ∧ ExprFrame d m m' := by
  intro e
  induction e with
  | const c =>
    intro d m pc _ hd hc hpc ha _ _
    have hd' : d ≤ 26 := by simp [Expr.regs] at hd; omega
    obtain ⟨m', hs, hpc', hr, hi, hdm, htr, hother⟩ :=
      loadImm_correct (p := p) hc hpc ha (tmp_ne_zero hd')
    refine ⟨m', hs, by simpa [compileExpr, loadImm] using hpc', hr, hi, hdm, htr, ?_⟩
    intro r hr'
    apply hother
    intro he; subst he; rw [tmp_val hd'] at hr'; omega
  | var i =>
    intro d m pc hv hd hc hpc ha hgp hglob
    have hd' : d ≤ 26 := by simp [Expr.regs] at hd; omega
    have hi : i < g := by simpa [Expr.varsBelow] using hv
    have h0 := code0 hc 0 (by simp [compileExpr])
    simp only [compileExpr, List.getElem_cons_zero, after_zero] at h0
    have haddr : m.reg gp + sext12 (slot i) = after base i := by
      rw [hgp, sext12_slot (by omega)]; rfl
    let m' := (m.setReg (tmp d) (m.dmem (after base i))).next
    have hs : step p m = some m' := by
      apply step_of h0 hpc ha
      simp only [exec, haddr, aligned_after hbase i, hmmio i hi, and_self, ↓reduceIte]
      rfl
    refine ⟨m', .single hs, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
    · simp [m', hpc, compileExpr]; rfl
    · simp only [m', next_reg, reg_setReg_self _ _ _ (tmp_ne_zero hd'), Expr.eval]
      exact hglob i hi
    · simp [m']
    · simp [m']
    · simp [m']
    · intro r hr
      simp only [m', next_reg]
      apply reg_setReg_other
      intro he; subst he; rw [tmp_val hd'] at hr; omega
  | bin op a b iha ihb =>
    intro d m pc hv hd hc hpc ha hgp hglob
    simp only [Expr.varsBelow, Bool.and_eq_true] at hv
    simp only [Expr.regs] at hd
    have hb1 := Expr.regs_pos b
    have hd' : d ≤ 25 := by omega
    simp only [compileExpr, CodeAt.append] at hc
    obtain ⟨⟨hca, hcb⟩, hco⟩ := hc
    obtain ⟨m1, hs1, hpc1, hr1, hf1⟩ :=
      iha d m pc hv.1 (by omega) hca hpc ha hgp hglob
    obtain ⟨m2, hs2, hpc2, hr2, hf2⟩ :=
      ihb (d + 1) m1 _ hv.2 (by omega) (by rw [hf1.imem]; exact hcb) hpc1
        (aligned_after ha _) (by rw [hf1.regs gp (by rw [gp_val]; omega)]; exact hgp)
        (by rw [hf1.dmem]; exact hglob)
    have hco' := CodeAt.single.mp hco
    rw [List.length_append] at hco'
    rw [after_after] at hpc2
    let m3 := (m2.setReg (tmp d) (op.eval (m2.reg (tmp d)) (m2.reg (tmp (d + 1))))).next
    have hs3 : step p m2 = some m3 :=
      step_of (by rw [hf2.imem, hf1.imem]; exact hco') hpc2 (aligned_after ha _)
        (binInstr_exec op m2 _ _ _)
    have hd2 : m2.reg (tmp d) = a.eval vars := by
      rw [hf2.regs (tmp d) (by rw [tmp_val (by omega)]; omega), hr1]
    refine ⟨m3, (hs1.trans hs2).trans (.single hs3), ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
    · simp only [m3, next_pc, setReg_pc, hpc2, after_succ, compileExpr, List.length_append,
        List.length_singleton]
    · simp only [m3, next_reg, Expr.eval, hd2, hr2]
      exact reg_setReg_self _ _ _ (tmp_ne_zero (by omega))
    · simp [m3, hf2.imem, hf1.imem]
    · simp [m3, hf2.dmem, hf1.dmem]
    · simp [m3, hf2.trace, hf1.trace]
    · intro r hr
      simp only [m3, next_reg]
      rw [reg_setReg_other _ _ _ _ (by intro he; subst he; rw [tmp_val (by omega)] at hr; omega),
        hf2.regs r (by omega), hf1.regs r hr]

/-! ## Single instructions the statement code uses -/

theorem setReg_zero (m : Machine) (v : Word) : m.setReg 0 v = m := by
  simp [Machine.setReg]

@[simp] theorem reg_zero (m : Machine) : m.reg zero = 0 := rfl

theorem exec_sw_ram {m : Machine} {rs2 rs1 : Reg} {imm : BitVec 12} {a : Word}
    (ha : m.reg rs1 + sext12 imm = a) (hal : aligned a) (hm : p.isMmio a = false) :
    exec p m (.sw rs2 rs1 imm) =
      some { m.next with dmem := fun x => if x = a then m.reg rs2 else m.dmem x } := by
  simp only [exec, ha, hal, hm, ↓reduceIte, Bool.false_eq_true]

theorem exec_sw_mmio {m : Machine} {rs2 rs1 : Reg} {imm : BitVec 12} {a : Word}
    (ha : m.reg rs1 + sext12 imm = a) (hal : aligned a) (hm : p.isMmio a = true) :
    exec p m (.sw rs2 rs1 imm) = some { m.next with trace := m.trace ++ [⟨a, m.reg rs2⟩] } := by
  simp only [exec, ha, hal, hm, ↓reduceIte]

theorem exec_lw {m : Machine} {rd rs1 : Reg} {imm : BitVec 12} {a : Word}
    (ha : m.reg rs1 + sext12 imm = a) (hal : aligned a) (hm : p.isMmio a = false) :
    exec p m (.lw rd rs1 imm) = some ((m.setReg rd (m.dmem a)).next) := by
  simp only [exec, ha, hal, hm, and_self, ↓reduceIte]

theorem exec_jal_zero (m : Machine) (off : BitVec 20) :
    exec p m (.jal zero off) = some { m with pc := m.pc + jumpOffset off } := by
  simp only [exec, zero, setReg_zero]

theorem exec_bne_taken {m : Machine} {rs1 rs2 : Reg} {off : BitVec 12}
    (h : m.reg rs1 ≠ m.reg rs2) :
    exec p m (.bne rs1 rs2 off) = some { m with pc := m.pc + branchOffset off } := by
  simp only [exec, h, ne_eq, not_false_eq_true, ↓reduceIte]

theorem exec_bne_not {m : Machine} {rs1 rs2 : Reg} {off : BitVec 12}
    (h : m.reg rs1 = m.reg rs2) : exec p m (.bne rs1 rs2 off) = some m.next := by
  simp only [exec, h, ne_eq, not_true_eq_false, ↓reduceIte]

/-! ## Statements -/

/-- The machine holds source state `s`: `gp` points at the globals, RAM holds
their values, and the device stores so far match. -/
structure Inv (base : Word) (g : Nat) (m : Machine) (s : State) : Prop where
  gp : m.reg gp = base
  vars : GlobalsAt base g s.vars m.dmem
  trace : m.trace = s.trace

/-- What the statement proof needs from the target: `n` aligned RAM slots
from `base`, none of them a device register. -/
structure Layout (p : Platform) (base : Word) (n : Nat) : Prop where
  aligned : aligned base
  ram : ∀ i < n, p.isMmio (after base i) = false
  bound : n ≤ 512

theorem Inv.withPc {base : Word} {g : Nat} {m : Machine} {s : State} (h : Inv base g m s)
    (x : Word) : Inv base g { m with pc := x } s :=
  ⟨h.gp, h.vars, h.trace⟩

theorem tmp0_ne_gp : tmp 0 ≠ gp := by decide
theorem tmp1_ne_gp : tmp 1 ≠ gp := by decide
theorem tmp0_ne_tmp1 : tmp 0 ≠ tmp 1 := by decide

theorem Nat.repeat_succ' {α : Type} (f : α → α) (n : Nat) (a : α) :
    Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat] at *; rw [ih]

theorem sext12_neg_one : sext12 (-1) = -1 := by decide

theorem ofNat_succ_sub_one (r : Nat) :
    BitVec.ofNat 32 (r + 1) + sext12 (-1) = BitVec.ofNat 32 r := by
  rw [sext12_neg_one, BitVec.ofNat_add, BitVec.add_assoc,
    show BitVec.ofNat 32 1 + -1 = 0 by decide]
  simp

theorem ofNat_succ_ne_zero (r : Nat) (h : r + 1 < 2 ^ 32) : BitVec.ofNat 32 (r + 1) ≠ 0 := by
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  simp at this

theorem loadImm_length (rd : Reg) (c : Word) : (loadImm rd c).length = 2 := rfl

theorem jumpOffset_fwd_int {x : Int} {n : Nat} (hx : x = n) (h : n < 2 ^ 18) :
    jumpOffset (jumpBy x) = .ofNat 32 (4 * n) := by
  subst hx; exact jumpOffset_fwd h

theorem jumpOffset_back_int {x : Int} {n : Nat} (hx : x = -(n : Int)) (h : n < 2 ^ 18) :
    jumpOffset (jumpBy x) + .ofNat 32 (4 * n) = 0 := by
  subst hx; exact jumpOffset_back h

theorem ite_neg {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem stmt_correct (t : Target) (base : Word) (g n : Nat) (hl : Layout t.platform base n) :
    ∀ (s : Stmt) (k : Nat) (m : Machine) (st : State) (pc : Word),
      s.wf t g = true → g + k + s.loopDepth ≤ n → (compileStmt g s k).length < 2 ^ 17 →
      CodeAt m.imem pc (compileStmt g s k) → m.pc = pc → aligned pc → Inv base g m st →
      ∃ m', Star t.platform m m' ∧ m'.pc = after pc (compileStmt g s k).length ∧
        Inv base g m' (s.run st) ∧ m'.imem = m.imem ∧
        ∀ j < k, m'.dmem (after base (g + j)) = m.dmem (after base (g + j)) := by
  have hexpr := expr_correct (p := t.platform) base g
  have hb := hl.bound
  intro s
  induction s with
  | skip =>
    intro k m st pc _ _ _ _ hpc _ hinv
    exact ⟨m, .refl m, by simp [compileStmt, hpc], hinv, rfl, fun _ _ => rfl⟩
  | assign i e =>
    intro k m st pc hwf hn _ hc hpc ha hinv
    simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨hi, hv⟩, hr⟩ := hwf
    simp only [compileStmt, CodeAt.append] at hc
    obtain ⟨hce, hcs⟩ := hc
    obtain ⟨m1, hs1, hpc1, hr1, hf1⟩ :=
      hexpr st.vars hl.aligned (fun i hi => hl.ram i (by omega)) (by have := hl.bound; omega)
        e 0 m pc hv (by omega) hce hpc ha hinv.gp hinv.vars
    have hgp1 : m1.reg gp = base := by rw [hf1.regs gp (by rw [gp_val]; omega), hinv.gp]
    have haddr : m1.reg gp + sext12 (slot i) = after base i := by
      rw [hgp1, sext12_slot (by have := hl.bound; omega)]; rfl
    let v := e.eval st.vars
    let m2 : Machine := { m1.next with dmem := fun x => if x = after base i then v else m1.dmem x }
    have hs2 : step t.platform m1 = some m2 := by
      apply step_of (by rw [hf1.imem]; exact CodeAt.single.mp hcs) hpc1 (aligned_after ha _)
      rw [exec_sw_ram haddr (aligned_after hl.aligned i) (hl.ram i (by omega)), hr1]
    refine ⟨m2, hs1.trans (.single hs2), ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [m2, next_pc, hpc1, after_succ, compileStmt, List.length_append,
        List.length_singleton]
    · exact hgp1
    · intro j hj
      simp only [m2, Stmt.run]
      by_cases hji : j = i
      · subst hji; simp [v]
      · rw [ite_neg (slot_ne (by omega) (by omega) hji), ite_neg hji, hf1.dmem]
        exact hinv.vars j hj
    · simp [m2, Stmt.run, hf1.trace, hinv.trace]
    · simp [m2, hf1.imem]
    · intro j hj
      simp only [m2]
      rw [ite_neg (slot_ne (by omega) (by omega) (by omega)), hf1.dmem]
  | store a e =>
    intro k m st pc hwf hn _ hc hpc ha hinv
    simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
    obtain ⟨⟨⟨hmm, hal⟩, hv⟩, hr⟩ := hwf
    simp only [compileStmt, CodeAt.append] at hc
    obtain ⟨⟨hce, hcl⟩, hcs⟩ := hc
    obtain ⟨m1, hs1, hpc1, hr1, hf1⟩ :=
      hexpr st.vars hl.aligned (fun i hi => hl.ram i (by omega)) (by have := hl.bound; omega)
        e 0 m pc hv (by omega) hce hpc ha hinv.gp hinv.vars
    obtain ⟨m2, hs2, hpc2, hr2, hi2, hd2, ht2, ho2⟩ :=
      loadImm_correct (p := t.platform) (by rw [hf1.imem]; exact hcl) hpc1 (aligned_after ha _)
        (tmp_ne_zero (d := 1) (by omega))
    rw [after_after] at hpc2
    have hv2 : m2.reg (tmp 0) = e.eval st.vars := by rw [ho2 _ tmp0_ne_tmp1, hr1]
    let m3 : Machine := { m2.next with trace := m2.trace ++ [⟨a, m2.reg (tmp 0)⟩] }
    have hs3 : step t.platform m2 = some m3 := by
      have hcs' := CodeAt.single.mp hcs
      simp only [List.length_append, loadImm, List.length_cons, List.length_nil] at hcs'
      apply step_of (by rw [hi2, hf1.imem]; exact hcs') hpc2 (aligned_after ha _)
      exact exec_sw_mmio (by rw [hr2, sext12_zero]; simp) hal hmm
    refine ⟨m3, (hs1.trans hs2).trans (.single hs3), ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [m3, next_pc, hpc2, after_succ, compileStmt, List.length_append,
        List.length_singleton, loadImm, List.length_cons, List.length_nil]
    · change m2.reg gp = base
      rw [ho2 _ tmp1_ne_gp.symm, hf1.regs gp (by rw [gp_val]; omega), hinv.gp]
    · simp only [m3, next_dmem, hd2, hf1.dmem, Stmt.run]; exact hinv.vars
    · simp only [m3, next_trace, ht2, hf1.trace, hinv.trace, Stmt.run, hv2]
    · simp [m3, hi2, hf1.imem]
    · intro j _; simp [m3, hd2, hf1.dmem]
  | seq a b iha ihb =>
    intro k m st pc hwf hn hlen hc hpc ha hinv
    simp only [Stmt.wf, Bool.and_eq_true] at hwf
    simp only [Stmt.loopDepth] at hn
    simp only [compileStmt, CodeAt.append, List.length_append] at hc hlen
    obtain ⟨m1, hs1, hpc1, hinv1, hi1, hk1⟩ :=
      iha k m st pc hwf.1 (by omega) (by omega) hc.1 hpc ha hinv
    obtain ⟨m2, hs2, hpc2, hinv2, hi2, hk2⟩ :=
      ihb k m1 _ _ hwf.2 (by omega) (by omega) (by rw [hi1]; exact hc.2) hpc1
        (aligned_after ha _) hinv1
    refine ⟨m2, hs1.trans hs2, ?_, hinv2, by rw [hi2, hi1], fun j hj => by rw [hk2 j hj, hk1 j hj]⟩
    rw [hpc2, after_after]; simp [compileStmt]
  | ite c a b iha ihb =>
    intro k m st pc hwf hn hlen hc hpc ha hinv
    simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨hv, hr⟩, hwa⟩, hwb⟩ := hwf
    simp only [Stmt.loopDepth] at hn
    simp only [compileStmt, CodeAt.append, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.reduceAdd] at hc hlen ⊢
    obtain ⟨⟨⟨⟨hcc, hcbr⟩, hca⟩, hcj⟩, hcb⟩ := hc
    generalize hla : (compileStmt g a k).length = la at *
    generalize hlb : (compileStmt g b k).length = lb at *
    generalize hlc : (compileExpr c 0).length = lc at *
    have hbne : m.imem (after pc lc) = encode (.bne (tmp 0) zero 4) := by
      simpa using hcbr 0 (by simp)
    have hjal1 : m.imem (after pc (lc + 1)) =
        encode (.jal zero (jumpBy ((la : Int) + 2))) := by
      have := hcbr 1 (by simp); rw [after_after] at this; simpa using this
    obtain ⟨m1, hs1, hpc1, hr1, hf1⟩ :=
      hexpr st.vars hl.aligned (fun i hi => hl.ram i (by omega)) (by omega)
        c 0 m pc hv (by omega) hcc hpc ha hinv.gp hinv.vars
    rw [hlc] at hpc1
    have hinv1 : Inv base g m1 st :=
      ⟨by rw [hf1.regs gp (by rw [gp_val]; omega), hinv.gp], by rw [hf1.dmem]; exact hinv.vars,
        by rw [hf1.trace]; exact hinv.trace⟩
    by_cases hcond : c.eval st.vars = 0
    · -- The condition is zero: jump over the `then` branch to the `else` branch.
      have hs2 : step t.platform m1 = some m1.next :=
        step_of (by rw [hf1.imem]; exact hbne) hpc1 (aligned_after ha _)
          (exec_bne_not (by rw [hr1, reg_zero]; exact hcond))
      let m3 : Machine := { m1.next with pc := m1.next.pc + jumpOffset (jumpBy ((la : Int) + 2)) }
      have hs3 : step t.platform m1.next = some m3 :=
        step_of (by rw [next_imem, hf1.imem]; exact hjal1) (by rw [next_pc, hpc1, after_succ])
          (aligned_after ha _) (exec_jal_zero _ _)
      have hpc3 : m3.pc = after pc (lc + 2 + la + 1) := by
        simp only [m3, next_pc, hpc1, after_succ]
        rw [jumpOffset_fwd_int (n := la + 2) (by omega) (by omega), ← after, after_after]
        congr 1; omega
      obtain ⟨m4, hs4, hpc4, hinv4, hi4, hk4⟩ :=
        ihb k m3 st _ hwb (by omega) (by omega)
          (by simp only [m3, next_imem]; rw [hf1.imem]; exact hcb) hpc3 (aligned_after ha _)
          ⟨hinv1.gp, hinv1.vars, hinv1.trace⟩
      rw [hlb] at hpc4
      refine ⟨m4, ((hs1.trans (.single hs2)).trans (.single hs3)).trans hs4, ?_, ?_, ?_, ?_⟩
      · rw [hpc4, after_after]
      · simp only [Stmt.run, hcond, ne_eq, not_true_eq_false, ↓reduceIte]; exact hinv4
      · simp [hi4, m3, hf1.imem]
      · intro j hj; rw [hk4 j hj]; simp only [m3, next_dmem]; rw [hf1.dmem]
    · -- The condition is nonzero: run the `then` branch, then jump past `else`.
      let m2 : Machine := { m1 with pc := m1.pc + branchOffset 4 }
      have hs2 : step t.platform m1 = some m2 :=
        step_of (by rw [hf1.imem]; exact hbne) hpc1 (aligned_after ha _)
          (exec_bne_taken (by rw [hr1, reg_zero]; exact hcond))
      have hpc2 : m2.pc = after pc (lc + 2) := by
        show m1.pc + branchOffset 4 = _
        rw [hpc1, branchOffset_four, ← after_after]; rfl
      obtain ⟨m3, hs3, hpc3, hinv3, hi3, hk3⟩ :=
        iha k m2 st _ hwa (by omega) (by omega)
          (by show CodeAt m1.imem _ _; rw [hf1.imem]; exact hca) hpc2 (aligned_after ha _)
          ⟨hinv1.gp, hinv1.vars, hinv1.trace⟩
      rw [hla, after_after] at hpc3
      have hj : m3.imem (after pc (lc + 2 + la)) =
          encode (.jal zero (jumpBy ((lb : Int) + 1))) := by
        rw [hi3]; show m1.imem _ = _; rw [hf1.imem]; exact CodeAt.single.mp hcj
      let m4 : Machine := { m3 with pc := m3.pc + jumpOffset (jumpBy ((lb : Int) + 1)) }
      have hs4 : step t.platform m3 = some m4 :=
        step_of hj hpc3 (aligned_after ha _) (exec_jal_zero m3 _)
      refine ⟨m4, ((hs1.trans (.single hs2)).trans hs3).trans (.single hs4), ?_, ?_, ?_, ?_⟩
      · simp only [m4, hpc3]
        rw [jumpOffset_fwd_int (n := lb + 1) (by omega) (by omega), ← after, after_after]
        congr 1; omega
      · simp only [Stmt.run, hcond, ne_eq, not_false_eq_true, ↓reduceIte]
        exact ⟨hinv3.gp, hinv3.vars, hinv3.trace⟩
      · simp only [m4]; rw [hi3]; show m1.imem = m.imem; exact hf1.imem
      · intro j hj; simp only [m4]; rw [hk3 j hj]; show m1.dmem _ = _; rw [hf1.dmem]
  | loop cnt body ih =>
    intro k m st pc hwf hn hlen hc hpc ha hinv
    simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨hcnt, hwb⟩ := hwf
    simp only [Stmt.loopDepth] at hn
    simp only [compileStmt, CodeAt.append, List.length_append, List.length_cons,
      List.length_nil, loadImm_length, Nat.zero_add, Nat.reduceAdd] at hc hlen ⊢
    obtain ⟨⟨⟨⟨hli, hsw⟩, hhead⟩, hcb⟩, hback⟩ := hc
    generalize hlb : (compileStmt g body (k + 1)).length = lb at *
    have hgk : g + k < n := by omega
    let ctr := after base (g + k)
    have hctr : m.reg gp + sext12 (slot (g + k)) = ctr := by
      rw [hinv.gp, sext12_slot (by omega)]; rfl
    have hctr_ram := hl.ram (g + k) hgk
    have hctr_al := aligned_after hl.aligned (g + k)
    -- Load the count and store it in the loop's counter slot.
    obtain ⟨m1, hs1, hpc1, hr1, hi1, hd1, ht1, ho1⟩ :=
      loadImm_correct (p := t.platform) hli hpc ha (tmp_ne_zero (d := 0) (by omega))
    have hgp1 : m1.reg gp = base := by rw [ho1 gp tmp0_ne_gp.symm, hinv.gp]
    let m2 : Machine :=
      { m1.next with dmem := fun x => if x = ctr then m1.reg (tmp 0) else m1.dmem x }
    have hs2 : step t.platform m1 = some m2 :=
      step_of (by rw [hi1]; exact CodeAt.single.mp hsw) hpc1 (aligned_after ha _)
        (exec_sw_ram (by rw [hgp1, ← hinv.gp]; exact hctr) hctr_al hctr_ram)
    have hinv2 : Inv base g m2 st := by
      refine ⟨hgp1, fun i hi => ?_, by simp [m2, ht1, hinv.trace]⟩
      simp only [m2]
      rw [ite_neg (slot_ne (by omega) (by omega) (by omega)), hd1]
      exact hinv.vars i hi
    have hhead' : ∀ i (hi : i < 5), m.imem (after pc (3 + i)) = encode
        ([.lw (tmp 0) gp (slot (g + k)), .bne (tmp 0) zero 4,
          .jal zero (jumpBy ((lb : Int) + 4)), .addi (tmp 0) (tmp 0) (-1),
          .sw (tmp 0) gp (slot (g + k))] : List Instr)[i] := by
      intro i hi; rw [← after_after]; exact hhead i (by simpa using hi)
    -- Each pass through the loop head, by the number of passes left.
    have hloop : ∀ r, r ≤ cnt → ∀ (m' : Machine) (st' : State),
        m'.imem = m.imem → m'.pc = after pc 3 → m'.dmem ctr = .ofNat 32 r →
        Inv base g m' st' →
        ∃ m'', Star t.platform m' m'' ∧ m''.pc = after pc (3 + 5 + lb + 1) ∧
          Inv base g m'' (Nat.repeat body.run r st') ∧ m''.imem = m'.imem ∧
          ∀ j < k, m''.dmem (after base (g + j)) = m'.dmem (after base (g + j)) := by
      intro r
      induction r with
      | zero =>
        intro _ ma sta him hpca hctra hinva
        have hca : ma.reg gp + sext12 (slot (g + k)) = ctr := by
          rw [hinva.gp, sext12_slot (by omega)]; rfl
        let mb := (ma.setReg (tmp 0) (ma.dmem ctr)).next
        have hsa : step t.platform ma = some mb :=
          step_of (by rw [him]; exact hhead' 0 (by omega)) hpca (aligned_after ha _)
            (exec_lw hca hctr_al hctr_ram)
        have hsb : step t.platform mb = some mb.next :=
          step_of (by simp only [mb, next_imem, setReg_imem, him]; exact hhead' 1 (by omega))
            (by simp only [mb, next_pc, setReg_pc, hpca, after_succ]) (aligned_after ha _)
            (exec_bne_not (by
              simp only [mb, next_reg, reg_setReg_self _ _ _ (tmp_ne_zero (d := 0) (by omega)),
                hctra, reg_zero]; rfl))
        let mc : Machine := { mb.next with pc := mb.next.pc + jumpOffset (jumpBy ((lb : Int) + 4)) }
        have hsc : step t.platform mb.next = some mc :=
          step_of (by simp only [mb, next_imem, setReg_imem, him]; exact hhead' 2 (by omega))
            (by simp only [mb, next_pc, setReg_pc, hpca, after_succ]) (aligned_after ha _)
            (exec_jal_zero _ _)
        refine ⟨mc, (.step hsa (.step hsb (.single hsc))), ?_, ?_, ?_, ?_⟩
        · simp only [mc, mb, next_pc, setReg_pc, hpca, after_succ]
          rw [jumpOffset_fwd_int (n := lb + 4) (by omega) (by omega), ← after, after_after]
          congr 1; omega
        · refine ⟨?_, ?_, ?_⟩
          · change (ma.setReg (tmp 0) (ma.dmem ctr)).reg gp = base
            rw [reg_setReg_other _ _ _ _ tmp0_ne_gp.symm, hinva.gp]
          · exact hinva.vars
          · exact hinva.trace
        · simp [mc, mb]
        · intro j _; simp [mc, mb]
      | succ r ihr =>
        intro hr ma sta him hpca hctra hinva
        have hca : ma.reg gp + sext12 (slot (g + k)) = ctr := by
          rw [hinva.gp, sext12_slot (by omega)]; rfl
        let mb := (ma.setReg (tmp 0) (ma.dmem ctr)).next
        have hsa : step t.platform ma = some mb :=
          step_of (by rw [him]; exact hhead' 0 (by omega)) hpca (aligned_after ha _)
            (exec_lw hca hctr_al hctr_ram)
        have hbt0 : mb.reg (tmp 0) = .ofNat 32 (r + 1) := by
          simp only [mb, next_reg, reg_setReg_self _ _ _ (tmp_ne_zero (d := 0) (by omega)), hctra]
        let mc : Machine := { mb with pc := mb.pc + branchOffset 4 }
        have hsb : step t.platform mb = some mc :=
          step_of (by simp only [mb, next_imem, setReg_imem, him]; exact hhead' 1 (by omega))
            (by simp only [mb, next_pc, setReg_pc, hpca, after_succ]) (aligned_after ha _)
            (exec_bne_taken (by rw [hbt0, reg_zero]; exact ofNat_succ_ne_zero r (by omega)))
        have hpcc : mc.pc = after pc (3 + 3) := by
          show mb.pc + branchOffset 4 = _
          simp only [mb, next_pc, setReg_pc, hpca, after_succ, branchOffset_four]
          rw [show (3 + 3 : Nat) = (3 + 1) + 2 from rfl, ← after_after pc (3 + 1) 2]
          rfl
        let md := (mc.setReg (tmp 0) (mc.reg (tmp 0) + sext12 (-1))).next
        have hsc : step t.platform mc = some md :=
          step_of (by simp only [mc, mb, next_imem, setReg_imem, him]; exact hhead' 3 (by omega))
            hpcc (aligned_after ha _) rfl
        have hdt0 : md.reg (tmp 0) = .ofNat 32 r := by
          simp only [md, next_reg, reg_setReg_self _ _ _ (tmp_ne_zero (d := 0) (by omega))]
          show mb.reg (tmp 0) + _ = _
          rw [hbt0, ofNat_succ_sub_one]
        have hdgp : md.reg gp = base := by
          simp only [md, next_reg, reg_setReg_other _ _ _ _ tmp0_ne_gp.symm]
          change (ma.setReg (tmp 0) (ma.dmem ctr)).reg gp = base
          rw [reg_setReg_other _ _ _ _ tmp0_ne_gp.symm, hinva.gp]
        have hdc : md.reg gp + sext12 (slot (g + k)) = ctr := by
          rw [hdgp, sext12_slot (by omega)]; rfl
        let me : Machine :=
          { md.next with dmem := fun x => if x = ctr then md.reg (tmp 0) else md.dmem x }
        have hsd : step t.platform md = some me :=
          step_of (by simp only [md, mc, mb, next_imem, setReg_imem, him]; exact hhead' 4 (by omega))
            (by simp only [md, next_pc, setReg_pc, hpcc, after_succ]) (aligned_after ha _)
            (exec_sw_ram hdc hctr_al hctr_ram)
        have hdm : md.dmem = ma.dmem := by simp [md, mc, mb]
        have hinve : Inv base g me sta := by
          refine ⟨hdgp, fun i hi => ?_, by simp [me, md, mc, mb, hinva.trace]⟩
          simp only [me]
          rw [ite_neg (slot_ne (by omega) (by omega) (by omega)), hdm]
          exact hinva.vars i hi
        have hime : me.imem = m.imem := by simp [me, md, mc, mb, him]
        -- The body.
        obtain ⟨mf, hsf, hpcf, hinvf, hif, hkf⟩ :=
          ih (k + 1) me sta (after pc 8) hwb (by omega) (by omega)
            (by rw [hime]; exact hcb) (by simp only [me, md, next_pc, setReg_pc, hpcc, after_succ])
            (aligned_after ha _) hinve
        rw [hlb, after_after] at hpcf
        have hctrf : mf.dmem ctr = .ofNat 32 r := by
          rw [show ctr = after base (g + k) from rfl, hkf k (by omega)]
          simp only [me, ↓reduceIte, ctr, hdt0]
        -- Jump back to the loop head.
        let mg : Machine :=
          { mf with pc := mf.pc + jumpOffset (jumpBy (-((lb : Int) + 5))) }
        have hsg : step t.platform mf = some mg :=
          step_of (by rw [hif, hime]; simpa [after_after] using CodeAt.single.mp hback) hpcf
            (aligned_after ha _) (exec_jal_zero _ _)
        have hpcg : mg.pc = after pc 3 := by
          simp only [mg, hpcf]
          rw [show (8 + lb : Nat) = 3 + (lb + 5) by omega, ← after_after]
          unfold after
          rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 _),
            jumpOffset_back_int (n := lb + 5) (by omega) (by omega)]
          simp
        obtain ⟨mh, hsh, hpch, hinvh, hih, hkh⟩ :=
          ihr (by omega) mg (body.run sta) (by show mf.imem = m.imem; rw [hif, hime]) hpcg hctrf
            (hinvf.withPc _)
        have hpre : Star t.platform ma me := .step hsa (.step hsb (.step hsc (.single hsd)))
        have hpost : Star t.platform mf mh := .step hsg hsh
        refine ⟨mh, (hpre.trans hsf).trans hpost, hpch, ?_, ?_, ?_⟩
        · rw [Nat.repeat_succ']; exact hinvh
        · exact hih.trans (hif.trans (hime.trans him.symm))
        · intro j hj
          rw [hkh j hj]
          simp only [mg]
          rw [hkf j (by omega)]
          simp only [me]
          rw [ite_neg (slot_ne (by omega) (by omega) (by omega)), hdm]
    obtain ⟨m3, hs3, hpc3, hinv3, hi3, hk3⟩ :=
      hloop cnt (Nat.le_refl _) m2 st (by simp [m2, hi1])
        (by simp only [m2, next_pc, hpc1, after_succ])
        (by show (if ctr = ctr then m1.reg (tmp 0) else m1.dmem ctr) = _
            simp only [↓reduceIte]; exact hr1)
        hinv2
    refine ⟨m3, (hs1.trans (.single hs2)).trans hs3, by rw [hpc3], ?_, ?_, ?_⟩
    · exact hinv3
    · exact hi3.trans hi1
    · intro j hj
      rw [hk3 j hj]
      simp only [m2]
      rw [ite_neg (slot_ne (by omega) (by omega) (by omega)), hd1]

end VerifiedFw.Compiler
