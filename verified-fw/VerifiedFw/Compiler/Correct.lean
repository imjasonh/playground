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

end VerifiedFw.Compiler
