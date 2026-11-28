import C3BootProofs.Proof.Code

/-!
# One instruction at a time

`St M base m off f` says the machine `m` is at offset `off` of the code at
`base`, its memory is `M`, and `f` gives every register's value. Each lemma
here runs one instruction of a given kind and returns the next machine with
its `St`. The register file stays a symbolic function, so `simp` can
evaluate it at concrete registers; a store changes `M` to the stored memory.
-/

namespace C3.RV32

/-- A register file with `rd` set to `v`, as `writeReg` sets it. -/
def upd (f : Fin 32 → Word) (rd : Fin 32) (v : Word) : Fin 32 → Word :=
  fun r => if r.val = 0 then 0 else if r = rd then v else f r

theorem add_ofNat_zero (a : Word) : a + BitVec.ofNat 32 0 = a := BitVec.add_zero a

/-- Memory `M` holds `code` from `base`. -/
abbrev CodeIn (M : Word → BitVec 8) (base : Word) (code : List Nat) : Prop :=
  ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i

/-- `M` with byte `a` set to `v`, as `store8` sets it. -/
def memStore8 (M : Word → BitVec 8) (a : Word) (v : BitVec 8) : Word → BitVec 8 :=
  fun x => if x = a then v else M x

/-- `M` with the little-endian word at `a` set to `v`, as `store32` sets it. -/
def memStore32 (M : Word → BitVec 8) (a v : Word) : Word → BitVec 8 :=
  memStore8 (memStore8 (memStore8 (memStore8 M a (v.extractLsb' 0 8)) (a + 1) (v.extractLsb' 8 8))
    (a + 2) (v.extractLsb' 16 8)) (a + 3) (v.extractLsb' 24 8)

/-- The little-endian word at `a` in `M`, as `load32` reads it. -/
def memLoad32 (M : Word → BitVec 8) (a : Word) : Word := M (a + 3) ++ M (a + 2) ++ M (a + 1) ++ M a

/-- No byte of the `n` bytes at `a` is one of the `k` bytes at `b`. -/
def Sep (a : Word) (n : Nat) (b : Word) (k : Nat) : Prop :=
  ∀ i, i < n → ∀ j, j < k → a + BitVec.ofNat 32 i ≠ b + BitVec.ofNat 32 j

theorem CodeIn.store8 {M : Word → BitVec 8} {base a : Word} {code : List Nat} {v : BitVec 8}
    (hc : CodeIn M base code) (h : Sep a 1 base code.length) :
    CodeIn (memStore8 M a v) base code := by
  intro i hi
  unfold memStore8
  have hne : base + BitVec.ofNat 32 i ≠ a := by
    have := h 0 (by decide) i hi
    rw [add_ofNat_zero] at this
    exact fun e => this e.symm
  rw [ite_eq_right hne]
  exact hc i hi

theorem Sep.shift {a b : Word} {n k : Nat} (h : Sep a n b k) {c : Nat} (hc : c < n) :
    Sep (a + BitVec.ofNat 32 c) 1 b k := by
  intro i hi j hj
  have : i = 0 := by omega
  subst this
  rw [add_ofNat_zero]
  exact h c hc j hj

theorem CodeIn.store32 {M : Word → BitVec 8} {base a v : Word} {code : List Nat}
    (hc : CodeIn M base code) (h : Sep a 4 base code.length) :
    CodeIn (memStore32 M a v) base code := by
  unfold memStore32
  have h0 : Sep a 1 base code.length := by
    have := h.shift (c := 0) (by decide)
    rwa [add_ofNat_zero] at this
  exact ((((hc.store8 h0).store8 (h.shift (c := 1) (by decide))).store8
    (h.shift (c := 2) (by decide))).store8 (h.shift (c := 3) (by decide)))

/-- The machine is at offset `off` of the code at `base`, its memory is
`M`, and `f` gives every register's value. -/
structure St (M : Word → BitVec 8) (base : Word) (m : Machine) (off : Nat)
    (f : Fin 32 → Word) : Prop where
  pc : m.pc = base + BitVec.ofNat 32 off
  mem : m.mem = M
  regs : ∀ r, reg m r = f r

section Step

variable {M : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine} {off : Nat}
  {f : Fin 32 → Word}

theorem St.codeAt (s : St M base m off f) (hc : ∀ i, i < code.length →
    M (base + BitVec.ofNat 32 i) = byteAt code i) : CodeAt m base code := by
  intro i hi; rw [s.mem]; exact hc i hi

theorem St.write {v : Word} {rd : Fin 32} {off' : Nat} {len : Word} (s : St M base m off f)
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    St M base (Arch.setPc (writeReg m rd v) (m.pc + len)) off' (upd f rd v) where
  pc := by simp only [Machine.setPc_pc]; rw [s.pc, BitVec.add_assoc, hn]
  mem := by simp [s.mem]
  regs r := by simp only [reg_setPc, reg_writeReg, upd, s.regs]

theorem St.aluImm (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {op : AluOp} {rd rs1 : Fin 32} {imm len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.aluImm op rd rs1 imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧ St M base m1 off' (upd f rd (aluEval op (f rs1) imm)) := by
  refine ⟨_, ?_, s.write (v := aluEval op (f rs1) imm) (rd := rd) hn⟩
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1]; rfl

theorem St.alu (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {op : AluOp} {rd rs1 rs2 : Fin 32} {len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.alu op rd rs1 rs2, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧ St M base m1 off' (upd f rd (aluEval op (f rs1) (f rs2))) := by
  refine ⟨_, ?_, s.write (v := aluEval op (f rs1) (f rs2)) (rd := rd) hn⟩
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1, ← s.regs rs2]; rfl

theorem St.lui (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rd : Fin 32} {imm len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.lui rd imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧ St M base m1 off' (upd f rd imm) := by
  refine ⟨_, ?_, s.write (v := imm) (rd := rd) hn⟩
  rw [step_code (s.codeAt hc) s.pc hf]; rfl

theorem St.lbu (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rd rs1 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.load .lbu rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧
      St M base m1 off' (upd f rd ((M (f rs1 + o)).zeroExtend 32)) := by
  refine ⟨_, ?_, s.write (v := (M (f rs1 + o)).zeroExtend 32) (rd := rd) hn⟩
  have ha : aligned (loadSize .lbu) (reg m rs1 + o) = true := by
    unfold aligned loadSize; rw [Nat.mod_one]; rfl
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1, ← s.mem]
  unfold exec
  simp only [ha, Bool.not_true]
  rfl

theorem St.stepBranch (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {op : BranchOp} {rs1 rs2 : Fin 32} {o len : Word}
    (hf : fetchRel code off = some (.branch op rs1 rs2 o, len)) :
    step m = some (Arch.setPc m
      (if branchTaken op (f rs1) (f rs2) then m.pc + o else m.pc + len)) := by
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1, ← s.regs rs2]; rfl

theorem St.lw (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rd rs1 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.load .lw rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off')
    (hal : (f rs1 + o).toNat % 4 = 0) :
    ∃ m1, step m = some m1 ∧ St M base m1 off' (upd f rd (memLoad32 M (f rs1 + o))) := by
  refine ⟨_, ?_, s.write (v := memLoad32 M (f rs1 + o)) (rd := rd) hn⟩
  have ha : aligned (loadSize .lw) (reg m rs1 + o) = true := by
    unfold aligned loadSize; rw [s.regs, hal]; rfl
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1, ← s.mem]
  unfold exec
  simp only [ha, Bool.not_true]
  rfl

theorem St.sw (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rs1 rs2 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.store .sw rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off')
    (hal : (f rs1 + o).toNat % 4 = 0) :
    ∃ m1, step m = some m1 ∧ St (memStore32 M (f rs1 + o) (f rs2)) base m1 off' f := by
  have ha : aligned (storeSize .sw) (reg m rs1 + o) = true := by
    unfold aligned storeSize; rw [s.regs, hal]; rfl
  refine ⟨Arch.setPc (store32 m (f rs1 + o) (f rs2)) (m.pc + len), ?_, ?_, ?_, ?_⟩
  · rw [step_code (s.codeAt hc) s.pc hf]
    unfold exec
    simp only [ha, Bool.not_true]
    rw [s.regs, s.regs]
    rfl
  · simp only [Machine.setPc_pc]; rw [s.pc, BitVec.add_assoc, hn]
  · rw [← s.mem]; rfl
  · intro r; rw [← s.regs r]; rfl

theorem St.sb (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rs1 rs2 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.store .sb rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧
      St (memStore8 M (f rs1 + o) ((f rs2).extractLsb' 0 8)) base m1 off' f := by
  have ha : aligned (storeSize .sb) (reg m rs1 + o) = true := by
    unfold aligned storeSize; rw [Nat.mod_one]; rfl
  refine ⟨Arch.setPc (store8 m (f rs1 + o) ((f rs2).extractLsb' 0 8)) (m.pc + len),
    ?_, ?_, ?_, ?_⟩
  · rw [step_code (s.codeAt hc) s.pc hf]
    unfold exec
    simp only [ha, Bool.not_true]
    rw [s.regs, s.regs]
    rfl
  · simp only [Machine.setPc_pc]; rw [s.pc, BitVec.add_assoc, hn]
  · rw [← s.mem]; rfl
  · intro r; rw [← s.regs r]; rfl

theorem St.auipc (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rd : Fin 32} {imm len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.auipc rd imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧ St M base m1 off' (upd f rd (base + BitVec.ofNat 32 off + imm)) := by
  refine ⟨_, ?_, s.write (v := base + BitVec.ofNat 32 off + imm) (rd := rd) hn⟩
  rw [step_code (s.codeAt hc) s.pc hf, ← s.pc]; rfl

theorem St.jump (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {o len : Word} {off' : Nat} (hf : fetchRel code off = some (.jal 0 o, len))
    (hn : BitVec.ofNat 32 off + o = BitVec.ofNat 32 off') (heven : (m.pc + o).getLsbD 0 = false) :
    ∃ m1, step m = some m1 ∧ St M base m1 off' f := by
  have hz : writeReg m 0 (m.pc + len) = m := by unfold writeReg; simp
  refine ⟨Arch.setPc m (m.pc + o), ?_, ?_, by simp [s.mem], fun r => by simp only [reg_setPc, s.regs]⟩
  · rw [step_code (s.codeAt hc) s.pc hf]
    unfold exec
    simp only [Machine.getPc_eq, heven, Bool.false_eq_true, ite_false, hz]
    rfl
  · simp only [Machine.setPc_pc]; rw [s.pc, BitVec.add_assoc, hn]

/-- A call: `jalr rd, o(rs1)` links `rd` and leaves the code. -/
theorem St.call (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rd rs1 : Fin 32} {o len : Word} (hf : fetchRel code off = some (.jalr rd rs1 o, len)) :
    ∃ m1, step m = some m1 ∧ m1.pc = (f rs1 + o) &&& ~~~1 ∧ m1.mem = M ∧
      ∀ r, reg m1 r = upd f rd (base + BitVec.ofNat 32 off + len) r := by
  refine ⟨Arch.setPc (writeReg m rd (m.pc + len)) ((f rs1 + o) &&& ~~~1), ?_, rfl,
    by simp [s.mem], fun r => ?_⟩
  · rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1]; rfl
  · simp only [reg_setPc, reg_writeReg, upd, s.regs, s.pc]

theorem St.taken (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {op : BranchOp} {rs1 rs2 : Fin 32} {o len : Word} (offT : Nat)
    (hf : fetchRel code off = some (.branch op rs1 rs2 o, len))
    (hT : BitVec.ofNat 32 off + o = BitVec.ofNat 32 offT)
    (hb : branchTaken op (f rs1) (f rs2) = true) :
    ∃ m1, step m = some m1 ∧ St M base m1 offT f := by
  have h := s.stepBranch hc hf
  rw [hb, ite_eq_left rfl] at h
  refine ⟨_, h, ?_, by simp [s.mem], fun r => by simp only [reg_setPc, s.regs]⟩
  simp only [Machine.setPc_pc]; rw [s.pc, BitVec.add_assoc, hT]

theorem St.notTaken (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {op : BranchOp} {rs1 rs2 : Fin 32} {o len : Word} (offF : Nat)
    (hf : fetchRel code off = some (.branch op rs1 rs2 o, len))
    (hF : BitVec.ofNat 32 off + len = BitVec.ofNat 32 offF)
    (hb : branchTaken op (f rs1) (f rs2) = false) :
    ∃ m1, step m = some m1 ∧ St M base m1 offF f := by
  have h := s.stepBranch hc hf
  rw [hb] at h
  refine ⟨_, h, ?_, by simp [s.mem], fun r => by simp only [reg_setPc, s.regs]⟩
  simp only [Machine.setPc_pc, Bool.false_eq_true, ite_false]; rw [s.pc, BitVec.add_assoc, hF]

theorem St.self (s : St M base m off f) : St M base m off (reg m) :=
  ⟨s.pc, s.mem, fun _ => rfl⟩

theorem St.zero (s : St M base m off f) : f 0 = 0 := by
  rw [← s.regs]; rfl

theorem St.jalr (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rs1 : Fin 32} {o len : Word} (hf : fetchRel code off = some (.jalr 0 rs1 o, len)) :
    ∃ m1, step m = some m1 ∧ m1.pc = (f rs1 + o) &&& ~~~1 ∧ m1.mem = M ∧
      ∀ r, reg m1 r = f r := by
  refine ⟨Arch.setPc m ((f rs1 + o) &&& ~~~1), ?_, rfl, by simp [s.mem],
    fun r => by simp only [reg_setPc, s.regs]⟩
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1]
  simp [exec, writeReg]

end Step

@[simp] theorem upd_zero (f : Fin 32 → Word) (rd : Fin 32) (v : Word) : upd f rd v 0 = 0 := rfl

end C3.RV32
