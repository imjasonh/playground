import C3BootProofs.Proofs.LeafStep

/-!
# The eFuse command runner, as compiled

`efuse::program::run(op_code, cmd)` writes `op_code` to the controller's
`CONF` register at 0x600089CC and `cmd` to its `CMD` register at
0x600089D4, then reads `CMD` up to 1,000,000 times and returns `true` once
`CMD & cmd` is 0, or `false` when the polls run out.

The machine model has plain memory and no eFuse controller, so a read of
`CMD` returns the last value written there. `efuseProgramRun_correct` pins
the two register writes, the poll bound, and the result: `true` when `cmd`
is 0, and `false` after the last poll otherwise. On hardware the controller
clears `CMD` when the command finishes; the model doesn't say when.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem epr_at_0 : fetchRel efuseProgramRunCode 0x0 = some (.lui a2 0x60009000, 4) := by decide
theorem epr_at_4 : fetchRel efuseProgramRunCode 0x4 = some (.store .sw a2 a0 0xFFFFF9CC, 4) := by decide
theorem epr_at_8 : fetchRel efuseProgramRunCode 0x8 = some (.store .sw a2 a1 0xFFFFF9D4, 4) := by decide
theorem epr_at_c : fetchRel efuseProgramRunCode 0xC = some (.aluImm .add a0 x0 0xFFFFFFFF, 2) := by decide
theorem epr_at_e : fetchRel efuseProgramRunCode 0xE = some (.lui a4 0xF4000, 4) := by decide
theorem epr_at_12 : fetchRel efuseProgramRunCode 0x12 = some (.aluImm .add a3 a4 0x240, 4) := by decide
theorem epr_at_16 : fetchRel efuseProgramRunCode 0x16 = some (.aluImm .add a4 a4 0x23F, 4) := by decide
theorem epr_at_1a : fetchRel efuseProgramRunCode 0x1A = some (.branch .beq a0 a4 0x10, 4) := by decide
theorem epr_at_1e : fetchRel efuseProgramRunCode 0x1E = some (.load .lw a5 a2 0xFFFFF9D4, 4) := by decide
theorem epr_at_22 : fetchRel efuseProgramRunCode 0x22 = some (.alu .and a5 a5 a1, 2) := by decide
theorem epr_at_24 : fetchRel efuseProgramRunCode 0x24 = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem epr_at_26 : fetchRel efuseProgramRunCode 0x26 = some (.branch .bne a5 x0 0xFFFFFFF4, 2) := by decide
theorem epr_at_28 : fetchRel efuseProgramRunCode 0x28 = some (.jal x0 0x4, 2) := by decide
theorem epr_at_2a : fetchRel efuseProgramRunCode 0x2A = some (.alu .add a0 x0 a3, 2) := by decide
theorem epr_at_2c : fetchRel efuseProgramRunCode 0x2C = some (.lui a1 0xF4000, 4) := by decide
theorem epr_at_30 : fetchRel efuseProgramRunCode 0x30 = some (.aluImm .add a1 a1 0x240, 4) := by decide
theorem epr_at_34 : fetchRel efuseProgramRunCode 0x34 = some (.alu .sltu a0 a0 a1, 4) := by decide
theorem epr_at_38 : fetchRel efuseProgramRunCode 0x38 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The registers `efuse::program::run` keeps: all but `a0` through `a5`. -/
def erKeep (q : Fin 32) : Bool := q.val < 10 || 15 < q.val

/-- **The compiled `efuse::program::run`**: called with an op code in `a0`
and a command in `a1`, it writes the op code to 0x600089CC and the command
to 0x600089D4, and returns 1 in `a0` when the command is 0 and 0 otherwise.
It writes no other memory and only `a0` through `a5`. -/
theorem efuseProgramRun_correct (m : Machine) {base retAddr op cmd : Word}
    (hc : CodeIn m.mem base efuseProgramRunCode) (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = op) (ha1 : reg m a1 = cmd) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (sCF : Sep 0x600089CC 4 base efuseProgramRunCode.length)
    (sCM : Sep 0x600089D4 4 base efuseProgramRunCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = memStore32 (memStore32 m.mem 0x600089CC op) 0x600089D4 cmd ∧
      reg m' a0 = (if cmd = 0 then 1 else 0) ∧ ∀ q, erKeep q = true → reg m' q = reg m q := by
  obtain ⟨M, hM⟩ : ∃ M, memStore32 (memStore32 m.mem 0x600089CC op) 0x600089D4 cmd = M := ⟨_, rfl⟩
  rw [hM]
  have hcM : CodeIn M base efuseProgramRunCode := by rw [← hM]; exact (hc.store32 sCF).store32 sCM
  have hld : memLoad32 M 0x600089D4 = cmd := by rw [← hM]; exact memLoad32_store32_same _ _ _
  -- the exit, from 0x2C: `a0 < 1_000_000`
  have exitP : ∀ {n : Machine} (y : Word), St M base n 0x2C (reg n) → reg n a0 = y →
      (∀ q, erKeep q = true → reg n q = reg m q) →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = M ∧ reg n' a0 = aluEval .sltu y 0xF4240 ∧
        ∀ q, erKeep q = true → reg n' q = reg m q := by
    intro n y st h0 kk
    obtain ⟨n1, d1, u1⟩ := st.lui hcM epr_at_2c (off' := 0x30) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hcM epr_at_30 (off' := 0x34) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.self.alu hcM epr_at_34 (off' := 0x38) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.self.jalr hcM epr_at_38
    have k1 := ls_kst u1 (by decide) kk
    have k2 := ls_kst u2 (by decide) k1
    have k3 := ls_kst u3 (by decide) k2
    refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), ?_, mem4, ?_,
      fun q hq => by rw [regs4]; exact k3 q hq⟩
    · rw [pc4, k3 ra (by decide), hra, add_lit_zero, hret]
    · rw [regs4, ls_get u3 (by decide), ls_get u2 (by decide), ls_oth u2 (show a0 ≠ a1 by decide),
        ls_get u1 (by decide), ls_oth u1 (show a0 ≠ a1 by decide), h0]
      rfl
  -- one poll, from the loop head at 0x1A to the branch at 0x26
  have body : ∀ {n : Machine} (x : Word), St M base n 0x1A (reg n) → reg n a0 = x → reg n a1 = cmd →
      reg n a2 = 0x60009000 → reg n a3 = 0xF4240 → reg n a4 = 0xF423F →
      (∀ q, erKeep q = true → reg n q = reg m q) → x ≠ 0xF423F →
      ∃ n', Steps n n' ∧ St M base n' 0x26 (reg n') ∧ reg n' a0 = x + 1 ∧ reg n' a5 = cmd ∧
        reg n' a1 = cmd ∧ reg n' a2 = 0x60009000 ∧ reg n' a3 = 0xF4240 ∧ reg n' a4 = 0xF423F ∧
        ∀ q, erKeep q = true → reg n' q = reg m q := by
    intro n x st h0 h1 h2 h3 h4 kk hx
    obtain ⟨n1, d1, u1⟩ := st.notTaken hcM 0x1E epr_at_1a (by decide) (by
      rw [h0, h4]; exact beq_false_of_ne hx)
    obtain ⟨n2, d2, u2⟩ := u1.lw hcM epr_at_1e (off' := 0x22) (by decide) (by rw [h2]; decide)
    rw [h2, show (0x60009000 : Word) + 0xFFFFF9D4 = 0x600089D4 by decide, hld] at u2
    obtain ⟨n3, d3, u3⟩ := u2.self.alu hcM epr_at_22 (off' := 0x24) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hcM epr_at_24 (off' := 0x26) (by decide)
    have k := ls_kst u4 (by decide) (ls_kst u3 (by decide) (ls_kst u2 (by decide) kk))
    refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), u4.self, ?_, ?_, ?_, ?_, ?_, ?_, k⟩
    · rw [ls_get u4 (by decide), ls_oth u3 (show a0 ≠ a5 by decide), ls_oth u2 (show a0 ≠ a5 by decide), h0]
      rfl
    · rw [ls_oth u4 (show a5 ≠ a0 by decide), ls_get u3 (by decide), ls_get u2 (by decide),
        ls_oth u2 (show a1 ≠ a5 by decide), h1]
      exact BitVec.and_self
    · rw [ls_oth u4 (show a1 ≠ a0 by decide), ls_oth u3 (show a1 ≠ a5 by decide),
        ls_oth u2 (show a1 ≠ a5 by decide), h1]
    · rw [ls_oth u4 (show a2 ≠ a0 by decide), ls_oth u3 (show a2 ≠ a5 by decide),
        ls_oth u2 (show a2 ≠ a5 by decide), h2]
    · rw [ls_oth u4 (show a3 ≠ a0 by decide), ls_oth u3 (show a3 ≠ a5 by decide),
        ls_oth u2 (show a3 ≠ a5 by decide), h3]
    · rw [ls_oth u4 (show a4 ≠ a0 by decide), ls_oth u3 (show a4 ≠ a5 by decide),
        ls_oth u2 (show a4 ≠ a5 by decide), h4]
  -- the last poll: `a0` reached 999,999, so `a0` becomes 1,000,000
  have timeout : ∀ {n : Machine}, St M base n 0x1A (reg n) → reg n a0 = 0xF423F → reg n a3 = 0xF4240 →
      reg n a4 = 0xF423F → (∀ q, erKeep q = true → reg n q = reg m q) →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = M ∧ reg n' a0 = 0 ∧
        ∀ q, erKeep q = true → reg n' q = reg m q := by
    intro n st h0 h3 h4 kk
    obtain ⟨n1, d1, u1⟩ := st.taken hcM 0x2A epr_at_1a (by decide) (by rw [h0, h4]; exact beq_iff_eq.mpr rfl)
    obtain ⟨n2, d2, u2⟩ := u1.alu hcM epr_at_2a (off' := 0x2C) (by decide)
    obtain ⟨n', c', pc', mem', a0', k'⟩ := exitP 0xF4240 u2.self
      (by rw [ls_get u2 (by decide), ls_r0, h3]; rfl) (ls_kst u2 (by decide) kk)
    exact ⟨n', .cons d1 (.cons d2 c'), pc', mem', by rw [a0']; rfl, k'⟩
  -- the polls with a nonzero command
  have loop : ∀ (d j : Nat) {n : Machine}, j + d = 0xF423F → cmd ≠ 0 → St M base n 0x1A (reg n) →
      reg n a0 = BitVec.ofNat 32 j → reg n a1 = cmd → reg n a2 = 0x60009000 → reg n a3 = 0xF4240 →
      reg n a4 = 0xF423F → (∀ q, erKeep q = true → reg n q = reg m q) →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = M ∧ reg n' a0 = 0 ∧
        ∀ q, erKeep q = true → reg n' q = reg m q := by
    intro d
    induction d with
    | zero =>
      intro j n hj _ st h0 _ _ h3 h4 kk
      exact timeout st (by rw [h0, show j = 0xF423F by omega]; rfl) h3 h4 kk
    | succ d ih =>
      intro j n hj hcmd st h0 h1 h2 h3 h4 kk
      have hx : BitVec.ofNat 32 j ≠ 0xF423F := fun e => by
        have := congrArg BitVec.toNat e
        rw [ls_ofNat_toNat_lt (by omega)] at this
        have h' : (0xF423F : Word).toNat = 0xF423F := rfl
        omega
      obtain ⟨n1, c1, u1, a01, a51, a11, a21, a31, a41, k1⟩ := body _ st h0 h1 h2 h3 h4 kk hx
      obtain ⟨n2, d2, u2⟩ := u1.taken hcM 0x1A epr_at_26 (by decide) (by
        rw [a51, ls_r0]; exact bne_iff_ne.mpr hcmd)
      obtain ⟨n', c', h'⟩ := ih (j + 1) (by omega) hcmd u2.self
        (by rw [u2.regs, a01]; exact ofNat_add_ofNat j 1) (by rw [u2.regs, a11]) (by rw [u2.regs, a21])
        (by rw [u2.regs, a31]) (by rw [u2.regs, a41]) (fun q hq => by rw [u2.regs]; exact k1 q hq)
      exact ⟨n', c1.trans (.cons d2 c'), h'⟩
  -- the prologue
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have kk0 : ∀ q, erKeep q = true → reg m q = reg m q := fun _ _ => rfl
  obtain ⟨n1, d1, u1⟩ := s0.lui hc epr_at_0 (off' := 4) (by decide)
  have k1 := ls_kst u1 (by decide) kk0
  obtain ⟨n2, d2, u2⟩ := u1.self.sw hc epr_at_4 (off' := 8) (by decide) (by rw [ls_get u1 (by decide)]; decide)
  rw [ls_get u1 (by decide), ls_oth u1 (show a0 ≠ a2 by decide), ha0,
    show (0x60009000 : Word) + 0xFFFFF9CC = 0x600089CC by decide] at u2
  obtain ⟨n3, d3, u3⟩ := u2.sw (hc.store32 sCF) epr_at_8 (off' := 0xC) (by decide)
    (by rw [ls_get u1 (by decide)]; decide)
  rw [ls_get u1 (by decide), ls_oth u1 (show a1 ≠ a2 by decide), ha1,
    show (0x60009000 : Word) + 0xFFFFF9D4 = 0x600089D4 by decide, hM] at u3
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hcM epr_at_c (off' := 0xE) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.lui hcM epr_at_e (off' := 0x12) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.aluImm hcM epr_at_12 (off' := 0x16) (by decide)
  obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hcM epr_at_16 (off' := 0x1A) (by decide)
  have k4 := ls_kst u4 (by decide) k1
  have k7 := ls_kst u7 (by decide) (ls_kst u6 (by decide) (ls_kst u5 (by decide) k4))
  have a07 : reg n7 a0 = 0xFFFFFFFF := by
    rw [ls_oth u7 (show a0 ≠ a4 by decide), ls_oth u6 (show a0 ≠ a3 by decide),
      ls_oth u5 (show a0 ≠ a4 by decide), ls_get u4 (by decide), ls_r0]
    rfl
  have a17 : reg n7 a1 = cmd := by
    rw [ls_oth u7 (show a1 ≠ a4 by decide), ls_oth u6 (show a1 ≠ a3 by decide),
      ls_oth u5 (show a1 ≠ a4 by decide), ls_oth u4 (show a1 ≠ a0 by decide), ls_oth u1 (show a1 ≠ a2 by decide), ha1]
  have a27 : reg n7 a2 = 0x60009000 := by
    rw [ls_oth u7 (show a2 ≠ a4 by decide), ls_oth u6 (show a2 ≠ a3 by decide),
      ls_oth u5 (show a2 ≠ a4 by decide), ls_oth u4 (show a2 ≠ a0 by decide), ls_get u1 (by decide)]
  have a37 : reg n7 a3 = 0xF4240 := by
    rw [ls_oth u7 (show a3 ≠ a4 by decide), ls_get u6 (by decide), ls_get u5 (by decide)]
    rfl
  have a47 : reg n7 a4 = 0xF423F := by
    rw [ls_get u7 (by decide), ls_oth u6 (show a4 ≠ a3 by decide), ls_get u5 (by decide)]
    rfl
  -- the first poll, with `a0 = -1`
  obtain ⟨n8, c8, u8, a08, a58, a18, a28, a38, a48, k8⟩ :=
    body _ u7.self a07 a17 a27 a37 a47 k7 (by decide)
  have pre : Steps m n8 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c8))))))
  by_cases hcmd : cmd = 0
  · obtain ⟨n9, d9, u9⟩ := u8.notTaken hcM 0x28 epr_at_26 (by decide) (by
      rw [a58, ls_r0, hcmd]; rfl)
    obtain ⟨n10, d10, u10⟩ := u9.jump hcM epr_at_28 (off' := 0x2C) (by decide) (by
      rw [u9.pc]; exact ls_even hbase 0x28 0x4 0x2C (by decide) (by decide))
    obtain ⟨n', c', pc', mem', a0', k'⟩ := exitP 0 u10.self (by rw [u10.regs, a08]; rfl)
      (fun q hq => by rw [u10.regs]; exact k8 q hq)
    exact ⟨n', pre.trans (.cons d9 (.cons d10 c')), pc', mem', by rw [a0', if_pos hcmd]; rfl, k'⟩
  · obtain ⟨n9, d9, u9⟩ := u8.taken hcM 0x1A epr_at_26 (by decide) (by
      rw [a58, ls_r0]; exact bne_iff_ne.mpr hcmd)
    obtain ⟨n', c', pc', mem', a0', k'⟩ := loop 0xF423F 0 (by decide) hcmd u9.self
      (by rw [u9.regs, a08]; rfl) (by rw [u9.regs, a18]) (by rw [u9.regs, a28])
      (by rw [u9.regs, a38]) (by rw [u9.regs, a48]) (fun q hq => by rw [u9.regs]; exact k8 q hq)
    exact ⟨n', pre.trans (.cons d9 c'), pc', mem', by rw [a0', if_neg hcmd], k'⟩

end C3.RV32
