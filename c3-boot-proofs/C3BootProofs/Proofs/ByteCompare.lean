import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.DerTlv

/-!
# `less_than_le` and `in_scalar_range`, as compiled

`c3_crypto::less_than_le` compares two 32-byte little-endian numbers from
the top byte down, and `c3_crypto::ecdsa::in_scalar_range` checks that a
big-endian scalar is nonzero and below the group order. Both decide at the
first byte that differs.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem ltl_at_0 : fetchRel lessThanLeCode 0x0 = some (.aluImm .add a0 a0 0x1F, 2) := by decide
theorem ltl_at_2 : fetchRel lessThanLeCode 0x2 = some (.aluImm .add a1 a1 0x1F, 2) := by decide
theorem ltl_at_4 : fetchRel lessThanLeCode 0x4 = some (.aluImm .add a2 x0 0xFFFFFFE0, 2) := by decide
theorem ltl_at_6 : fetchRel lessThanLeCode 0x6 = some (.branch .beq a2 x0 0x1A, 2) := by decide
theorem ltl_at_8 : fetchRel lessThanLeCode 0x8 = some (.load .lbu a3 a0 0x0, 4) := by decide
theorem ltl_at_c : fetchRel lessThanLeCode 0xC = some (.load .lbu a4 a1 0x0, 4) := by decide
theorem ltl_at_10 : fetchRel lessThanLeCode 0x10 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem ltl_at_12 : fetchRel lessThanLeCode 0x12 = some (.aluImm .add a2 a2 0x1, 2) := by decide
theorem ltl_at_14 : fetchRel lessThanLeCode 0x14 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem ltl_at_16 : fetchRel lessThanLeCode 0x16 = some (.branch .beq a3 a4 0xFFFFFFF0, 4) := by decide
theorem ltl_at_1a : fetchRel lessThanLeCode 0x1A = some (.alu .sltu a0 a3 a4, 4) := by decide
theorem ltl_at_1e : fetchRel lessThanLeCode 0x1E = some (.jalr x0 ra 0x0, 2) := by decide
theorem ltl_at_20 : fetchRel lessThanLeCode 0x20 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem ltl_at_22 : fetchRel lessThanLeCode 0x22 = some (.jalr x0 ra 0x0, 2) := by decide
theorem isr_at_0 : fetchRel inScalarRangeCode 0x0 = some (.branch .bne a1 a3 0x2A, 4) := by decide
theorem isr_at_4 : fetchRel inScalarRangeCode 0x4 = some (.alu .add a3 x0 a1, 2) := by decide
theorem isr_at_6 : fetchRel inScalarRangeCode 0x6 = some (.alu .add a4 x0 a0, 2) := by decide
theorem isr_at_8 : fetchRel inScalarRangeCode 0x8 = some (.branch .beq a3 x0 0x22, 2) := by decide
theorem isr_at_a : fetchRel inScalarRangeCode 0xA = some (.load .lbu a5 a4 0x0, 4) := by decide
theorem isr_at_e : fetchRel inScalarRangeCode 0xE = some (.aluImm .add a4 a4 0x1, 2) := by decide
theorem isr_at_10 : fetchRel inScalarRangeCode 0x10 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem isr_at_12 : fetchRel inScalarRangeCode 0x12 = some (.branch .beq a5 x0 0xFFFFFFF6, 2) := by decide
theorem isr_at_14 : fetchRel inScalarRangeCode 0x14 = some (.jal x0 0x14, 2) := by decide
theorem isr_at_16 : fetchRel inScalarRangeCode 0x16 = some (.load .lbu a3 a0 0x0, 4) := by decide
theorem isr_at_1a : fetchRel inScalarRangeCode 0x1A = some (.load .lbu a4 a2 0x0, 4) := by decide
theorem isr_at_1e : fetchRel inScalarRangeCode 0x1E = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem isr_at_20 : fetchRel inScalarRangeCode 0x20 = some (.aluImm .add a2 a2 0x1, 2) := by decide
theorem isr_at_22 : fetchRel inScalarRangeCode 0x22 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem isr_at_24 : fetchRel inScalarRangeCode 0x24 = some (.branch .bne a3 a4 0xA, 4) := by decide
theorem isr_at_28 : fetchRel inScalarRangeCode 0x28 = some (.branch .bne a1 x0 0xFFFFFFEE, 2) := by decide
theorem isr_at_2a : fetchRel inScalarRangeCode 0x2A = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem isr_at_2c : fetchRel inScalarRangeCode 0x2C = some (.jalr x0 ra 0x0, 2) := by decide
theorem isr_at_2e : fetchRel inScalarRangeCode 0x2E = some (.alu .sltu a0 a3 a4, 4) := by decide
theorem isr_at_32 : fetchRel inScalarRangeCode 0x32 = some (.jalr x0 ra 0x0, 2) := by decide
end
theorem bc_zext8_inj {x y : BitVec 8} (h : (x.zeroExtend 32 : Word) = y.zeroExtend 32) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega),
    Nat.mod_eq_of_lt (by have := y.isLt; omega)] at this

theorem beq_zext (x y : BitVec 8) : branchTaken .beq (x.zeroExtend 32) (y.zeroExtend 32) = decide (x = y) := by
  show (x.zeroExtend 32 == y.zeroExtend 32) = _
  by_cases h : x = y
  · subst h; rw [decide_eq_true rfl]; exact decide_eq_true rfl
  · rw [decide_eq_false h]; exact decide_eq_false (fun e => h (bc_zext8_inj e))

theorem sltu_zext (x y : BitVec 8) :
    aluEval .sltu (x.zeroExtend 32) (y.zeroExtend 32) = if x.toNat < y.toNat then 1 else 0 := by
  show (if BitVec.ult (x.zeroExtend 32) (y.zeroExtend 32) then (1 : Word) else 0) = _
  have hx := x.isLt; have hy := y.isLt
  have e : BitVec.ult (x.zeroExtend 32) (y.zeroExtend 32) = decide (x.toNat < y.toNat) := by
    simp only [BitVec.ult, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show x.toNat < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show y.toNat < 2 ^ 32 by omega)]
  rw [e]
  by_cases h : x.toNat < y.toNat
  · rw [decide_eq_true h, ite_eq_left h]; rfl
  · rw [decide_eq_false h, ite_eq_right h]; rfl

/-- Whether the `k` little-endian bytes at `a` are below those at `b`: the
top byte that differs decides, and equal numbers are not below. -/
def ltLE (M : Word → BitVec 8) (a b : Word) : Nat → Bool
  | 0 => false
  | k + 1 => if M (a + BitVec.ofNat 32 k) = M (b + BitVec.ofNat 32 k) then ltLE M a b k
      else decide ((M (a + BitVec.ofNat 32 k)).toNat < (M (b + BitVec.ofNat 32 k)).toNat)

/-- `less_than_le`'s loop body, from 0x8 to the branch at 0x16. -/
def ltlBody : List BInstr :=
  [.lbu a3 a0 0x0, .lbu a4 a1 0x0, .aluImm .add a0 a0 0xFFFFFFFF, .aluImm .add a2 a2 0x1,
   .aluImm .add a1 a1 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem ltlBody_end : blockEnd lessThanLeCode 0x8 ltlBody = some 0x16 := by decide
theorem ltlPre_end : blockEnd lessThanLeCode 0x0 [.aluImm .add a0 a0 0x1F, .aluImm .add a1 a1 0x1F,
    .aluImm .add a2 x0 0xFFFFFFE0] = some 0x6 := by decide
end

theorem ltl_dec_ofNat {k : Nat} (b : Word) : b + BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF = b + BitVec.ofNat 32 k := by
  have e : BitVec.ofNat 32 (k + 1) + (0xFFFFFFFF : Word) = BitVec.ofNat 32 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
    omega
  rw [BitVec.add_assoc, e]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `c3_crypto::less_than_le`**: 1 when the 32 little-endian
bytes at `a` are below those at `b`, and 0 otherwise. It writes no memory. -/
theorem lessThanLe_correct (m : Machine) {base retAddr a b : Word}
    (hc : CodeIn m.mem base lessThanLeCode) (hpc : m.pc = base) (ha0 : reg m a0 = a) (ha1 : reg m a1 = b)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if ltLE m.mem a b 32 then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have loop : ∀ k, k ≤ 32 → ∀ {n : Machine}, St m.mem base n 0x6 (reg n) →
      reg n a0 = a + BitVec.ofNat 32 k + 0xFFFFFFFF → reg n a1 = b + BitVec.ofNat 32 k + 0xFFFFFFFF →
      reg n a2 = BitVec.ofNat 32 (2 ^ 32 - k) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n r = reg m r) →
      ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if ltLE m.mem a b k then 1 else 0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
    intro k
    induction k with
    | zero =>
      intro _ n s r0 r1 r2 hk
      obtain ⟨n1, d1, u1⟩ := s.taken hc 0x20 ltl_at_6 (by decide) (by rw [r2, s.zero]; decide)
      obtain ⟨n2, d2, u2⟩ := u1.aluImm hc ltl_at_20 (off' := 0x22) (by decide)
      obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc ltl_at_22
      refine ⟨n3, .cons d1 (.cons d2 (.single d3)), ?_, ?_, fun r h0 h1 h2 h3 h4 => ?_, ?_⟩
      · rw [pc3, upd_ne (by decide) (by decide), hk ra (by decide) (by decide) (by decide) (by decide) (by decide),
          add_lit_zero, hra, hret]
      · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [s.zero]; rfl
      · rw [regs3, updz s.zero h0]; exact hk r h0 h1 h2 h3 h4
      · exact mem3
    | succ k ih =>
      intro hk32 n s r0 r1 r2 hk
      obtain ⟨n1, d1, u1⟩ := s.notTaken hc 0x8 ltl_at_6 (by decide) (by
        rw [r2, s.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat] at this; change _ = 0 at this; omega)
      obtain ⟨n2, c2, u2⟩ := St.block ltlBody u1 hc ltlBody_end (by simp [BlockOk, BInstr.ok, ltlBody])
      simp only [runBlock, BInstr.run, ltlBody] at u2
      have v3 : reg n2 a3 = (m.mem (a + BitVec.ofNat 32 k)).zeroExtend 32 := by
        rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, add_lit_zero, ltl_dec_ofNat]
      have v4 : reg n2 a4 = (m.mem (b + BitVec.ofNat 32 k)).zeroExtend 32 := by
        rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, add_lit_zero, ltl_dec_ofNat]
      have keep2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n2 r = reg m r :=
        fun r h0' h1' h2' h3' h4' => by
          rw [u2.regs]
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact hz.symm
          simp only [upd_app, h0, h0', h1', h2', h3', h4', ite_false]; exact hk r h0' h1' h2' h3' h4'
      by_cases he : m.mem (a + BitVec.ofNat 32 k) = m.mem (b + BitVec.ofNat 32 k)
      · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x6 ltl_at_16 (by decide) (by
          rw [v3, v4, beq_zext]; exact decide_eq_true he)
        obtain ⟨m', c', h1, h2, h3, h4⟩ := ih (by omega) u3.self
          (by rw [u3.regs, u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, ev_add, ltl_dec_ofNat])
          (by rw [u3.regs, u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, ev_add, ltl_dec_ofNat])
          (by
            rw [u3.regs, u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, ev_add]
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
            omega)
          (fun r h0' h1' h2' h3' h4' => by rw [u3.regs]; exact keep2 r h0' h1' h2' h3' h4')
        refine ⟨m', .cons d1 (c2.trans (.cons d3 c')), h1, ?_, h3, h4⟩
        rw [h2]; simp only [ltLE, he, ↓reduceIte]
      · obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x1A ltl_at_16 (by decide) (by
          rw [v3, v4, beq_zext]; exact decide_eq_false he)
        obtain ⟨n4, d4, u4⟩ := u3.self.alu hc ltl_at_1a (off' := 0x1E) (by decide)
        obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.jalr hc ltl_at_1e
        refine ⟨n5, .cons d1 (c2.trans (.cons d3 (.cons d4 (.single d5)))), ?_, ?_, fun r h0' h1' h2' h3' h4' => ?_, ?_⟩
        · rw [pc5, upd_ne (by decide) (by decide), u3.regs, keep2 ra (by decide) (by decide) (by decide) (by decide)
            (by decide), add_lit_zero, hra, hret]
        · rw [regs5]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.regs, u3.regs, v3, v4, sltu_zext]
          simp only [ltLE, he, ↓reduceIte]
          by_cases hl : (m.mem (a + BitVec.ofNat 32 k)).toNat < (m.mem (b + BitVec.ofNat 32 k)).toNat
          · rw [ite_eq_left hl, decide_eq_true hl]; rfl
          · rw [ite_eq_right hl, decide_eq_false hl]; rfl
        · rw [regs5, updz u3.self.zero h0', u3.regs]; exact keep2 r h0' h1' h2' h3' h4'
        · exact mem5
  obtain ⟨n1, c1, u1⟩ := St.block _ s0 hc ltlPre_end (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  obtain ⟨m', c', h1, h2, h3, h4⟩ := loop 32 (by decide) u1.self
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, ev_add, BitVec.add_assoc]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1, ev_add, BitVec.add_assoc]; rfl)
    (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte])
    (fun r h0' h1' h2' _ _ => by
      rw [u1.regs]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h0', h1', h2', ite_false])
  exact ⟨m', c1.trans c', h1, h2, h3, h4⟩

/-- Whether the big-endian bytes `x` are below `o`: the first byte that
differs decides, and equal strings are not below. -/
def bytesLtBE : Bytes → Bytes → Bool
  | x :: xs, o :: os => if x = o then bytesLtBE xs os else decide (x < o)
  | _, _ => false

/-- `in_scalar_range`: `x` has `order`'s length, is not all zeros, and is
below it. -/
def inScalarRange (x o : Bytes) : Bool :=
  x.length == o.length && !(x.all (· == 0)) && bytesLtBE x o

theorem beq_zext0 : ∀ b : BitVec 8, branchTaken .beq (b.zeroExtend 32) 0 = decide (b.toNat = 0) := by decide

theorem bne_zext (x y : BitVec 8) : branchTaken .bne (x.zeroExtend 32) (y.zeroExtend 32) = !decide (x = y) := by
  rw [← beq_zext]; rfl

/-- `in_scalar_range`'s compare loop body, from 0x16 to the branch at 0x24. -/
def isrCmp : List BInstr :=
  [.lbu a3 a0 0x0, .lbu a4 a2 0x0, .aluImm .add a0 a0 0x1, .aluImm .add a2 a2 0x1, .aluImm .add a1 a1 0xFFFFFFFF]

/-- `in_scalar_range`'s zero loop body, from 0xA to the branch at 0x12. -/
def isrZero : List BInstr := [.lbu a5 a4 0x0, .aluImm .add a4 a4 0x1, .aluImm .add a3 a3 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem isrCmp_end : blockEnd inScalarRangeCode 0x16 isrCmp = some 0x24 := by decide
theorem isrZero_end : blockEnd inScalarRangeCode 0xA isrZero = some 0x12 := by decide
theorem isrMov_end : blockEnd inScalarRangeCode 0x4 [.alu .add a3 x0 a1, .alu .add a4 x0 a0] = some 0x8 := by decide
end

theorem dec1 {k : Nat} : BitVec.ofNat 32 (k + 1) + (0xFFFFFFFF : Word) = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
  omega

theorem isr_ofNat_ne0 {k : Nat} (hk : k + 1 < 2 ^ 32) : branchTaken .bne (BitVec.ofNat 32 (k + 1)) 0 = true := by
  simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
  have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at this; change _ = 0 at this; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `c3_crypto::ecdsa::in_scalar_range`**: 1 when the `n`
bytes at `x` and the `n'` bytes of the order at `o` satisfy
`inScalarRange`, and 0 otherwise. It writes no memory. -/
theorem inScalarRange_correct (m : Machine) {base retAddr x o : Word} {n n' : Nat} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base inScalarRangeCode) (hpc : m.pc = base) (ha0 : reg m a0 = x)
    (ha1 : reg m a1 = BitVec.ofNat 32 n) (ha2 : reg m a2 = o) (ha3 : reg m a3 = BitVec.ofNat 32 n')
    (hn : n < 2 ^ 32) (hn' : n' < 2 ^ 32)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if inScalarRange (memBytes m.mem x n) (memBytes m.mem o n') then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- returning 0 from 0x2A
  have ret0 : ∀ {n1 : Machine}, St m.mem base n1 0x2A (reg n1) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧ reg m' a0 = 0 ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
    intro n1 s hk
    obtain ⟨n2, d2, u2⟩ := s.aluImm hc isr_at_2a (off' := 0x2C) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc isr_at_2c
    refine ⟨n3, .cons d2 (.single d3), ?_, ?_, fun r h0 h1 h2 h3 h4 h5 => ?_, mem3⟩
    · rw [pc3, upd_ne (by decide) (by decide), hk ra (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), add_lit_zero, hra, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [s.zero]; rfl
    · rw [regs3, updz s.zero h0]; exact hk r h0 h1 h2 h3 h4 h5
  -- the compare loop, from 0x28 with `k` bytes left at `p` and `q`
  have cmp : ∀ k, k < 2 ^ 32 → ∀ {n1 : Machine} {p q : Word}, St m.mem base n1 0x28 (reg n1) →
      reg n1 a0 = p → reg n1 a2 = q → reg n1 a1 = BitVec.ofNat 32 k →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧
        reg m' a0 = (if bytesLtBE (memBytes m.mem p k) (memBytes m.mem q k) then 1 else 0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
    intro k
    induction k with
    | zero =>
      intro _ n1 p q s r0 r2 r1 hk
      obtain ⟨n2, d2, u2⟩ := s.notTaken hc 0x2A isr_at_28 (by decide) (by rw [r1, s.zero]; decide)
      obtain ⟨m', c', h1, h2, h3, h4⟩ := ret0 u2.self (fun r h0 h1 h2 h3 h4 h5 => by
        rw [u2.regs]; exact hk r h0 h1 h2 h3 h4 h5)
      exact ⟨m', .cons d2 c', h1, by rw [h2]; rfl, h3, h4⟩
    | succ k ih =>
      intro hk32 n1 p q s r0 r2 r1 hk
      obtain ⟨n2, d2, u2⟩ := s.taken hc 0x16 isr_at_28 (by decide) (by rw [r1, s.zero]; exact isr_ofNat_ne0 hk32)
      obtain ⟨n3, c3, u3⟩ := St.block isrCmp u2 hc isrCmp_end (by simp [BlockOk, BInstr.ok, isrCmp])
      simp only [runBlock, BInstr.run, isrCmp] at u3
      have v3 : reg n3 a3 = (m.mem p).zeroExtend 32 := by
        rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, add_lit_zero]
      have v4 : reg n3 a4 = (m.mem q).zeroExtend 32 := by
        rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, add_lit_zero]
      have keep3 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n3 r = reg m r :=
        fun r h0' h1' h2' h3' h4' h5' => by
          rw [u3.regs]
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact hz.symm
          simp only [upd_app, h0, h0', h1', h2', h3', h4', ite_false]; exact hk r h0' h1' h2' h3' h4' h5'
      have hL : ∀ b : Word, memBytes m.mem b (k + 1) = (m.mem b).toNat :: memBytes m.mem (b + 1) k :=
        fun b => memBytes_succ _ _ _
      by_cases he : m.mem p = m.mem q
      · obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc 0x28 isr_at_24 (by decide) (by
          rw [v3, v4, bne_zext, decide_eq_true he]; rfl)
        obtain ⟨m', c', h1, h2, h3, h4⟩ := ih (by omega) (p := p + 1) (q := q + 1) u4.self
          (by rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, ev_add])
          (by rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, ev_add])
          (by rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, ev_add, dec1])
          (fun r h0' h1' h2' h3' h4' h5' => by rw [u4.regs]; exact keep3 r h0' h1' h2' h3' h4' h5')
        refine ⟨m', .cons d2 (c3.trans (.cons d4 c')), h1, ?_, h3, h4⟩
        rw [h2, hL p, hL q]; simp only [bytesLtBE, he, ↓reduceIte]
      · obtain ⟨n4, d4, u4⟩ := u3.self.taken hc 0x2E isr_at_24 (by decide) (by
          rw [v3, v4, bne_zext, decide_eq_false he]; rfl)
        obtain ⟨n5, d5, u5⟩ := u4.self.alu hc isr_at_2e (off' := 0x32) (by decide)
        obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc isr_at_32
        have hne : (m.mem p).toNat ≠ (m.mem q).toNat := fun h => he (BitVec.eq_of_toNat_eq h)
        refine ⟨n6, .cons d2 (c3.trans (.cons d4 (.cons d5 (.single d6)))), ?_, ?_,
          fun r h0' h1' h2' h3' h4' h5' => ?_, mem6⟩
        · rw [pc6, upd_ne (by decide) (by decide), u4.regs, keep3 ra (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide), add_lit_zero, hra, hret]
        · rw [regs6]; simp +decide only [upd_app, ↓reduceIte]; rw [u4.regs, u4.regs, v3, v4, sltu_zext, hL p, hL q]
          simp only [bytesLtBE, hne, ↓reduceIte]
          by_cases hl : (m.mem p).toNat < (m.mem q).toNat
          · rw [ite_eq_left hl, decide_eq_true hl]; rfl
          · rw [ite_eq_right hl, decide_eq_false hl]; rfl
        · rw [regs6, updz u4.self.zero h0', u4.regs]; exact keep3 r h0' h1' h2' h3' h4' h5'
  -- the zero loop, from 0x8 with `k` bytes left at `p`
  have zl : ∀ k, k < 2 ^ 32 → ∀ {n1 : Machine} {p : Word}, St m.mem base n1 0x8 (reg n1) →
      reg n1 a4 = p → reg n1 a3 = BitVec.ofNat 32 k → reg n1 a0 = x → reg n1 a1 = BitVec.ofNat 32 n →
      reg n1 a2 = o →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧
        reg m' a0 = (if (memBytes m.mem p k).all (· == 0) then 0 else
          if bytesLtBE (memBytes m.mem x n) (memBytes m.mem o n) then 1 else 0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧ m'.mem = m.mem := by
    intro k
    induction k with
    | zero =>
      intro _ n1 p s r4 r3 r0 r1 r2 hk
      obtain ⟨n2, d2, u2⟩ := s.taken hc 0x2A isr_at_8 (by decide) (by rw [r3, s.zero]; decide)
      obtain ⟨m', c', h1, h2, h3, h4⟩ := ret0 u2.self (fun r h0 h1 h2 h3 h4 h5 => by
        rw [u2.regs]; exact hk r h0 h1 h2 h3 h4 h5)
      exact ⟨m', .cons d2 c', h1, by rw [h2]; rfl, h3, h4⟩
    | succ k ih =>
      intro hk32 n1 p s r4 r3 r0 r1 r2 hk
      obtain ⟨n2, d2, u2⟩ := s.notTaken hc 0xA isr_at_8 (by decide) (by
        rw [r3, s.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at this; change _ = 0 at this; omega)
      obtain ⟨n3, c3, u3⟩ := St.block isrZero u2 hc isrZero_end (by simp [BlockOk, BInstr.ok, isrZero])
      simp only [runBlock, BInstr.run, isrZero] at u3
      have v5 : reg n3 a5 = (m.mem p).zeroExtend 32 := by
        rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r4, add_lit_zero]
      have keep3 : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n3 r = reg n1 r := fun r h3 h4 h5 => by
        rw [u3.regs]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact s.zero.symm
        simp only [upd_app, h0, h3, h4, h5, ite_false]
      have hL : memBytes m.mem p (k + 1) = (m.mem p).toNat :: memBytes m.mem (p + 1) k := memBytes_succ _ _ _
      by_cases h0b : (m.mem p).toNat = 0
      · obtain ⟨n4, d4, u4⟩ := u3.self.taken hc 0x8 isr_at_12 (by decide) (by
          rw [v5, u3.self.zero, beq_zext0]; exact decide_eq_true h0b)
        obtain ⟨m', c', h1, h2, h3, h4⟩ := ih (by omega) (p := p + 1) u4.self
          (by rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r4, ev_add])
          (by rw [u4.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r3, ev_add, dec1])
          (by rw [u4.regs, keep3 a0 (by decide) (by decide) (by decide), r0])
          (by rw [u4.regs, keep3 a1 (by decide) (by decide) (by decide), r1])
          (by rw [u4.regs, keep3 a2 (by decide) (by decide) (by decide), r2])
          (fun r h0' h1' h2' h3' h4' h5' => by
            rw [u4.regs, keep3 r h3' h4' h5']; exact hk r h0' h1' h2' h3' h4' h5')
        refine ⟨m', .cons d2 (c3.trans (.cons d4 c')), h1, ?_, h3, h4⟩
        rw [h2, hL]; simp only [List.all_cons, h0b, show ((0 : Nat) == 0) = true from rfl, Bool.true_and]
      · obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc 0x14 isr_at_12 (by decide) (by
          rw [v5, u3.self.zero, beq_zext0]; exact decide_eq_false h0b)
        obtain ⟨n5, d5, u5⟩ := u4.self.jump hc isr_at_14 (off' := 0x28) (by decide) (by
          rw [u4.pc, show base + BitVec.ofNat 32 0x14 + 0x14 = base + BitVec.ofNat 32 0x28 by
            rw [BitVec.add_assoc]; rfl]
          exact even_bit0 (even_at base hP 0x28 (by decide)))
        have r5 : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n5 r = reg n1 r := fun r h3 h4 h5 => by
          rw [u5.regs, u4.regs, keep3 r h3 h4 h5]
        obtain ⟨m', c', h1, h2, h3, h4⟩ := cmp n hn (p := x) (q := o) u5.self
          (by rw [r5 a0 (by decide) (by decide) (by decide), r0]) (by rw [r5 a2 (by decide) (by decide) (by decide), r2])
          (by rw [r5 a1 (by decide) (by decide) (by decide), r1])
          (fun r h0' h1' h2' h3' h4' h5' => by rw [r5 r h3' h4' h5']; exact hk r h0' h1' h2' h3' h4' h5')
        refine ⟨m', .cons d2 (c3.trans (.cons d4 (.cons d5 c'))), h1, ?_, h3, h4⟩
        have hb : ((m.mem p).toNat == 0) = false := by
          cases h : ((m.mem p).toNat == 0)
          · rfl
          · exact absurd (beq_iff_eq.mp h) h0b
        rw [h2, hL]; simp only [List.all_cons, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  by_cases hnn : n = n'
  · subst hnn
    obtain ⟨n1, d1, u1⟩ := s0.notTaken hc 0x4 isr_at_0 (by decide) (by
      rw [ha1, ha3]; simp only [branchTaken, bne_self_eq_false])
    obtain ⟨n2, c2, u2⟩ := St.block _ u1 hc isrMov_end (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u2
    obtain ⟨m', c', h1, h2, h3, h4⟩ := zl n hn (p := x) u2.self
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; exact zw x)
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1]; exact zw _)
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact ha0)
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact ha1)
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact ha2)
      (fun r h0' h1' h2' h3' h4' h5' => by
        rw [u2.regs]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact hz.symm
        simp only [upd_app, h0, h3', h4', ite_false])
    refine ⟨m', .cons d1 (c2.trans c'), h1, ?_, h3, h4⟩
    rw [h2]; simp only [inScalarRange, memBytes_length, show (n == n) = true from decide_eq_true rfl, Bool.true_and]
    cases (memBytes m.mem x n).all (· == 0) <;> rfl
  · obtain ⟨n1, d1, u1⟩ := s0.taken hc 0x2A isr_at_0 (by decide) (by
      rw [ha1, ha3]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
      have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt hn'] at this; exact hnn this)
    obtain ⟨m', c', h1, h2, h3, h4⟩ := ret0 u1.self (fun r _ _ _ _ _ _ => by rw [u1.regs])
    refine ⟨m', .cons d1 c', h1, ?_, h3, h4⟩
    have hb : (n == n') = false := by
      cases h : (n == n')
      · rfl
      · exact absurd (beq_iff_eq.mp h) hnn
    rw [h2]; simp only [inScalarRange, memBytes_length, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end C3.RV32
