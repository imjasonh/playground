import C3BootProofs.Proofs.ByteCompare

/-!
# `checkpoint::line`, as compiled

`c3_verify::checkpoint::line` splits a byte slice at its first newline. It
returns the bytes before the newline and the bytes after it, or
`BadCheckpoint` (0x1A) when the slice holds no newline.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem cl_at_0 : fetchRel checkpointLineCode 0x0 = some (.aluImm .add a3 x0 0x0, 2) := by decide
theorem cl_at_2 : fetchRel checkpointLineCode 0x2 = some (.aluImm .add a4 x0 0xA, 2) := by decide
theorem cl_at_4 : fetchRel checkpointLineCode 0x4 = some (.branch .beq a2 x0 0x14, 2) := by decide
theorem cl_at_6 : fetchRel checkpointLineCode 0x6 = some (.alu .add a5 a1 a3, 4) := by decide
theorem cl_at_a : fetchRel checkpointLineCode 0xA = some (.load .lbu a5 a5 0x0, 4) := by decide
theorem cl_at_e : fetchRel checkpointLineCode 0xE = some (.branch .beq a5 a4 0x16, 4) := by decide
theorem cl_at_12 : fetchRel checkpointLineCode 0x12 = some (.aluImm .add a3 a3 0x1, 2) := by decide
theorem cl_at_14 : fetchRel checkpointLineCode 0x14 = some (.branch .bne a2 a3 0xFFFFFFF2, 4) := by decide
theorem cl_at_18 : fetchRel checkpointLineCode 0x18 = some (.aluImm .add a1 x0 0x1A, 2) := by decide
theorem cl_at_1a : fetchRel checkpointLineCode 0x1A = some (.store .sw a0 x0 0x0, 4) := by decide
theorem cl_at_1e : fetchRel checkpointLineCode 0x1E = some (.store .sb a0 a1 0x4, 4) := by decide
theorem cl_at_22 : fetchRel checkpointLineCode 0x22 = some (.jalr x0 ra 0x0, 2) := by decide
theorem cl_at_24 : fetchRel checkpointLineCode 0x24 = some (.aluImm .add a4 a3 0x1, 4) := by decide
theorem cl_at_28 : fetchRel checkpointLineCode 0x28 = some (.alu .add a5 a1 a4, 4) := by decide
theorem cl_at_2c : fetchRel checkpointLineCode 0x2C = some (.alu .sub a2 a2 a4, 2) := by decide
theorem cl_at_2e : fetchRel checkpointLineCode 0x2E = some (.store .sw a0 a1 0x0, 2) := by decide
theorem cl_at_30 : fetchRel checkpointLineCode 0x30 = some (.store .sw a0 a3 0x4, 2) := by decide
theorem cl_at_32 : fetchRel checkpointLineCode 0x32 = some (.store .sw a0 a5 0x8, 2) := by decide
theorem cl_at_34 : fetchRel checkpointLineCode 0x34 = some (.store .sw a0 a2 0xC, 2) := by decide
theorem cl_at_36 : fetchRel checkpointLineCode 0x36 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The first index from `k`, among the next `f` bytes at `p`, that holds a
newline. -/
def nlScan (M : Word → BitVec 8) (p : Word) : Nat → Nat → Option Nat
  | _, 0 => none
  | k, f + 1 => if M (p + BitVec.ofNat 32 k) = 0x0A then some k else nlScan M p (k + 1) f

/-- What `checkpoint::line` stores in its `Result<(&[u8], &[u8]), Error>` at
`out` for the `n` bytes at `p`, given the newline's index. -/
def lineMem (M : Word → BitVec 8) (out p : Word) (n : Nat) : Option Nat → Word → BitVec 8
  | none => memStore8 (memStore32 M out 0) (out + 4) 0x1A
  | some i => memStore32 (memStore32 (memStore32 (memStore32 M out p) (out + 4) (BitVec.ofNat 32 i))
      (out + 8) (p + BitVec.ofNat 32 (i + 1))) (out + 0xC) (BitVec.ofNat 32 n - BitVec.ofNat 32 (i + 1))

theorem cl_succ (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `checkpoint::line`**: for the `n` bytes at `p`, it stores
`lineMem` of the first newline's index at `out`, and changes no other
memory. -/
theorem checkpointLine_correct (m : Machine) {base retAddr out p : Word} {n : Nat}
    (hc : CodeIn m.mem base checkpointLineCode) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) (hout : out.toNat % 4 = 0)
    (sOC : Sep out 16 base checkpointLineCode.length) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = lineMem m.mem out p n (nlScan m.mem p 0 n) ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have c4 : ∀ (c : Nat) {v : Word} {M : Word → BitVec 8}, c + 4 ≤ 16 → CodeIn M base checkpointLineCode →
      CodeIn (memStore32 M (out + BitVec.ofNat 32 c) v) base checkpointLineCode := by
    intro c v M h hcM; exact CodeIn.store32 hcM (sOC.sub (by omega))
  -- the found path, from 0x24 with the newline at `i`
  have found : ∀ {nn : Machine} (i : Nat), i < n → St m.mem base nn 0x24 (reg nn) → reg nn a3 = BitVec.ofNat 32 i →
      reg nn a2 = BitVec.ofNat 32 n → reg nn a1 = p → reg nn a0 = out →
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg nn r = reg m r) →
      ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧ m'.mem = lineMem m.mem out p n (some i) ∧
        ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
    intro nn i hi st r3 r2 r1 r0 kk
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc cl_at_24 (off' := 0x28) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.alu hc cl_at_28 (off' := 0x2C) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.self.alu hc cl_at_2c (off' := 0x2E) (by decide)
    have g3 : ∀ q, reg n3 q = upd (reg n2) a2 (aluEval .sub (reg n2 a2) (reg n2 a4)) q := u3.regs
    have v4 : reg n2 a4 = BitVec.ofNat 32 (i + 1) := by
      rw [u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [r3, ev_add, cl_succ]
    have v5 : reg n3 a5 = p + BitVec.ofNat 32 (i + 1) := by
      rw [g3, upd_ne' (by decide) u2.self.zero, u2.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u1.regs, upd_ne' (by decide) st.zero, r1, ev_add, ← v4, u2.regs, upd_ne' (by decide) u1.self.zero]
    have v2 : reg n3 a2 = BitVec.ofNat 32 n - BitVec.ofNat 32 (i + 1) := by
      rw [g3]; simp +decide only [upd_app, ↓reduceIte]
      rw [v4, u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs, upd_ne' (by decide) st.zero, r2]; rfl
    have k3 : ∀ q, q ≠ a2 → q ≠ a4 → q ≠ a5 → reg n3 q = reg nn q := fun q h2 h4 h5 => by
      rw [g3, upd_ne' h2 u2.self.zero, u2.regs, upd_ne' h5 u1.self.zero, u1.regs, upd_ne' h4 st.zero]
    have o0 : reg n3 a0 = out := by rw [k3 a0 (by decide) (by decide) (by decide), r0]
    obtain ⟨n4, d4, u4⟩ := u3.self.sw hc cl_at_2e (off' := 0x30) (by decide) (by rw [o0, add_lit_zero]; exact hout)
    rw [o0, add_lit_zero, k3 a1 (by decide) (by decide) (by decide), r1] at u4
    have hc4 : CodeIn (memStore32 m.mem out p) base checkpointLineCode := by
      have := c4 0 (v := p) (M := m.mem) (by decide) hc; rwa [add_ofNat_zero] at this
    obtain ⟨n5, d5, u5⟩ := u4.sw hc4 cl_at_30 (off' := 0x32) (by decide) (by
      rw [o0]; exact aligned_add hout (k := 4) (by decide))
    rw [o0, k3 a3 (by decide) (by decide) (by decide), r3] at u5
    obtain ⟨n6, d6, u6⟩ := u5.sw (c4 4 (by decide) hc4) cl_at_32 (off' := 0x34) (by decide) (by
      rw [o0]; exact aligned_add hout (k := 8) (by decide))
    rw [o0, v5] at u6
    obtain ⟨n7, d7, u7⟩ := u6.sw (c4 8 (by decide) (c4 4 (by decide) hc4)) cl_at_34 (off' := 0x36) (by decide) (by
      rw [o0]; exact aligned_add hout (k := 0xC) (by decide))
    rw [o0, v2] at u7
    obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr (c4 0xC (by decide) (c4 8 (by decide) (c4 4 (by decide) hc4))) cl_at_36
    refine ⟨n8, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.single d8))))))), ?_, ?_,
      fun r h1 h2 h3 h4 h5 => ?_⟩
    · rw [pc8, add_lit_zero, k3 ra (by decide) (by decide) (by decide),
        kk ra (by decide) (by decide) (by decide) (by decide) (by decide), hra, hret]
    · rw [mem8]; rfl
    · rw [regs8, k3 r h2 h4 h5]; exact kk r h1 h2 h3 h4 h5
  -- no newline, from 0x18
  have none_ : ∀ {nn : Machine}, St m.mem base nn 0x18 (reg nn) → reg nn a0 = out →
      (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg nn r = reg m r) →
      ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧ m'.mem = lineMem m.mem out p n none ∧
        ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
    intro nn st r0 kk
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc cl_at_18 (off' := 0x1A) (by decide)
    have k1 : ∀ q, q ≠ a1 → reg n1 q = reg nn q := fun q h => by rw [u1.regs, upd_ne' h st.zero]
    obtain ⟨n2, d2, u2⟩ := u1.self.sw hc cl_at_1a (off' := 0x1E) (by decide) (by
      rw [k1 a0 (by decide), r0, add_lit_zero]; exact hout)
    rw [k1 a0 (by decide), r0, add_lit_zero, show reg n1 x0 = 0 from u1.self.zero] at u2
    have hc2 : CodeIn (memStore32 m.mem out 0) base checkpointLineCode := by
      have := c4 0 (v := 0) (M := m.mem) (by decide) hc; rwa [add_ofNat_zero] at this
    obtain ⟨n3, d3, u3⟩ := u2.sb hc2 cl_at_1e (off' := 0x22) (by decide)
    rw [k1 a0 (by decide), r0, u1.regs] at u3
    simp +decide only [upd_app, ↓reduceIte] at u3
    have hc3 := CodeIn.store8 (v := (aluEval .add (reg nn x0) 0x1A).extractLsb' 0 8) hc2 (sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc3 cl_at_22
    refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_⟩
    · rw [pc4, add_lit_zero, k1 ra (by decide), kk ra (by decide) (by decide) (by decide) (by decide) (by decide), hra, hret]
    · rw [mem4, st.zero]; rfl
    · rw [regs4, k1 r h1]; exact kk r h1 h2 h3 h4 h5
  -- the scan, from 0x6 with `f` bytes left to check after `k`
  have loop : ∀ f k, k + f + 1 = n → ∀ {nn : Machine}, St m.mem base nn 0x6 (reg nn) →
      reg nn a3 = BitVec.ofNat 32 k → reg nn a4 = 0xA → reg nn a2 = BitVec.ofNat 32 n → reg nn a1 = p →
      reg nn a0 = out → (∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg nn r = reg m r) →
      ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧ m'.mem = lineMem m.mem out p n (nlScan m.mem p k (f + 1)) ∧
        ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
    intro f
    induction f with
    | zero =>
      intro k hk nn st r3 r4 r2 r1 r0 kk
      obtain ⟨n1, d1, u1⟩ := st.alu hc cl_at_6 (off' := 0xA) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.self.lbu hc cl_at_a (off' := 0xE) (by decide)
      have v5 : reg n2 a5 = (m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32 := by
        rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [ev_add, r1, r3, add_lit_zero]
      have k2 : ∀ q, q ≠ a5 → reg n2 q = reg nn q := fun q h => by
        rw [u2.regs, upd_ne' h u1.self.zero, u1.regs, upd_ne' h st.zero]
      have kk2 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n2 r = reg m r := fun r h1 h2 h3 h4 h5 => by
        rw [k2 r h5]; exact kk r h1 h2 h3 h4 h5
      by_cases hb : m.mem (p + BitVec.ofNat 32 k) = 0x0A
      · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x24 cl_at_e (by decide) (by
          rw [v5, k2 a4 (by decide), r4, show (0xA : Word) = (0x0A : BitVec 8).zeroExtend 32 from rfl, beq_zext]
          exact decide_eq_true hb)
        obtain ⟨m', c', h1, h2, h3⟩ := found k (by omega) u3.self (by rw [u3.regs, k2 a3 (by decide), r3])
          (by rw [u3.regs, k2 a2 (by decide), r2]) (by rw [u3.regs, k2 a1 (by decide), r1])
          (by rw [u3.regs, k2 a0 (by decide), r0]) (fun r h1 h2 h3 h4 h5 => by rw [u3.regs]; exact kk2 r h1 h2 h3 h4 h5)
        refine ⟨m', .cons d1 (.cons d2 (.cons d3 c')), h1, ?_, h3⟩
        rw [h2]; simp only [nlScan, hb, ↓reduceIte]
      obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x12 cl_at_e (by decide) (by
        rw [v5, k2 a4 (by decide), r4, show (0xA : Word) = (0x0A : BitVec 8).zeroExtend 32 from rfl, beq_zext]
        exact decide_eq_false hb)
      obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc cl_at_12 (off' := 0x14) (by decide)
      have v4 : reg n4 a3 = BitVec.ofNat 32 (k + 1) := by
        rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.regs, k2 a3 (by decide), r3, ev_add, cl_succ]
      have k4 : ∀ q, q ≠ a3 → reg n4 q = reg n2 q := fun q h => by rw [u4.regs, upd_ne' h u3.self.zero, u3.regs]
      have hk1 : k + 1 = n := by omega
      obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc 0x18 cl_at_14 (by decide) (by
        rw [k4 a2 (by decide), k2 a2 (by decide), r2, v4, hk1]; exact bne_self_eq_false _)
      obtain ⟨m', c', h1, h2, h3⟩ := none_ u5.self (by rw [u5.regs, k4 a0 (by decide), k2 a0 (by decide), r0])
        (fun r h1 h2 h3 h4 h5 => by rw [u5.regs, k4 r h3]; exact kk2 r h1 h2 h3 h4 h5)
      refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c')))), h1, ?_, h3⟩
      rw [h2]; simp only [nlScan, hb, ↓reduceIte]
    | succ f ih =>
      intro k hk nn st r3 r4 r2 r1 r0 kk
      obtain ⟨n1, d1, u1⟩ := st.alu hc cl_at_6 (off' := 0xA) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.self.lbu hc cl_at_a (off' := 0xE) (by decide)
      have v5 : reg n2 a5 = (m.mem (p + BitVec.ofNat 32 k)).zeroExtend 32 := by
        rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [ev_add, r1, r3, add_lit_zero]
      have k2 : ∀ q, q ≠ a5 → reg n2 q = reg nn q := fun q h => by
        rw [u2.regs, upd_ne' h u1.self.zero, u1.regs, upd_ne' h st.zero]
      have kk2 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n2 r = reg m r := fun r h1 h2 h3 h4 h5 => by
        rw [k2 r h5]; exact kk r h1 h2 h3 h4 h5
      by_cases hb : m.mem (p + BitVec.ofNat 32 k) = 0x0A
      · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x24 cl_at_e (by decide) (by
          rw [v5, k2 a4 (by decide), r4, show (0xA : Word) = (0x0A : BitVec 8).zeroExtend 32 from rfl, beq_zext]
          exact decide_eq_true hb)
        obtain ⟨m', c', h1, h2, h3⟩ := found k (by omega) u3.self (by rw [u3.regs, k2 a3 (by decide), r3])
          (by rw [u3.regs, k2 a2 (by decide), r2]) (by rw [u3.regs, k2 a1 (by decide), r1])
          (by rw [u3.regs, k2 a0 (by decide), r0]) (fun r h1 h2 h3 h4 h5 => by rw [u3.regs]; exact kk2 r h1 h2 h3 h4 h5)
        refine ⟨m', .cons d1 (.cons d2 (.cons d3 c')), h1, ?_, h3⟩
        rw [h2]; simp only [nlScan, hb, ↓reduceIte]
      obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x12 cl_at_e (by decide) (by
        rw [v5, k2 a4 (by decide), r4, show (0xA : Word) = (0x0A : BitVec 8).zeroExtend 32 from rfl, beq_zext]
        exact decide_eq_false hb)
      obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc cl_at_12 (off' := 0x14) (by decide)
      have v4 : reg n4 a3 = BitVec.ofNat 32 (k + 1) := by
        rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.regs, k2 a3 (by decide), r3, ev_add, cl_succ]
      have k4 : ∀ q, q ≠ a3 → reg n4 q = reg n2 q := fun q h => by rw [u4.regs, upd_ne' h u3.self.zero, u3.regs]
      obtain ⟨n5, d5, u5⟩ := u4.self.taken hc 0x6 cl_at_14 (by decide) (by
        rw [k4 a2 (by decide), k2 a2 (by decide), r2, v4]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h; rw [ofNat_tn hn, ofNat_tn (by omega)] at this; omega)
      obtain ⟨m', c', h1, h2, h3⟩ := ih (k + 1) (by omega) u5.self (by rw [u5.regs, v4])
        (by rw [u5.regs, k4 a4 (by decide), k2 a4 (by decide), r4]) (by rw [u5.regs, k4 a2 (by decide), k2 a2 (by decide), r2])
        (by rw [u5.regs, k4 a1 (by decide), k2 a1 (by decide), r1]) (by rw [u5.regs, k4 a0 (by decide), k2 a0 (by decide), r0])
        (fun r h1 h2 h3 h4 h5 => by rw [u5.regs, k4 r h3]; exact kk2 r h1 h2 h3 h4 h5)
      refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c')))), h1, ?_, h3⟩
      rw [h2]; conv => rhs; rw [nlScan]
      rw [ite_eq_right hb]
  obtain ⟨n1, c1, u1⟩ := St.block [.aluImm .add a3 x0 0, .aluImm .add a4 x0 0xA] s0 hc (off' := 4) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have k1 : ∀ q, q ≠ a3 → q ≠ a4 → reg n1 q = reg m q := fun q h3 h4 => by
    rw [u1.regs, updz ((updz hz (by decide)).trans hz) h4, updz hz h3]
  have kk1 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg m r := fun r _ _ h3 h4 _ => k1 r h3 h4
  cases n with
  | zero =>
    obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x18 cl_at_4 (by decide) (by
      rw [k1 a2 (by decide) (by decide), ha2, u1.self.zero]; rfl)
    obtain ⟨m', c', h1, h2, h3⟩ := none_ u2.self (by rw [u2.regs, k1 a0 (by decide) (by decide), ha0])
      (fun r h1 h2 h3 h4 h5 => by rw [u2.regs]; exact kk1 r h1 h2 h3 h4 h5)
    exact ⟨m', c1.trans (.cons d2 c'), h1, by rw [h2]; rfl, h3⟩
  | succ f =>
    obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x6 cl_at_4 (by decide) (by
      rw [k1 a2 (by decide) (by decide), ha2, u1.self.zero]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]
      intro h; have := congrArg BitVec.toNat h; rw [ofNat_tn hn] at this; change _ = 0 at this; omega)
    obtain ⟨m', c', h1, h2, h3⟩ := loop f 0 (by omega) u2.self
      (by rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]; rfl)
      (by rw [u2.regs, u1.regs]; simp +decide only [upd_app, ↓reduceIte])
      (by rw [u2.regs, k1 a2 (by decide) (by decide), ha2]) (by rw [u2.regs, k1 a1 (by decide) (by decide), ha1])
      (by rw [u2.regs, k1 a0 (by decide) (by decide), ha0])
      (fun r h1 h2 h3 h4 h5 => by rw [u2.regs]; exact kk1 r h1 h2 h3 h4 h5)
    exact ⟨m', c1.trans (.cons d2 c'), h1, h2, h3⟩

end C3.RV32
