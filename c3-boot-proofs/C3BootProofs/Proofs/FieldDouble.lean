import C3BootProofs.Proofs.FieldAdd

/-! # `FieldElement::double`, as compiled -/

namespace C3.RV32

open C3.Image

/-- Where `FieldElement::double` runs: its code at `P`, and `field_impl::add`,
which it tail-calls with both operands at `ap`, where the image puts it. -/
structure FDEnv (M : Word → BitVec 8) (P sp0 res ap : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P fieldDoubleCode
  add : FAEnv M (P + 0xFFFFFCFA) sp0 res ap ap

/-- **The compiled `FieldElement::double`**, called with the result at `res`
and the operand `A` at `ap`: it tail-calls `field_impl::add` with `A` twice,
so it stores `subRes (A + A)`, which is `2A mod p` for `A` below `p`. It
returns with `sp` and every register but `a0` through `a7` and `t0` through
`t6` as they were, and changes no memory outside the 0xB4 bytes of stack
below `sp` and the result. -/
theorem fieldDouble_correct (m : Machine) {P sp0 res ap retAddr : Word}
    (env : FDEnv m.mem P sp0 res ap) (hpc : m.pc = P) (ha0 : reg m a0 = res) (ha1 : reg m a1 = ap)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
        reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem res 8) = subRes (limbVal (wordsAt m.mem ap 8) + limbVal (wordsAt m.mem ap 8)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep res 32 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.alu env.code fd_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.auipc env.code fd_at_2 (off' := 6) (by decide)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.self.jalr env.code fd_at_6
  have k2 : ∀ q, q ≠ a2 → q ≠ t1 → reg n2 q = reg m q := fun q h2 ht => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u2.self.zero, hz]
    · rw [u2.regs, upd_ne h0 ht, u1.regs, upd_ne h0 h2]
  have e2 : reg n2 a2 = ap := by
    rw [u2.regs, upd_ne (by decide) (by decide), u1.regs, upd_same (by decide), hz, ha1]; exact BitVec.zero_add _
  have et : reg n2 t1 = P + BitVec.ofNat 32 2 := by
    rw [u2.regs, upd_same (by decide), add_lit_zero]
  have pcA : n3.pc = P + 0xFFFFFCFA := by
    rw [pc3, et, BitVec.add_assoc]
    exact even_clear _ (even_at P env.hP 0xFFFFFCFA (by decide))
  obtain ⟨n4, c4, pc4, sp4, regs4, val4, frame4⟩ := fieldAdd_correct n3 (by rw [mem3]; exact env.add) pcA
    (by rw [regs3, k2 _ (by decide) (by decide), ha0]) (by rw [regs3, k2 _ (by decide) (by decide), ha1])
    (by rw [regs3, e2]) (by rw [regs3, k2 _ (by decide) (by decide), hra]) hret
    (by rw [regs3, k2 _ (by decide) (by decide), hsp])
  rw [mem3] at val4 frame4
  refine ⟨n4, .cons d1 (.cons d2 (.cons d3 c4)), pc4, sp4, fun q q0 q1 q2 q3 q4 q5 q6 q7 qt0 qt1 qt2 qt3 qt4 qt5 qt6 => ?_,
    val4, frame4⟩
  rw [regs4 q q0 q1 q2 q3 q4 q5 q6 q7 qt0 qt1 qt2 qt3 qt4 qt5 qt6, regs3, k2 q q2 qt1]

end C3.RV32
