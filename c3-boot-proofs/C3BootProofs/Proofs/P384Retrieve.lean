import C3BootProofs.Proofs.MontRetrieve12
import C3BootProofs.Proofs.P384Mont

/-!
# P-384's field `retrieve`, as compiled

`ConstMontyForm<p384::FieldParams, 12>::retrieve` loads the modulus's
address and `k = 1` and tail-calls `montgomery_retrieve::<12>`. For an input
below `p`, the result is `p3fm A 1`, the input out of Montgomery form.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem p3r_at_0 : fetchRel p384FieldRetrieveCode 0x0 = some (.lui a2 0x3FCC5000, 4) := by decide
theorem p3r_at_4 : fetchRel p384FieldRetrieveCode 0x4 = some (.aluImm .add a2 a2 0xFFFFFCF4, 4) := by decide
theorem p3r_at_8 : fetchRel p384FieldRetrieveCode 0x8 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem p3r_at_a : fetchRel p384FieldRetrieveCode 0xA = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem p3r_at_e : fetchRel p384FieldRetrieveCode 0xE = some (.jalr x0 (6 : Fin 32) 0xFFFFFF1A, 4) := by decide
end

/-- Where `ConstMontyForm<p384::FieldParams, 12>::retrieve` runs: its code
at `P`, and `montgomery_retrieve::<12>`'s environment with the modulus where
the image puts it. -/
structure P3REnv (M : Word → BitVec 8) (P sp0 out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384FieldRetrieveCode
  pmod : CodeIn M p3M p384ModulusData
  mr : MREnv M (P + 0xFFFFFF24) sp0 out xp p3M

/-- **The compiled `ConstMontyForm<p384::FieldParams, 12>::retrieve`**,
called with the result at `out` and an input `A < p` at `xp`, stores
`p3fm A 1 = A · 2^-384 mod p`. It returns with `sp`, `ra`, `gp`, `tp`, and
`s0` through `s11` as they were, and changes no memory outside the 0x50
bytes of stack below `sp` and the result. -/
theorem p384FieldRetrieve_correct (m : Machine) {P sp0 out xp retAddr : Word}
    (env : P3REnv m.mem P sp0 out xp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hA : accV m.mem xp 12 < p384) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      accV m'.mem out 12 = p3fm (accV m.mem xp 12) 1 ∧
      ∀ x, Sep (sp0 + 0xFFFFFFB0) 0x50 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.lui env.code p3r_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm env.code p3r_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm env.code p3r_at_8 (off' := 0xA) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.auipc env.code p3r_at_a (off' := 0xE) (by decide)
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.self.jalr env.code p3r_at_e
  have k4 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ t1 → reg n4 q = reg m q := fun q h2 h3 ht => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u4.self.zero, hz]
    · rw [u4.regs, upd_ne h0 ht, u3.regs, upd_ne h0 h3, u2.regs, upd_ne h0 h2, u1.regs, upd_ne h0 h2]
  have e2 : reg n4 a2 = p3M := by
    rw [u4.regs, upd_ne (by decide) (by decide), u3.regs, upd_ne (by decide) (by decide), u2.regs,
      upd_same (by decide), u1.regs, upd_same (by decide)]; rfl
  have e3 : reg n4 a3 = 1 := by
    rw [u4.regs, upd_ne (by decide) (by decide), u3.regs, upd_same (by decide),
      show reg n2 x0 = 0 from u2.self.zero]; rfl
  have et : reg n4 t1 = P + BitVec.ofNat 32 0xA + 0x0 := by rw [u4.regs, upd_same (by decide)]
  have pcA : n5.pc = P + 0xFFFFFF24 := by
    rw [pc5, et, add_lit_zero, BitVec.add_assoc]
    exact even_clear _ (even_at P env.hP 0xFFFFFF24 (by decide))
  have hk : ((1 : Word).toNat * (memLoad32 n5.mem p3M).toNat + 1) % 2 ^ 32 = 0 := by
    rw [mem5, p3M_w0 env.pmod]; decide
  obtain ⟨n6, c6, pc6, sp6, val6, lt6, fr6, k6⟩ := montRetrieve12_correct n5 (by rw [mem5]; exact env.mr) pcA
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), ha0])
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), ha1])
    (by rw [regs5, e2]) (by rw [regs5, e3])
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), hra]) hret
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), hsp]) hk
  rw [mem5, p3M_val env.pmod] at lt6 val6
  rw [mem5] at fr6
  refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c6)))), pc6, sp6, fun q hq => ?_, ?_, fr6⟩
  · have h : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ t1 := by revert q; decide
    rw [k6 q hq, regs5, k4 q h.1 h.2.1 h.2.2]
  · exact p3_mont (lt6 hA) (by rw [val6, Nat.mul_one])

end C3.RV32
