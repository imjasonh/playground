import C3BootProofs.Proofs.P384Double
import C3BootProofs.Proofs.SqrMont12Main
import C3BootProofs.Image.Bootloader

/-!
# P-384's field multiplication and squaring wrappers, as compiled

`ConstMontyForm<p384::FieldParams, 12>::mul` and `FieldElement::square` load
the modulus's address and `k = 1` and tail-call `mul_montgomery_form::<12>`
and `square_montgomery_form::<12>`. `p3fm` is the Montgomery product modulo
P-384's `p` as a function, so callers can name the results.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem p3m_at_0 : fetchRel p384MulCode 0x0 = some (.lui a3 0x3FCC5000, 4) := by decide
theorem p3m_at_4 : fetchRel p384MulCode 0x4 = some (.aluImm .add a3 a3 0xFFFFFC8C, 4) := by decide
theorem p3m_at_8 : fetchRel p384MulCode 0x8 = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem p3m_at_a : fetchRel p384MulCode 0xA = some (.auipc (6 : Fin 32) 0xFFFFF000, 4) := by decide
theorem p3m_at_e : fetchRel p384MulCode 0xE = some (.jalr x0 (6 : Fin 32) 0x454, 4) := by decide
theorem p3q_at_0 : fetchRel p384SqrCode 0x0 = some (.lui a2 0x3FCC5000, 4) := by decide
theorem p3q_at_4 : fetchRel p384SqrCode 0x4 = some (.aluImm .add a2 a2 0xFFFFFC8C, 4) := by decide
theorem p3q_at_8 : fetchRel p384SqrCode 0x8 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem p3q_at_a : fetchRel p384SqrCode 0xA = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem p3q_at_e : fetchRel p384SqrCode 0xE = some (.jalr x0 (6 : Fin 32) 0xFFFFF95E, 4) := by decide
end

/-- `(2 ^ 384)⁻¹ mod p`. -/
def p3RInv : Nat := 0x14000000140000000c00000002fffffffcfffffffafffffffbfffffffdffffffebffffffd8ffffffe100000006

/-- The Montgomery product `a · b · 2^-384 mod p`. -/
def p3fm (a b : Nat) : Nat := a * b * p3RInv % p384

set_option exponentiation.threshold 600 in
theorem p384_pos : 0 < p384 := by unfold p384; decide

theorem p3fm_lt (a b : Nat) : p3fm a b < p384 := Nat.mod_lt _ p384_pos

set_option exponentiation.threshold 600 in
theorem p3_mont {R A B : Nat} (hR : R < p384) (h : (R * 2 ^ 384) % p384 = (A * B) % p384) : R = p3fm A B := by
  have hinv : (2 ^ 384 * p3RInv) % p384 = 1 := by unfold p384 p3RInv; decide
  unfold p3fm
  calc R = R % p384 := (Nat.mod_eq_of_lt hR).symm
    _ = (R * ((2 ^ 384 * p3RInv) % p384)) % p384 := by rw [hinv, Nat.mul_one]
    _ = (R * 2 ^ 384 * p3RInv) % p384 := by rw [Nat.mul_mod_mod, Nat.mul_assoc]
    _ = ((R * 2 ^ 384) % p384 * p3RInv) % p384 := by rw [Nat.mod_mul_mod]
    _ = ((A * B) % p384 * p3RInv) % p384 := by rw [h]
    _ = (A * B * p3RInv) % p384 := by rw [Nat.mod_mul_mod]

theorem p3M_w0 {M : Word → BitVec 8} (h : CodeIn M p3M p384ModulusData) : memLoad32 M p3M = 0xFFFFFFFF := by
  have b0 : M p3M = byteAt p384ModulusData 0 := by have := h 0 (by decide); rwa [add_ofNat_zero] at this
  have b1 : M (p3M + 1) = byteAt p384ModulusData 1 := h 1 (by decide)
  have b2 : M (p3M + 2) = byteAt p384ModulusData 2 := h 2 (by decide)
  have b3 : M (p3M + 3) = byteAt p384ModulusData 3 := h 3 (by decide)
  unfold memLoad32
  rw [b3, b2, b1, b0]
  decide

/-- Where `ConstMontyForm<p384::FieldParams, 12>::mul` runs: its code at `P`,
and `mul_montgomery_form::<12>`'s environment with the modulus where the
image puts it. -/
structure P3MEnv (M : Word → BitVec 8) (P sp0 out xp yp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384MulCode
  pmod : CodeIn M p3M p384ModulusData
  mm : MMEnv M (P + 0xFFFFF45E) sp0 out xp yp p3M

/-- **The compiled `ConstMontyForm<p384::FieldParams, 12>::mul`**, called
with the result at `out` and operands `A` at `xp` and `B < p` at `yp`, stores
`p3fm A B`: the Montgomery product modulo P-384's `p`. It returns with `sp`,
`ra`, `gp`, `tp`, and `s0` through `s11` as they were, and changes no memory
outside the 0xF0 bytes of stack below `sp` and the result. -/
theorem p384Mul_correct (m : Machine) {P sp0 out xp yp retAddr : Word}
    (env : P3MEnv m.mem P sp0 out xp yp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (ha2 : reg m a2 = yp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hB : limbVal (wordsAt m.mem yp 12) < p384) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 12) = p3fm (limbVal (wordsAt m.mem xp 12)) (limbVal (wordsAt m.mem yp 12)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.lui env.code p3m_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm env.code p3m_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm env.code p3m_at_8 (off' := 0xA) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.auipc env.code p3m_at_a (off' := 0xE) (by decide)
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.self.jalr env.code p3m_at_e
  have k4 : ∀ q, q ≠ a3 → q ≠ a4 → q ≠ t1 → reg n4 q = reg m q := fun q h3 h4 ht => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u4.self.zero, hz]
    · rw [u4.regs, upd_ne h0 ht, u3.regs, upd_ne h0 h4, u2.regs, upd_ne h0 h3, u1.regs, upd_ne h0 h3]
  have e3 : reg n4 a3 = p3M := by
    rw [u4.regs, upd_ne (by decide) (by decide), u3.regs, upd_ne (by decide) (by decide), u2.regs,
      upd_same (by decide), u1.regs, upd_same (by decide)]; rfl
  have e4 : reg n4 a4 = 1 := by
    rw [u4.regs, upd_ne (by decide) (by decide), u3.regs, upd_same (by decide),
      show reg n2 x0 = 0 from u2.self.zero]; rfl
  have et : reg n4 t1 = P + BitVec.ofNat 32 0xA + 0xFFFFF000 := by rw [u4.regs, upd_same (by decide)]
  have pcA : n5.pc = P + 0xFFFFF45E := by
    rw [pc5, et, BitVec.add_assoc, BitVec.add_assoc]
    exact even_clear _ (even_at P env.hP 0xFFFFF45E (by decide))
  have hk : ((1 : Word).toNat * (memLoad32 n5.mem p3M).toNat + 1) % 2 ^ 32 = 0 := by
    rw [mem5, p3M_w0 env.pmod]; decide
  obtain ⟨n6, c6, pc6, sp6, lt6, val6, fr6, k6⟩ := mulMont12_correct n5 (by rw [mem5]; exact env.mm) pcA
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), ha0])
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), ha1])
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), ha2]) (by rw [regs5, e3]) (by rw [regs5, e4])
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), hra]) hret
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), hsp]) hk
    (by rw [mem5, p3M_val env.pmod, ← limbVal_wordsAt]; exact hB)
  rw [mem5, p3M_val env.pmod] at lt6 val6
  rw [mem5] at fr6
  refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c6)))), pc6, sp6, fun q hq => ?_, ?_, fr6⟩
  · have h : q ≠ a3 ∧ q ≠ a4 ∧ q ≠ t1 := by revert q; decide
    rw [k6 q hq, regs5, k4 q h.1 h.2.1 h.2.2]
  · rw [limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt]
    exact p3_mont lt6 val6

/-- Where `FieldElement::square` for P-384 runs: its code at `P`, and
`square_montgomery_form::<12>`'s environment with the modulus where the image
puts it. -/
structure P3QEnv (M : Word → BitVec 8) (P sp0 out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384SqrCode
  pmod : CodeIn M p3M p384ModulusData
  sq : SQEnv M (P + 0xFFFFF968) sp0 out xp p3M

/-- **The compiled `<p384::FieldElement as ff::Field>::square`**, called with
the result at `out` and an operand `A < p` at `xp`, stores `p3fm A A`. It
returns with `sp`, `ra`, `gp`, `tp`, and `s0` through `s11` as they were, and
changes no memory outside the 0xF0 bytes of stack below `sp` and the
result. -/
theorem p384Sqr_correct (m : Machine) {P sp0 out xp retAddr : Word}
    (env : P3QEnv m.mem P sp0 out xp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hA : limbVal (wordsAt m.mem xp 12) < p384) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 12) = p3fm (limbVal (wordsAt m.mem xp 12)) (limbVal (wordsAt m.mem xp 12)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.lui env.code p3q_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm env.code p3q_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm env.code p3q_at_8 (off' := 0xA) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.auipc env.code p3q_at_a (off' := 0xE) (by decide)
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.self.jalr env.code p3q_at_e
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
  have pcA : n5.pc = P + 0xFFFFF968 := by
    rw [pc5, et, add_lit_zero, BitVec.add_assoc]
    exact even_clear _ (even_at P env.hP 0xFFFFF968 (by decide))
  have hk : ((1 : Word).toNat * (memLoad32 n5.mem p3M).toNat + 1) % 2 ^ 32 = 0 := by
    rw [mem5, p3M_w0 env.pmod]; decide
  obtain ⟨n6, c6, pc6, sp6, lt6, val6, fr6, k6⟩ := sqrMont12_correct n5 (by rw [mem5]; exact env.sq) pcA
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), ha0])
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), ha1])
    (by rw [regs5, e2]) (by rw [regs5, e3])
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), hra]) hret
    (by rw [regs5, k4 _ (by decide) (by decide) (by decide), hsp]) hk
    (by rw [mem5, p3M_val env.pmod, ← limbVal_wordsAt]; exact hA)
  rw [mem5, p3M_val env.pmod] at lt6 val6
  rw [mem5] at fr6
  refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c6)))), pc6, sp6, fun q hq => ?_, ?_, fr6⟩
  · have h : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ t1 := by revert q; decide
    rw [k6 q hq, regs5, k4 q h.1 h.2.1 h.2.2]
  · rw [limbVal_wordsAt, limbVal_wordsAt]
    exact p3_mont lt6 val6

end C3.RV32
