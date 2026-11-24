import C3BootProofs.Proofs.P384Mont

/-!
# P-384 scalar `mul` and `new`, as compiled

`ConstMontyForm<p384::ScalarParams, 12>::mul` and `::new` tail-call the
proved `mul_montgomery_form::<12>` with the group order `n` and
`-n⁻¹ mod 2^32` from the image. `new` multiplies by `R² mod n`, which the
image keeps 0x60 bytes past the order, so it stores `A · 2^384 mod n`, the
operand in Montgomery form.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem nsm_at_0 : fetchRel p384ScalarMulCode 0x0 = some (.lui a3 0x3FCC5000, 4) := by decide
theorem nsm_at_4 : fetchRel p384ScalarMulCode 0x4 = some (.aluImm .add a3 a3 0xFFFFFD90, 4) := by decide
theorem nsm_at_8 : fetchRel p384ScalarMulCode 0x8 = some (.lui a4 0xE88FE000, 4) := by decide
theorem nsm_at_c : fetchRel p384ScalarMulCode 0xC = some (.aluImm .add a4 a4 0xFFFFFC45, 4) := by decide
theorem nsm_at_10 : fetchRel p384ScalarMulCode 0x10 = some (.auipc (6 : Fin 32) 0xFFFFF000, 4) := by decide
theorem nsm_at_14 : fetchRel p384ScalarMulCode 0x14 = some (.jalr x0 (6 : Fin 32) 0xFFFFFF48, 4) := by decide
theorem nsn_at_0 : fetchRel p384ScalarNewCode 0x0 = some (.lui a3 0x3FCC5000, 4) := by decide
theorem nsn_at_4 : fetchRel p384ScalarNewCode 0x4 = some (.aluImm .add a3 a3 0xFFFFFD90, 4) := by decide
theorem nsn_at_8 : fetchRel p384ScalarNewCode 0x8 = some (.aluImm .add a2 a3 0x60, 4) := by decide
theorem nsn_at_c : fetchRel p384ScalarNewCode 0xC = some (.lui a4 0xE88FE000, 4) := by decide
theorem nsn_at_10 : fetchRel p384ScalarNewCode 0x10 = some (.aluImm .add a4 a4 0xFFFFFC45, 4) := by decide
theorem nsn_at_14 : fetchRel p384ScalarNewCode 0x14 = some (.auipc (6 : Fin 32) 0xFFFFF000, 4) := by decide
theorem nsn_at_18 : fetchRel p384ScalarNewCode 0x18 = some (.jalr x0 (6 : Fin 32) 0xFFFFFE50, 4) := by decide
end

/-- The order of P-384's group. -/
def n384 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973

/-- `(2 ^ 384)⁻¹ mod n`. -/
def n3RInv : Nat :=
  0x355ca87de39dbb1fa150206ce4f194ac78d4ba5866d61787e29f9fb70a9da219d26d4aeba664edb0610ae855f2c0d911

/-- `2 ^ 768 mod n`, which the image keeps for `new`. -/
def n3R2 : Nat :=
  0xc84ee012b39bf213fb05b7a28266895d40d49174aab1cc5bc3e483afcb82947ff3d81e5df1aa4192d319b2419b409a9

set_option exponentiation.threshold 800 in
theorem n3R2_eq : n3R2 = 2 ^ 768 % n384 := by unfold n3R2 n384; decide

/-- The Montgomery product `a · b · 2^-384 mod n`. -/
def n3fm (a b : Nat) : Nat := a * b * n3RInv % n384

abbrev n3M : Word := BitVec.ofNat 32 p384OrderAddress
abbrev n3R2A : Word := BitVec.ofNat 32 p384ScalarR2Address

set_option exponentiation.threshold 600 in
theorem n384_pos : 0 < n384 := by unfold n384; decide

set_option exponentiation.threshold 600 in
theorem n3_mont {R A B : Nat} (hR : R < n384) (h : (R * 2 ^ 384) % n384 = (A * B) % n384) : R = n3fm A B := by
  have hinv : (2 ^ 384 * n3RInv) % n384 = 1 := by unfold n384 n3RInv; decide
  unfold n3fm
  calc R = R % n384 := (Nat.mod_eq_of_lt hR).symm
    _ = (R * ((2 ^ 384 * n3RInv) % n384)) % n384 := by rw [hinv, Nat.mul_one]
    _ = (R * 2 ^ 384 * n3RInv) % n384 := by rw [Nat.mul_mod_mod, Nat.mul_assoc]
    _ = ((R * 2 ^ 384) % n384 * n3RInv) % n384 := by rw [Nat.mod_mul_mod]
    _ = ((A * B) % n384 * n3RInv) % n384 := by rw [h]
    _ = (A * B * n3RInv) % n384 := by rw [Nat.mod_mul_mod]

set_option exponentiation.threshold 600 in
/-- Multiplying by `R² mod n` puts a value in Montgomery form. -/
theorem n3fm_R2 (A : Nat) : n3fm A n3R2 = A * 2 ^ 384 % n384 := by
  have h : (n3R2 * n3RInv) % n384 = 2 ^ 384 % n384 := by unfold n3R2 n3RInv n384; decide
  unfold n3fm
  rw [Nat.mul_assoc, Nat.mul_mod, h, ← Nat.mul_mod]

theorem n3M_w0 {M : Word → BitVec 8} (h : CodeIn M n3M p384OrderData) : memLoad32 M n3M = 0xCCC52973 := by
  have b0 : M n3M = byteAt p384OrderData 0 := by have := h 0 (by decide); rwa [add_ofNat_zero] at this
  have b1 : M (n3M + 1) = byteAt p384OrderData 1 := h 1 (by decide)
  have b2 : M (n3M + 2) = byteAt p384OrderData 2 := h 2 (by decide)
  have b3 : M (n3M + 3) = byteAt p384OrderData 3 := h 3 (by decide)
  unfold memLoad32
  rw [b3, b2, b1, b0]
  decide

set_option exponentiation.threshold 600 in
theorem n3M_val {M : Word → BitVec 8} (h : CodeIn M n3M p384OrderData) : accV M n3M 12 = n384 := by
  have he : ∀ i : Fin 12, (byteAt p384OrderData (4 * i.val + 3) ++ byteAt p384OrderData (4 * i.val + 2) ++
      byteAt p384OrderData (4 * i.val + 1) ++ byteAt p384OrderData (4 * i.val)) =
      BitVec.ofNat 32 ((n384 / 2 ^ (32 * i.val)) % 2 ^ 32) := by decide +kernel
  have hw : ∀ i, i < 12 → memLoad32 M (n3M + BitVec.ofNat 32 (4 * i)) =
      BitVec.ofNat 32 ((n384 / 2 ^ (32 * i)) % 2 ^ 32) := fun i hi => by
    rw [← he ⟨i, hi⟩]
    unfold memLoad32
    have hl : p384OrderData.length = 48 := rfl
    have b0 := h (4 * i) (by omega)
    have b1 : M (n3M + BitVec.ofNat 32 (4 * i) + 1) = byteAt p384OrderData (4 * i + 1) := by
      rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    have b2 : M (n3M + BitVec.ofNat 32 (4 * i) + 2) = byteAt p384OrderData (4 * i + 2) := by
      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    have b3 : M (n3M + BitVec.ofNat 32 (4 * i) + 3) = byteAt p384OrderData (4 * i + 3) := by
      rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    rw [b3, b2, b1, b0]
  simp only [accV]
  rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide),
    hw 6 (by decide), hw 7 (by decide), hw 8 (by decide), hw 9 (by decide), hw 10 (by decide), hw 11 (by decide)]
  decide

set_option exponentiation.threshold 600 in
theorem n3R2_val {M : Word → BitVec 8} (h : CodeIn M n3R2A p384ScalarR2Data) : accV M n3R2A 12 = n3R2 := by
  have he : ∀ i : Fin 12, (byteAt p384ScalarR2Data (4 * i.val + 3) ++ byteAt p384ScalarR2Data (4 * i.val + 2) ++
      byteAt p384ScalarR2Data (4 * i.val + 1) ++ byteAt p384ScalarR2Data (4 * i.val)) =
      BitVec.ofNat 32 ((n3R2 / 2 ^ (32 * i.val)) % 2 ^ 32) := by decide +kernel
  have hw : ∀ i, i < 12 → memLoad32 M (n3R2A + BitVec.ofNat 32 (4 * i)) =
      BitVec.ofNat 32 ((n3R2 / 2 ^ (32 * i)) % 2 ^ 32) := fun i hi => by
    rw [← he ⟨i, hi⟩]
    unfold memLoad32
    have hl : p384ScalarR2Data.length = 48 := rfl
    have b0 := h (4 * i) (by omega)
    have b1 : M (n3R2A + BitVec.ofNat 32 (4 * i) + 1) = byteAt p384ScalarR2Data (4 * i + 1) := by
      rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    have b2 : M (n3R2A + BitVec.ofNat 32 (4 * i) + 2) = byteAt p384ScalarR2Data (4 * i + 2) := by
      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    have b3 : M (n3R2A + BitVec.ofNat 32 (4 * i) + 3) = byteAt p384ScalarR2Data (4 * i + 3) := by
      rw [show (3 : Word) = BitVec.ofNat 32 3 from rfl, add_ofNat_assoc]; exact h _ (by omega)
    rw [b3, b2, b1, b0]
  simp only [accV]
  rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide),
    hw 6 (by decide), hw 7 (by decide), hw 8 (by decide), hw 9 (by decide), hw 10 (by decide), hw 11 (by decide)]
  decide

/-- Where `ConstMontyForm<p384::ScalarParams, 12>::mul` runs: its code at
`P`, and `mul_montgomery_form::<12>`'s environment with the order where the
image puts it. -/
structure N3MEnv (M : Word → BitVec 8) (P sp0 out xp yp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384ScalarMulCode
  nmod : CodeIn M n3M p384OrderData
  mm : MMEnv M (P + 0xFFFFEF58) sp0 out xp yp n3M

/-- **The compiled `ConstMontyForm<p384::ScalarParams, 12>::mul`**, called
with the result at `out` and operands `A` at `xp` and `B < n` at `yp`,
stores `n3fm A B`: the Montgomery product modulo P-384's order. It returns
with `sp`, `ra`, `gp`, `tp`, and `s0` through `s11` as they were, and changes
no memory outside the 0xF0 bytes of stack below `sp` and the result. -/
theorem p384ScalarMul_correct (m : Machine) {P sp0 out xp yp retAddr : Word}
    (env : N3MEnv m.mem P sp0 out xp yp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (ha2 : reg m a2 = yp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hB : accV m.mem yp 12 < n384) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      accV m'.mem out 12 = n3fm (accV m.mem xp 12) (accV m.mem yp 12) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.lui env.code nsm_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm env.code nsm_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.lui env.code nsm_at_8 (off' := 0xC) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm env.code nsm_at_c (off' := 0x10) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.auipc env.code nsm_at_10 (off' := 0x14) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr env.code nsm_at_14
  have k5 : ∀ q, q ≠ a3 → q ≠ a4 → q ≠ t1 → reg n5 q = reg m q := fun q h3 h4 ht => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u5.self.zero, hz]
    · rw [u5.regs, upd_ne h0 ht, u4.regs, upd_ne h0 h4, u3.regs, upd_ne h0 h4, u2.regs, upd_ne h0 h3, u1.regs,
        upd_ne h0 h3]
  have e3 : reg n5 a3 = n3M := by
    rw [u5.regs, upd_ne (by decide) (by decide), u4.regs, upd_ne (by decide) (by decide), u3.regs,
      upd_ne (by decide) (by decide), u2.regs, upd_same (by decide), u1.regs, upd_same (by decide)]; rfl
  have e4 : reg n5 a4 = 0xE88FDC45 := by
    rw [u5.regs, upd_ne (by decide) (by decide), u4.regs, upd_same (by decide), u3.regs, upd_same (by decide)]; rfl
  have et : reg n5 t1 = P + BitVec.ofNat 32 0x10 + 0xFFFFF000 := by rw [u5.regs, upd_same (by decide)]
  have pcA : n6.pc = P + 0xFFFFEF58 := by
    rw [pc6, et, BitVec.add_assoc, BitVec.add_assoc]
    exact even_clear _ (even_at P env.hP 0xFFFFEF58 (by decide))
  have hk : ((0xE88FDC45 : Word).toNat * (memLoad32 n6.mem n3M).toNat + 1) % 2 ^ 32 = 0 := by
    rw [mem6, n3M_w0 env.nmod]; decide
  obtain ⟨n7, c7, pc7, sp7, lt7, val7, fr7, k7⟩ := mulMont12_correct n6 (by rw [mem6]; exact env.mm) pcA
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide), ha0])
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide), ha1])
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide), ha2]) (by rw [regs6, e3]) (by rw [regs6, e4])
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide), hra]) hret
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide), hsp]) hk
    (by rw [mem6, n3M_val env.nmod]; exact hB)
  rw [mem6, n3M_val env.nmod] at lt7 val7
  rw [mem6] at fr7
  refine ⟨n7, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c7))))), pc7, sp7, fun q hq => ?_,
    n3_mont lt7 val7, fr7⟩
  have h : q ≠ a3 ∧ q ≠ a4 ∧ q ≠ t1 := by revert q; decide
  rw [k7 q hq, regs6, k5 q h.1 h.2.1 h.2.2]

/-- Where `ConstMontyForm<p384::ScalarParams, 12>::new` runs: its code at
`P`, and `mul_montgomery_form::<12>`'s environment with the order and
`R² mod n` where the image puts them. -/
structure N3NEnv (M : Word → BitVec 8) (P sp0 out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p384ScalarNewCode
  nmod : CodeIn M n3M p384OrderData
  r2 : CodeIn M n3R2A p384ScalarR2Data
  mm : MMEnv M (P + 0xFFFFEE64) sp0 out xp n3R2A n3M

/-- **The compiled `ConstMontyForm<p384::ScalarParams, 12>::new`**, called
with the result at `out` and any 12 limbs `A` at `xp`, stores
`A · 2^384 mod n`, `A` in Montgomery form. -/
theorem p384ScalarNew_correct (m : Machine) {P sp0 out xp retAddr : Word}
    (env : N3NEnv m.mem P sp0 out xp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      accV m'.mem out 12 = accV m.mem xp 12 * 2 ^ 384 % n384 ∧
      ∀ x, Sep (sp0 + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.lui env.code nsn_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm env.code nsn_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm env.code nsn_at_8 (off' := 0xC) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.lui env.code nsn_at_c (off' := 0x10) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm env.code nsn_at_10 (off' := 0x14) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.auipc env.code nsn_at_14 (off' := 0x18) (by decide)
  obtain ⟨n7, d7, pc7, mem7, regs7⟩ := u6.self.jalr env.code nsn_at_18
  have k6 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ t1 → reg n6 q = reg m q := fun q h2 h3 h4 ht => by
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u6.self.zero, hz]
    · rw [u6.regs, upd_ne h0 ht, u5.regs, upd_ne h0 h4, u4.regs, upd_ne h0 h4, u3.regs, upd_ne h0 h2, u2.regs,
        upd_ne h0 h3, u1.regs, upd_ne h0 h3]
  have e3 : reg n6 a3 = n3M := by
    rw [u6.regs, upd_ne (by decide) (by decide), u5.regs, upd_ne (by decide) (by decide), u4.regs,
      upd_ne (by decide) (by decide), u3.regs, upd_ne (by decide) (by decide), u2.regs, upd_same (by decide),
      u1.regs, upd_same (by decide)]; rfl
  have e2 : reg n6 a2 = n3R2A := by
    rw [u6.regs, upd_ne (by decide) (by decide), u5.regs, upd_ne (by decide) (by decide), u4.regs,
      upd_ne (by decide) (by decide), u3.regs, upd_same (by decide), u2.regs, upd_same (by decide), u1.regs,
      upd_same (by decide)]; rfl
  have e4 : reg n6 a4 = 0xE88FDC45 := by
    rw [u6.regs, upd_ne (by decide) (by decide), u5.regs, upd_same (by decide), u4.regs, upd_same (by decide)]; rfl
  have et : reg n6 t1 = P + BitVec.ofNat 32 0x14 + 0xFFFFF000 := by rw [u6.regs, upd_same (by decide)]
  have pcA : n7.pc = P + 0xFFFFEE64 := by
    rw [pc7, et, BitVec.add_assoc, BitVec.add_assoc]
    exact even_clear _ (even_at P env.hP 0xFFFFEE64 (by decide))
  have hk : ((0xE88FDC45 : Word).toNat * (memLoad32 n7.mem n3M).toNat + 1) % 2 ^ 32 = 0 := by
    rw [mem7, n3M_w0 env.nmod]; decide
  obtain ⟨n8, c8, pc8, sp8, lt8, val8, fr8, k8⟩ := mulMont12_correct n7 (by rw [mem7]; exact env.mm) pcA
    (by rw [regs7, k6 _ (by decide) (by decide) (by decide) (by decide), ha0])
    (by rw [regs7, k6 _ (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [regs7, e2]) (by rw [regs7, e3]) (by rw [regs7, e4])
    (by rw [regs7, k6 _ (by decide) (by decide) (by decide) (by decide), hra]) hret
    (by rw [regs7, k6 _ (by decide) (by decide) (by decide) (by decide), hsp]) hk
    (by rw [mem7, n3M_val env.nmod, n3R2_val env.r2]; unfold n3R2 n384; decide)
  rw [mem7, n3M_val env.nmod] at lt8
  rw [mem7, n3M_val env.nmod, n3R2_val env.r2] at val8
  rw [mem7] at fr8
  refine ⟨n8, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c8)))))), pc8, sp8,
    fun q hq => ?_, by rw [n3_mont lt8 val8, n3fm_R2], fr8⟩
  have h : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ t1 := by revert q; decide
  rw [k8 q hq, regs7, k6 q h.1 h.2.1 h.2.2.1 h.2.2.2]

end C3.RV32
