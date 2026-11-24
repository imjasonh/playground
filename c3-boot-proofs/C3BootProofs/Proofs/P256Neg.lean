import C3BootProofs.Proofs.FieldSubOp

/-!
# P-256's `FieldElement::neg`, as compiled

`<p256::arithmetic::field::FieldElement>::neg` tail-calls the proved
`field_impl::sub` with `FieldElement::ZERO`, 32 zero bytes in the image's
data, as the left operand. For an operand below `p` it returns `p - x` for a
nonzero `x` and 0 for zero.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem pn_at_0 : fetchRel p256FieldNegCode 0x0 = some (.alu .add a2 x0 a1, 2) := by decide
theorem pn_at_2 : fetchRel p256FieldNegCode 0x2 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem pn_at_6 : fetchRel p256FieldNegCode 0x6 = some (.aluImm .add a1 a1 0x1B8, 4) := by decide
theorem pn_at_a : fetchRel p256FieldNegCode 0xA = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem pn_at_e : fetchRel p256FieldNegCode 0xE = some (.jalr x0 (6 : Fin 32) 0x8, 4) := by decide
end

theorem pn_data_word {M : Word → BitVec 8} {a : Nat} {d : List Nat} (h : CodeIn M (BitVec.ofNat 32 a) d)
    (ha : a + d.length < 2 ^ 32) (i : Nat) (hi : 4 * i + 4 ≤ d.length) :
    memLoad32 M (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i)) =
      memLoad32 (fun x => byteAt d (x - BitVec.ofNat 32 a).toNat) (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i)) :=
  memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc, h _ (by omega), BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]

theorem pn_zero_words : ∀ i : Fin 8,
    memLoad32 (fun x => byteAt p256ZeroData (x - BitVec.ofNat 32 p256ZeroAddress).toNat)
      (BitVec.ofNat 32 p256ZeroAddress + BitVec.ofNat 32 (4 * i.val)) = 0 := by decide

/-- `FieldElement::ZERO` in memory is the number 0. -/
theorem pn_zero_val {M : Word → BitVec 8} (h : CodeIn M (BitVec.ofNat 32 p256ZeroAddress) p256ZeroData) :
    limbVal (wordsAt M (BitVec.ofNat 32 p256ZeroAddress) 8) = 0 := by
  have hw : ∀ i, i < 8 → memLoad32 M (BitVec.ofNat 32 p256ZeroAddress + BitVec.ofNat 32 (4 * i)) = 0 := fun i hi => by
    rw [pn_data_word h (by decide) i (by show 4 * i + 4 ≤ 32; omega)]; exact pn_zero_words ⟨i, hi⟩
  unfold wordsAt
  rw [List.map_congr_left (g := fun _ => (0 : Word)) (fun i hi => hw i (List.mem_range.mp hi))]
  rfl

set_option exponentiation.threshold 300 in
/-- Negating a field element below `p` with `subGen` from 0 gives `(p - x) mod p`. -/
theorem p256_subGen_zero {x : Nat} (hx : x < p256) : subGen 0 x = (p256 - x) % p256 := by
  unfold subGen
  by_cases h : 0 < x
  · have h256 : p256 < 2 ^ 256 := by decide
    rw [ite_eq_left h, Nat.mod_eq_of_lt (show p256 - x < p256 by omega),
      show 0 + 2 ^ 288 + p256 - x = (p256 - x) + 2 ^ 256 * 2 ^ 32 by
        rw [show (2 : Nat) ^ 288 = 2 ^ 256 * 2 ^ 32 from rfl]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h, show x = 0 by omega, Nat.zero_mod, Nat.sub_zero, Nat.mod_self]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `FieldElement::neg`**: it stores `subGen 0 x` of the
operand at `bp` at `res`, which is `(p - x) mod p` for `x < p`, through the
proved `field_impl::sub`. -/
theorem p256FieldNeg_correct (m : Machine) {P sp0 res bp retAddr : Word} (hP : P.toNat % 2 = 0)
    (hc : CodeIn m.mem P p256FieldNegCode) (env : FSEnv m.mem (P + 0x12) sp0 res (BitVec.ofNat 32 p256ZeroAddress) bp)
    (hz : CodeIn m.mem (BitVec.ofNat 32 p256ZeroAddress) p256ZeroData)
    (hpc : m.pc = P) (ha0 : reg m a0 = res) (ha1 : reg m a1 = bp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem res 8) = subGen 0 (limbVal (wordsAt m.mem bp 8)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep res 32 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz0 := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.alu hc pn_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.lui hc pn_at_2 (off' := 6) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc pn_at_6 (off' := 0xA) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.auipc hc pn_at_a (off' := 0xE) (by decide)
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.self.jalr hc pn_at_e
  have k4 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ t1 → reg n4 q = reg m q := fun q h1 h2 h6 => by
    rw [u4.regs, updz u3.self.zero h6, u3.regs, updz u2.self.zero h1, u2.regs, updz u1.self.zero h1, u1.regs,
      updz hz0 h2]
  have k5 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ t1 → reg n5 q = reg m q := fun q h1 h2 h6 => by rw [regs5]; exact k4 q h1 h2 h6
  have pc5' : n5.pc = P + 0x12 := by
    rw [pc5, u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0xA + 0x0 + 0x8 = P + 0x12 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P hP 0x12 (by decide))
  obtain ⟨m', c', pc', sp', k', v', f'⟩ := fieldSub_correct n5 (by rw [mem5]; exact env) pc5'
    (by rw [k5 a0 (by decide) (by decide) (by decide), ha0])
    (by rw [regs5, u4.regs, updz u3.self.zero (by decide), u3.regs]; simp +decide only [upd, ↓reduceIte]
        rw [u2.regs]; simp +decide only [upd, ↓reduceIte])
    (by rw [regs5, u4.regs, updz u3.self.zero (by decide), u3.regs, updz u2.self.zero (by decide), u2.regs,
          updz u1.self.zero (by decide), u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [hz0, ha1]; exact BitVec.zero_add bp)
    (by rw [k5 ra (by decide) (by decide) (by decide), hra]) hret
    (by rw [k5 sp (by decide) (by decide) (by decide), hsp])
  rw [mem5, pn_zero_val hz] at v'
  rw [mem5] at f'
  refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c')))), pc', sp', fun q h0 h1 h2 h3 h4 h5 h6 h7 ht0 ht1 => ?_,
    v', f'⟩
  rw [k' q h0 h1 h2 h3 h4 h5 h6 h7 ht0]; exact k5 q h1 h2 ht1

end C3.RV32
