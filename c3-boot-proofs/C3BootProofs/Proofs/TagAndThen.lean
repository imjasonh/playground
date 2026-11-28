import C3BootProofs.Proofs.Sec1Tag
import C3BootProofs.Proofs.MemcpyAny

/-!
# `Result<u8, sec1::Error>::and_then(Tag::from_u8)`, as compiled

The function reads the result at `rp`. An `Ok` byte (the word at `rp` is
`0xFFFFFFFF`) goes to the proved `Tag::from_u8`; an error is copied to `out`
with the proved `memcpy`. Both are tail calls.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem tat_at_0 : fetchRel tagAndThenCode 0x0 = some (.load .lw a2 a1 0x0, 2) := by decide
theorem tat_at_2 : fetchRel tagAndThenCode 0x2 = some (.aluImm .add a3 x0 0xFFFFFFFF, 2) := by decide
theorem tat_at_4 : fetchRel tagAndThenCode 0x4 = some (.branch .beq a2 a3 0x10, 4) := by decide
theorem tat_at_8 : fetchRel tagAndThenCode 0x8 = some (.aluImm .add a2 x0 0x34, 4) := by decide
theorem tat_at_c : fetchRel tagAndThenCode 0xC = some (.auipc (6 : Fin 32) 0x13000, 4) := by decide
theorem tat_at_10 : fetchRel tagAndThenCode 0x10 = some (.jalr x0 (6 : Fin 32) 0x7B8, 4) := by decide
theorem tat_at_14 : fetchRel tagAndThenCode 0x14 = some (.load .lbu a1 a1 0x4, 4) := by decide
theorem tat_at_18 : fetchRel tagAndThenCode 0x18 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem tat_at_1c : fetchRel tagAndThenCode 0x1C = some (.jalr x0 (6 : Fin 32) 0x26, 4) := by decide
end

set_option maxRecDepth 20000 in
/-- **The compiled `Result<u8, sec1::Error>::and_then(Tag::from_u8)`**: for
an `Ok` byte at `rp + 4` it stores `tagFromU8Mem` at `out`, and otherwise it
copies the 0x34-byte error from `rp` to `out`, using the 16 bytes below `sp`. -/
theorem tagAndThen_correct (m : Machine) {base retAddr out rp : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base tagAndThenCode) (ht : CodeIn m.mem (base + 0x3E) tagFromU8Code)
    (hs : CodeIn m.mem (base + 0x137C4) memcpyStubCode)
    (E : McEnv m.mem (base + 0x137C4 + 8) out rp (reg m sp + 0xFFFFFFF0) 0x34)
    (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = rp) (hout : out.toNat % 4 = 0)
    (hrp : rp.toNat % 4 = 0) (sOT : Sep out 8 (base + 0x3E) tagFromU8Code.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' r = reg m r) ∧
      if memLoad32 m.mem rp = 0xFFFFFFFF then m'.mem = tagFromU8Mem m.mem out ((m.mem (rp + 4)).zeroExtend 32)
      else ∀ x, Sep (reg m sp + 0xFFFFFFF0) 16 x 1 → m'.mem x = copyBytes m.mem out rp 0x34 x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.lw hc tat_at_0 (off' := 2) (by decide) (by rw [ha1, add_lit_zero]; exact hrp)
  rw [ha1, add_lit_zero] at u1
  obtain ⟨n2, d2, u2⟩ := u1.aluImm hc tat_at_2 (off' := 4) (by decide)
  have k2 : ∀ q, q ≠ a2 → q ≠ a3 → reg n2 q = reg m q := fun q h2 h3 => by
    rw [u2.regs, upd_ne' h3 (upd_zero _ _ _), updz hz h2]
  have e2a2 : reg n2 a2 = memLoad32 m.mem rp := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  have e2a3 : reg n2 a3 = 0xFFFFFFFF := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  have keep : ∀ r : Fin 32, r.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ a6 ∧ r ≠ a7 ∧ r ≠ t0 ∧ r ≠ t1 ∧
        r ≠ (7 : Fin 32) ∧ r ≠ (28 : Fin 32) ∧ r ≠ (29 : Fin 32) ∧ r ≠ (30 : Fin 32) ∧ r ≠ sp := by decide
  by_cases hok : memLoad32 m.mem rp = 0xFFFFFFFF
  · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x14 tat_at_4 (by decide) (by
      rw [e2a2, e2a3, hok]; rfl)
    obtain ⟨n4, d4, u4⟩ := u3.lbu hc tat_at_14 (off' := 0x18) (by decide)
    obtain ⟨n5, d5, u5⟩ := u4.self.auipc hc tat_at_18 (off' := 0x1C) (by decide)
    obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr hc tat_at_1c
    have pc6' : n6.pc = base + 0x3E := by
      rw [pc6, u5.regs]; simp +decide only [upd, ↓reduceIte]
      rw [show base + BitVec.ofNat 32 0x18 + 0x0 + 0x26 = base + 0x3E by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
      exact even_clear _ (even_at base hP 0x3E (by decide))
    have k6 : ∀ q, q ≠ t1 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n6 q = reg m q := fun q h6 h1 h2 h3 => by
      rw [regs6, u5.regs, upd_ne' h6 u4.self.zero, u4.regs, upd_ne' h1 u3.zero, k2 q h2 h3]
    obtain ⟨m', c', pc', mem', k'⟩ := tagFromU8_correct n6 (out := out) (b := (m.mem (rp + 4)).zeroExtend 32)
      (by rw [mem6]; exact ht) pc6' (by rw [k6 a0 (by decide) (by decide) (by decide) (by decide), ha0])
      (by rw [regs6, u5.regs, upd_ne (by decide) (by decide), u4.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [k2 a1 (by decide) (by decide), ha1]) hout sOT
      (by rw [k6 ra (by decide) (by decide) (by decide) (by decide), hra]) hret
    refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), pc', ?_, fun r hr => ?_, ?_⟩
    · rw [k' sp (by decide) (by decide), k6 sp (by decide) (by decide) (by decide) (by decide)]
    · obtain ⟨_, h1, h2, h3, _, _, _, _, _, h6, _⟩ := keep r hr
      rw [k' r h2 h3, k6 r h6 h1 h2 h3]
    · rw [ite_eq_left hok, mem', mem6]
  · obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x8 tat_at_4 (by decide) (by
      rw [e2a2, e2a3]; simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; exact hok)
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hc tat_at_8 (off' := 0xC) (by decide)
    obtain ⟨n5, d5, u5⟩ := u4.self.auipc hc tat_at_c (off' := 0x10) (by decide)
    obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr hc tat_at_10
    have pc6' : n6.pc = base + 0x137C4 := by
      rw [pc6, u5.regs]; simp +decide only [upd, ↓reduceIte]
      rw [show base + BitVec.ofNat 32 0xC + 0x13000 + 0x7B8 = base + 0x137C4 by
        rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
      exact even_clear _ (even_at base hP 0x137C4 (by decide))
    have k6 : ∀ q, q ≠ t1 → q ≠ a2 → q ≠ a3 → reg n6 q = reg m q := fun q h6 h2 h3 => by
      rw [regs6, u5.regs, upd_ne' h6 u4.self.zero, u4.regs, upd_ne' h2 u3.zero, k2 q h2 h3]
    have sp6 : reg n6 sp = reg m sp := k6 sp (by decide) (by decide) (by decide)
    obtain ⟨m', c', pc', sp', _, f', k'⟩ := memcpy_correct n6 (base + 0x137C4) retAddr out rp 0x34
      (fun i hi => by rw [mem6]; exact hs i hi) (even_at base hP 0x137C4 (by decide)) pc6'
      (by rw [k6 a0 (by decide) (by decide) (by decide), ha0]) (by rw [k6 a1 (by decide) (by decide) (by decide), ha1])
      (by rw [regs6, u5.regs, upd_ne (by decide) (by decide), u4.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [u3.zero]; rfl)
      (by rw [k6 ra (by decide) (by decide) (by decide), hra]) hret (by rw [mem6, sp6]; exact E)
    refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), pc', by rw [sp', sp6],
      fun r hr => ?_, ?_⟩
    · obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, ht0, ht1, h7', h28, h29, h30, hs⟩ := keep r hr
      rw [k' r h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs, k6 r ht1 h2 h3]
    · rw [ite_eq_right hok]; intro x hx; rw [f' x (by rw [sp6]; exact hx), mem6]

end C3.RV32
