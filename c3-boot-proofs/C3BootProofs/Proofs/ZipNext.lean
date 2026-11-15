import C3BootProofs.Proofs.CtAssign

/-!
# `Zip<Skip<IterMut<u8>>, Iter<u8>>::next`, as compiled

The compiled `next` uses the zip's random-access form: it compares the
index at `zp + 0x14` with the length at `zp + 0x18`, and while the index is
below the length it bumps the index and returns a pointer into the first
slice, past the skip count at `zp + 8`, and one into the second slice.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem zn_at_4 : fetchRel zipSkipNextCode 0x4 = some (.branch .bgeu a1 a2 0x1A, 4) := by decide
theorem zn_at_1c : fetchRel zipSkipNextCode 0x1C = some (.jalr x0 ra 0x0, 2) := by decide
theorem zn_at_1e : fetchRel zipSkipNextCode 0x1E = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem zn_at_20 : fetchRel zipSkipNextCode 0x20 = some (.jalr x0 ra 0x0, 2) := by decide
end

def znHead : List BInstr := [.lw a1 a0 0x14, .lw a2 a0 0x18]

def znBody : List BInstr :=
  [.lw a2 a0 0, .lw a3 a0 8, .lw a4 a0 0xC, .aluImm .add a5 a1 1, .sw a0 a5 0x14, .alu .add a0 a2 a1,
   .alu .add a0 a0 a3, .alu .add a1 a1 a4]

section
set_option maxRecDepth 20000
theorem znHead_end : blockEnd zipSkipNextCode 0 znHead = some 4 := by decide
theorem znBody_end : blockEnd zipSkipNextCode 8 znBody = some 0x1C := by decide
end

theorem znBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock znBody (M, f)).1 = memStore32 M (f a0 + 0x14) (aluEval .add (f a1) 1) ∧
    (runBlock znBody (M, f)).2 a0 =
      aluEval .add (aluEval .add (memLoad32 M (f a0 + 0)) (f a1)) (memLoad32 M (f a0 + 8)) ∧
    (runBlock znBody (M, f)).2 a1 = aluEval .add (f a1) (memLoad32 M (f a0 + 0xC)) ∧
    (runBlock znBody (M, f)).2 ra = f ra ∧
    ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → (runBlock znBody (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, znBody]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · have h : ∀ r : Fin 32, r.val ∈ [10, 11, 12, 13, 14, 15] → q ≠ r := fun r hr e => by subst e; exact hq hr
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h a0 (by decide), h a1 (by decide), h a2 (by decide), h a3 (by decide), h a4 (by decide),
        h a5 (by decide)]

set_option maxRecDepth 20000 in
/-- **The compiled `Zip<Skip<IterMut<u8>>, Iter<u8>>::next`**, called with
the zip at `zp`: while its index `i` is below its length, it stores `i + 1`
and returns the pair of pointers `a + i + n` and `b + i`, for the slices'
starts `a` and `b` and the skip count `n`; at the end it returns `None` as a
null first pointer. It changes only `a0` to `a5` and the index. -/
theorem zipSkipNext_correct (m : Machine) {B zp retAddr : Word} (hc : CodeIn m.mem B zipSkipNextCode)
    (hpc : m.pc = B) (ha0 : reg m a0 = zp) (hzp : zp.toNat % 4 = 0)
    (sZC : Sep (zp + 0x14) 4 B zipSkipNextCode.length) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (if (memLoad32 m.mem (zp + 0x14)).ult (memLoad32 m.mem (zp + 0x18)) then
        m'.mem = memStore32 m.mem (zp + 0x14) (memLoad32 m.mem (zp + 0x14) + 1) ∧
        reg m' a0 = memLoad32 m.mem zp + memLoad32 m.mem (zp + 0x14) + memLoad32 m.mem (zp + 8) ∧
        reg m' a1 = memLoad32 m.mem (zp + 0x14) + memLoad32 m.mem (zp + 0xC)
      else m'.mem = m.mem ∧ reg m' a0 = 0) ∧
      ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15] → reg m' q = reg m q := by
  have s0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, c1, u1⟩ := St.block znHead s0 hc znHead_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, znHead, upd, ↓reduceIte, and_true]
    rw [ha0]; exact ⟨aligned_add hzp (k := 0x14) (by decide), aligned_add hzp (k := 0x18) (by decide)⟩)
  have g1 : ∀ q, reg n1 q = (runBlock znHead (m.mem, reg m)).2 q := u1.regs
  have v1 : reg n1 a1 = memLoad32 m.mem (zp + 0x14) := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, znHead, upd, ↓reduceIte]; rw [ha0]
  have v2 : reg n1 a2 = memLoad32 m.mem (zp + 0x18) := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, znHead, upd, ↓reduceIte]; rw [ha0]
  have k1 : ∀ q, q ≠ a1 → q ≠ a2 → reg n1 q = reg m q := fun q h1 h2 => by
    rw [g1]; simp only [runBlock, BInstr.run, znHead]
    rw [updz ((updz hz (by decide)).trans hz) h2, updz hz h1]
  have u1' : St m.mem B n1 4 (reg n1) := u1.self
  have hpcR : ∀ f : Fin 32 → Word, f ra = retAddr → (f ra + 0) &&& ~~~1 = retAddr := fun f h => by
    rw [h, add_lit_zero, hret]
  by_cases hlt : (memLoad32 m.mem (zp + 0x14)).ult (memLoad32 m.mem (zp + 0x18))
  · obtain ⟨n2, d2, u2⟩ := u1'.notTaken hc 8 zn_at_4 (by decide) (by
      rw [v1, v2]; show (!(memLoad32 m.mem (zp + 0x14)).ult (memLoad32 m.mem (zp + 0x18))) = false; rw [hlt]; rfl)
    obtain ⟨n3, c3, u3⟩ := St.block znBody u2 hc znBody_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, znBody, upd, ↓reduceIte, true_and, and_true]
      rw [k1 a0 (by decide) (by decide), ha0, add_lit_zero]
      exact ⟨hzp, aligned_add hzp (k := 8) (by decide), aligned_add hzp (k := 0xC) (by decide),
        aligned_add hzp (k := 0x14) (by decide), sZC⟩)
    obtain ⟨em, e0, e1, era, fr⟩ := znBody_run (M := m.mem) (f := reg n1) u1'.zero
    rw [k1 a0 (by decide) (by decide), ha0, v1] at em e1
    rw [k1 a0 (by decide) (by decide), ha0, v1, add_lit_zero] at e0
    rw [em] at u3
    have hc3 := CodeIn.store32 (v := aluEval .add (memLoad32 m.mem (zp + 0x14)) 1) hc sZC
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc3 zn_at_1c
    refine ⟨n4, c1.trans (.cons d2 (c3.trans (.single d4))), by rw [pc4]; exact hpcR _ (by
      rw [era, k1 ra (by decide) (by decide), hra]), ?_, fun q hq => ?_⟩
    · rw [ite_eq_left hlt]; exact ⟨mem4, by rw [regs4, e0]; rfl, by rw [regs4, e1]; rfl⟩
    · have h : ∀ r : Fin 32, r.val ∈ [10, 11, 12, 13, 14, 15] → q ≠ r := fun r hr e => by subst e; exact hq hr
      rw [regs4, fr q hq, k1 q (h a1 (by decide)) (h a2 (by decide))]
  · rw [Bool.not_eq_true] at hlt
    obtain ⟨n2, d2, u2⟩ := u1'.taken hc 0x1E zn_at_4 (by decide) (by
      rw [v1, v2]; show (!(memLoad32 m.mem (zp + 0x14)).ult (memLoad32 m.mem (zp + 0x18))) = true; rw [hlt]; rfl)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hc zn_at_1e (off' := 0x20) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc zn_at_20
    refine ⟨n4, c1.trans (.cons d2 (.cons d3 (.single d4))), by
      rw [pc4]; exact hpcR _ (by rw [updz u2.zero (by decide), k1 ra (by decide) (by decide), hra]), ?_,
      fun q hq => ?_⟩
    · rw [hlt]; exact ⟨mem4, by rw [regs4]; simp +decide only [upd, ↓reduceIte]; rw [u2.zero]; rfl⟩
    · have h : ∀ r : Fin 32, r.val ∈ [10, 11, 12, 13, 14, 15] → q ≠ r := fun r hr e => by subst e; exact hq hr
      rw [regs4, updz u2.zero (h a0 (by decide)), k1 q (h a1 (by decide)) (h a2 (by decide))]

end C3.RV32
