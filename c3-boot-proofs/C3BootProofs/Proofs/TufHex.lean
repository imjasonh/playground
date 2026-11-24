import C3BootProofs.Proofs.DerTlv
import C3BootProofs.Hex

/-!
# TUF hex digits, as compiled

`tuf::hex_value` maps a byte to its value as a lowercase hex digit and
returns `Option<u8>` as a tag in `a0` and the value in `a1`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem thv_at_0 : fetchRel tufHexValueCode 0x0 = some (.aluImm .add a4 x0 0xA, 2) := by decide
theorem thv_at_2 : fetchRel tufHexValueCode 0x2 = some (.aluImm .add a1 a0 0xFFFFFFD0, 4) := by decide
theorem thv_at_6 : fetchRel tufHexValueCode 0x6 = some (.aluImm .add a2 a0 0xFFFFFF9F, 4) := by decide
theorem thv_at_a : fetchRel tufHexValueCode 0xA = some (.aluImm .and a5 a1 0xFF, 4) := by decide
theorem thv_at_e : fetchRel tufHexValueCode 0xE = some (.aluImm .and a3 a2 0xFF, 4) := by decide
theorem thv_at_12 : fetchRel tufHexValueCode 0x12 = some (.aluImm .sltu a2 a5 0xA, 4) := by decide
theorem thv_at_16 : fetchRel tufHexValueCode 0x16 = some (.aluImm .sltu a3 a3 0x6, 4) := by decide
theorem thv_at_1a : fetchRel tufHexValueCode 0x1A = some (.branch .bltu a5 a4 0x8, 4) := by decide
theorem thv_at_1e : fetchRel tufHexValueCode 0x1E = some (.aluImm .add a1 a0 0xFFFFFFA9, 4) := by decide
theorem thv_at_22 : fetchRel tufHexValueCode 0x22 = some (.alu .or a0 a2 a3, 4) := by decide
theorem thv_at_26 : fetchRel tufHexValueCode 0x26 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The tag `hex_value` computes for the byte `x`. -/
def thvTag (x : Word) : Word :=
  aluEval .or (aluEval .sltu ((x + 0xFFFFFFD0) &&& 0xFF) 0xA) (aluEval .sltu ((x + 0xFFFFFF9F) &&& 0xFF) 0x6)

/-- The value `hex_value` computes for the byte `x`. -/
def thvVal (x : Word) : Word :=
  if branchTaken .bltu ((x + 0xFFFFFFD0) &&& 0xFF) 0xA then x + 0xFFFFFFD0 else x + 0xFFFFFFA9

/-- Whether `hex_value`'s tag and value agree with `hexDigit` at byte `c`. -/
def thvOk (c : Nat) : Bool :=
  (thvTag (BitVec.ofNat 32 c) == if (hexDigit c).isSome then 1 else 0) &&
    (hexDigit c).all (fun d => thvVal (BitVec.ofNat 32 c) == BitVec.ofNat 32 d)

theorem thv_t0 : ∀ i, i < 64 → thvOk i = true := by decide
theorem thv_t1 : ∀ i, i < 64 → thvOk (64 + i) = true := by decide
theorem thv_t2 : ∀ i, i < 64 → thvOk (128 + i) = true := by decide
theorem thv_t3 : ∀ i, i < 64 → thvOk (192 + i) = true := by decide

theorem thv_spec {c : Nat} (hc : c < 256) :
    thvTag (BitVec.ofNat 32 c) = (if (hexDigit c).isSome then 1 else 0) ∧
      ∀ d, hexDigit c = some d → thvVal (BitVec.ofNat 32 c) = BitVec.ofNat 32 d := by
  have h : thvOk c = true := by
    rcases Nat.lt_or_ge c 64 with h1 | h1
    · exact thv_t0 c h1
    rcases Nat.lt_or_ge c 128 with h2 | h2
    · have := thv_t1 (c - 64) (by omega); rwa [show 64 + (c - 64) = c by omega] at this
    rcases Nat.lt_or_ge c 192 with h3 | h3
    · have := thv_t2 (c - 128) (by omega); rwa [show 128 + (c - 128) = c by omega] at this
    · have := thv_t3 (c - 192) (by omega); rwa [show 192 + (c - 192) = c by omega] at this
  unfold thvOk at h
  rw [Bool.and_eq_true] at h
  refine ⟨eq_of_beq h.1, fun d hd => ?_⟩
  have h2 := h.2
  rw [hd, Option.all_some] at h2
  exact eq_of_beq h2

/-- **The compiled `tuf::hex_value`**: called with a byte `c` in `a0`, it
returns 1 in `a0` when `c` is a lowercase hex digit (`hexDigit c` is some
value) and 0 otherwise, and then the digit's value in `a1`. It writes no
memory and only `a0` through `a5`. -/
theorem tufHexValue_correct (m : Machine) {base retAddr : Word} {c : Nat} (hc : c < 256)
    (hcode : CodeIn m.mem base tufHexValueCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = BitVec.ofNat 32 c) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = m.mem ∧
      reg m' a0 = (if (hexDigit c).isSome then 1 else 0) ∧
      (∀ d, hexDigit c = some d → reg m' a1 = BitVec.ofNat 32 d) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, c1, u1⟩ := St.block [.aluImm .add a4 x0 0xA, .aluImm .add a1 a0 0xFFFFFFD0,
    .aluImm .add a2 a0 0xFFFFFF9F, .aluImm .and a5 a1 0xFF, .aluImm .and a3 a2 0xFF,
    .aluImm .sltu a2 a5 0xA, .aluImm .sltu a3 a3 0x6] s0 hcode (off' := 0x1A) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have spec := thv_spec hc
  have frame : ∀ (n : Machine) (off : Nat) (f : Fin 32 → Word), St m.mem base n off f →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → f r = reg m r) →
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n r = reg m r :=
    fun n _ f u hf r h0 h1 h2 h3 h4 h5 => by rw [u.regs]; exact hf r h0 h1 h2 h3 h4 h5
  have fin : ∀ (n : Machine) (f : Fin 32 → Word), St m.mem base n 0x22 f → f a2 = aluEval .sltu
      ((BitVec.ofNat 32 c + 0xFFFFFFD0) &&& 0xFF) 0xA → f a3 = aluEval .sltu
      ((BitVec.ofNat 32 c + 0xFFFFFF9F) &&& 0xFF) 0x6 → f a1 = thvVal (BitVec.ofNat 32 c) →
      f ra = retAddr →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → f r = reg m r) →
      ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ m'.mem = m.mem ∧
        reg m' a0 = (if (hexDigit c).isSome then 1 else 0) ∧
        (∀ d, hexDigit c = some d → reg m' a1 = BitVec.ofNat 32 d) ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r := by
    intro n f u fa2 fa3 fa1 fra fk
    obtain ⟨n1, d1, u1⟩ := u.alu hcode thv_at_22 (off' := 0x26) (by decide)
    obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.jalr hcode thv_at_26
    refine ⟨n2, .cons d1 (.single d2), ?_, by rw [mem2], ?_, fun d hd => ?_,
      fun r h0 h1 h2 h3 h4 h5 => ?_⟩
    · rw [pc2, upd_ne' (by decide) u.zero, fra, add_lit_zero, hret]
    · rw [regs2]; simp +decide only [upd_app, ↓reduceIte]; rw [fa2, fa3]; exact spec.1
    · rw [regs2, upd_ne' (by decide) u.zero, fa1]; exact spec.2 d hd
    · rw [regs2, upd_ne' h0 u.zero]; exact fk r h0 h1 h2 h3 h4 h5
  have k1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n1 r = reg m r := by
    intro r h0 h1 h2 h3 h4 h5
    rw [u1.regs, upd_ne' h3 (by simp [upd, hz]), upd_ne' h2 (by simp [upd, hz]),
      upd_ne' h3 (by simp [upd, hz]), upd_ne' h5 (by simp [upd, hz]), upd_ne' h2 (by simp [upd, hz]),
      upd_ne' h1 (by simp [upd, hz]), upd_ne' h4 hz]
  by_cases hb : branchTaken .bltu ((BitVec.ofNat 32 c + 0xFFFFFFD0) &&& 0xFF) 0xA = true
  · obtain ⟨n2, d2, u2⟩ := u1.taken hcode 0x22 thv_at_1a (by decide) (by
      simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ha0]; exact hb)
    obtain ⟨m', c', h⟩ := fin n2 _ u2.self (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; try rfl)
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; try rfl)
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; unfold thvVal; rw [if_pos hb]; rfl)
      (by rw [u2.regs, ← u1.regs]; exact k1 ra (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) |>.trans hra)
      (fun r h0 h1 h2 h3 h4 h5 => by rw [u2.regs, ← u1.regs]; exact k1 r h0 h1 h2 h3 h4 h5)
    exact ⟨m', c1.trans (.cons d2 c'), h⟩
  · obtain ⟨n2, d2, u2⟩ := u1.notTaken hcode 0x1E thv_at_1a (by decide) (by
      simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ha0]; exact Bool.eq_false_iff.mpr hb)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hcode thv_at_1e (off' := 0x22) (by decide)
    obtain ⟨m', c', h⟩ := fin n3 _ u3.self (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; try rfl)
      (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; try rfl)
      (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; unfold thvVal
          rw [if_neg hb]; rfl)
      (by rw [u3.regs, upd_ne' (by decide) u2.zero, ← u1.regs]
          exact k1 ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans hra)
      (fun r h0 h1 h2 h3 h4 h5 => by
        rw [u3.regs, upd_ne' h1 u2.zero, ← u1.regs]; exact k1 r h0 h1 h2 h3 h4 h5)
    exact ⟨m', c1.trans (.cons d2 (.cons d3 c')), h⟩

end C3.RV32
