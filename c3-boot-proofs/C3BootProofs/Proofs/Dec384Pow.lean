import C3BootProofs.Proofs.Dec384Sq2

/-!
# P-384 point decompression: the windowed exponentiation

`decompress` computes `(x³ + ax + b)^((p + 1) / 4)` in Montgomery form with
crypto-bigint's fixed-window exponentiation: a table of the first 16 powers,
then, for each 4-bit window of the exponent from the top, four squarings
and a multiplication by the table entry the window selects.
-/

namespace C3.RV32.Dq

open C3.Image

set_option maxRecDepth 20000

/-- `f` applied `k` times. -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | k + 1, a => iter f k (f a)

/-- A Montgomery squaring. -/
def msq (w : Nat) : Nat := p3fm w w

theorem iter_msq_lt (k : Nat) : ∀ w, w < p384 → iter msq k w < p384 := by
  induction k with
  | zero => intro w h; exact h
  | succ k ih => intro w _; rw [iter]; exact ih _ (p3fm_lt w w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The four squarings**, from the loop's head at 0x348 with `j` passes
done to its exit at 0x50E: the working value at `S + 0x98C` is squared
`4 - j` more times in Montgomery form. -/
theorem dq_sqr4 {S : Word} (F : DqFrame S) :
    ∀ k j, j + k = 4 → ∀ {M : Word → BitVec 8} {n : Machine}, DqCode M → St M DP n 0x348 (reg n) →
      reg n sp = S → reg n a1 = BitVec.ofNat 32 j →
      reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x98C → reg n (22 : Fin 32) = 12 →
      reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x9BC → reg n (23 : Fin 32) = 0xFFFFFFFF →
      reg n (21 : Fin 32) = S + BitVec.ofNat 32 0x138 → reg n (26 : Fin 32) = S + BitVec.ofNat 32 0x990 →
      reg n (18 : Fin 32) = S + BitVec.ofNat 32 0x9C0 →
      memLoad32 M (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF → accV M (S + BitVec.ofNat 32 0x134) 12 = p384 →
      accV M (S + BitVec.ofNat 32 0x98C) 12 < p384 →
      ∃ n', Steps n n' ∧ St n'.mem DP n' 0x50E (reg n') ∧ DqCode n'.mem ∧
        accV n'.mem (S + BitVec.ofNat 32 0x98C) 12 = iter msq k (accV M (S + BitVec.ofNat 32 0x98C) 12) ∧
        reg n' (18 : Fin 32) = S + BitVec.ofNat 32 0x9C0 ∧
        (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
          Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 → Sep (S + BitVec.ofNat 32 0x98C) 0x90 x 1 → n'.mem x = M x) ∧
        ∀ q, sqKeep q = true → reg n' q = reg n q := by
  intro k
  induction k with
  | zero =>
    intro j hj M n C s rsp ra1 r25 r22 r19 r23 r21 r26 r18 hN0 hN hW
    have j4 : j = 4 := by omega
    subst j4
    obtain ⟨n1, d1, u1⟩ := s.aluImm C.self dp_at_348 (off' := 0x34A) (by decide)
    have e1 : reg n1 a1 = 4 := by rw [u1.regs, updz s.zero (by decide), ra1]; rfl
    have e0 : reg n1 a0 = 4 := by rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [s.zero]; rfl
    obtain ⟨n2, d2, u2⟩ := u1.self.taken C.self 0x50E dp_at_34a (by decide) (by
      show (reg n1 a1 == reg n1 a0) = true; rw [e1, e0]; rfl)
    refine ⟨n2, .cons d1 (.single d2), ⟨u2.pc, by rw [u2.mem], fun _ => rfl⟩, by rw [u2.mem]; exact C,
      by rw [u2.mem]; rfl, by rw [u2.regs, u1.regs, updz s.zero (by decide)]; exact r18,
      fun x _ _ _ _ => by rw [u2.mem], fun q hq => ?_⟩
    rw [u2.regs, u1.regs, updz s.zero (pkeep_ne (r := a0) hq rfl)]
  | succ k ih =>
    intro j hj M n C s rsp ra1 r25 r22 r19 r23 r21 r26 r18 hN0 hN hW
    obtain ⟨n1, d1, u1⟩ := s.aluImm C.self dp_at_348 (off' := 0x34A) (by decide)
    have e1 : reg n1 a1 = BitVec.ofNat 32 j := by rw [u1.regs, updz s.zero (by decide), ra1]
    have e0 : reg n1 a0 = 4 := by rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [s.zero]; rfl
    have hj4 : j < 4 := by omega
    obtain ⟨n2, d2, u2⟩ := u1.self.notTaken C.self 0x34E dp_at_34a (by decide) (by
      show (reg n1 a1 == reg n1 a0) = false
      rw [e1, e0]
      have : ∀ j : Nat, j < 4 → (BitVec.ofNat 32 j == (4 : Word)) = false := by decide
      exact this j hj4)
    have g2 : ∀ q, q ≠ a0 → reg n2 q = reg n q := fun q h => by rw [u2.regs, u1.regs, updz s.zero h]
    have s2 : St M DP n2 0x34E (reg n2) := ⟨u2.pc, by rw [u2.mem], fun _ => rfl⟩
    obtain ⟨n3, c3, u3, C3, hlt, hsq, ha13, h183, fr3, k3⟩ := dq_sq (j := j) C F s2 (by rw [g2 sp (by decide)]; exact rsp)
      (by rw [g2 a1 (by decide)]; exact ra1) (by rw [g2 25 (by decide)]; exact r25) (by rw [g2 22 (by decide)]; exact r22)
      (by rw [g2 19 (by decide)]; exact r19) (by rw [g2 23 (by decide)]; exact r23) (by rw [g2 21 (by decide)]; exact r21)
      (by rw [g2 26 (by decide)]; exact r26) (by rw [g2 18 (by decide)]; exact r18) hN0 (by rw [hN]; exact hW)
    rw [hN] at hlt hsq
    have hv := p3_mont hlt hsq
    have hb16 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
    have hSl := F.lo; have hSh := F.hi
    have sq : ∀ c l d, c + l ≤ 0xA50 → d + 1 ≤ 0xA50 → (c + l ≤ d ∨ d + 1 ≤ c) →
        Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
    have s50 : ∀ d, d + 1 ≤ 0xA50 → Sep (S + 0xFFFFFFB0) 0x50 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
      sep_of_le (by rw [hb16, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)
    have nfr : ∀ i, i < 12 → memLoad32 n3.mem (S + BitVec.ofNat 32 0x134 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M (S + BitVec.ofNat 32 0x134 + BitVec.ofNat 32 (4 * i)) := fun i hi => by
      rw [add_ofNat_assoc]
      refine memLoad32_congr fun q hq => ?_
      rw [add_ofNat_assoc]
      exact fr3 _ (s50 _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
        (sq _ _ _ (by decide) (by omega) (.inr (by omega))) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
    have hN3 : accV n3.mem (S + BitVec.ofNat 32 0x134) 12 = p384 := by rw [← hN]; exact accV_congr2 12 nfr
    have hN03 : memLoad32 n3.mem (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF := by
      have := nfr 0 (by decide); rw [Nat.mul_zero, add_ofNat_zero] at this; rw [this, hN0]
    obtain ⟨n4, c4, u4, C4, hv4, h184, fr4, k4⟩ := ih (j + 1) (by omega) C3 u3
      (by rw [k3 sp rfl, g2 sp (by decide)]; exact rsp) (by rw [ha13, ofNat_succ])
      (by rw [k3 25 rfl, g2 25 (by decide)]; exact r25) (by rw [k3 22 rfl, g2 22 (by decide)]; exact r22)
      (by rw [k3 19 rfl, g2 19 (by decide)]; exact r19) (by rw [k3 23 rfl, g2 23 (by decide)]; exact r23)
      (by rw [k3 21 rfl, g2 21 (by decide)]; exact r21) (by rw [k3 26 rfl, g2 26 (by decide)]; exact r26) h183 hN03 hN3
      (by rw [hv]; exact p3fm_lt _ _)
    refine ⟨n4, .cons d1 (.cons d2 (c3.trans c4)), u4, C4, by rw [hv4, hv, iter]; rfl, h184,
      fun x h50 h3C h62 h98 => by rw [fr4 x h50 h3C h62 h98, fr3 x h50 h3C h62 h98],
      fun q hq => by rw [k4 q hq, k3 q hq, g2 q (pkeep_ne (r := a0) hq rfl)]⟩
end C3.RV32.Dq
