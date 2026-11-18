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
/-! ## Montgomery powers -/

/-- The Montgomery form of 1. -/
def p3one : Nat := 2 ^ 384 % p384

/-- A Montgomery multiplication by `A`. -/
def mmul (A z : Nat) : Nat := p3fm z A

/-- `A` to the `n` in Montgomery form, as repeated multiplication from 1. -/
def mpow (A n : Nat) : Nat := iter (mmul A) n p3one

set_option exponentiation.threshold 600 in
theorem p3one_lt : p3one < p384 := by unfold p3one p384; decide

set_option exponentiation.threshold 600 in
theorem p3one_inv : p3one * p3RInv % p384 = 1 := by unfold p3one p384 p3RInv; decide

theorem iter_mmul (A n : Nat) : ∀ z, z < p384 → iter (mmul A) n z = z * (A * p3RInv) ^ n % p384 := by
  induction n with
  | zero => intro z h; rw [iter, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt h]
  | succ n ih =>
    intro z _
    rw [iter, ih _ (show mmul A z < p384 from p3fm_lt z A)]
    unfold mmul p3fm
    rw [Nat.mod_mul_mod, Nat.pow_succ]
    congr 1
    ac_rfl

theorem mpow_val (A n : Nat) : mpow A n = p3one * (A * p3RInv) ^ n % p384 := iter_mmul A n _ p3one_lt

theorem mpow_lt (A n : Nat) : mpow A n < p384 := by rw [mpow_val]; exact Nat.mod_lt _ p384_pos

theorem mod3 (X Y R p : Nat) : X % p * (Y % p) * R % p = X * Y * R % p := by
  rw [Nat.mul_mod, Nat.mul_mod (X * Y), Nat.mul_mod X Y]

theorem mpow_add (A a b : Nat) : p3fm (mpow A a) (mpow A b) = mpow A (a + b) := by
  rw [mpow_val, mpow_val, mpow_val]
  unfold p3fm
  rw [mod3, show p3one * (A * p3RInv) ^ a * (p3one * (A * p3RInv) ^ b) * p3RInv =
      (p3one * p3RInv) * (p3one * (A * p3RInv) ^ (a + b)) by rw [Nat.pow_add]; ac_rfl,
    Nat.mul_mod, p3one_inv, Nat.one_mul, Nat.mod_mod]

theorem mpow_one (A : Nat) (h : A < p384) : mpow A 1 = A := by
  rw [mpow_val, Nat.pow_one, show p3one * (A * p3RInv) = A * (p3one * p3RInv) by ac_rfl, Nat.mul_mod, p3one_inv,
    Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt h]

theorem iter_msq_mpow (A k : Nat) : ∀ a, iter msq k (mpow A a) = mpow A (2 ^ k * a) := by
  induction k with
  | zero => intro a; rw [iter, Nat.pow_zero, Nat.one_mul]
  | succ k ih =>
    intro a
    have h2 : msq (mpow A a) = mpow A (2 * a) := by unfold msq; rw [mpow_add, Nat.two_mul]
    rw [iter, h2, ih, Nat.pow_succ, Nat.mul_assoc]

/-! ## One window -/

def dqW1 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x18D, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x15D,
   .aluImm .add a2 x0 0x30]
def dqW2 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x15D, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x18D,
   .aluImm .add a2 x0 0x30]

theorem dqW1_end : blockEnd p384DecompressCode 0x32A dqW1 = some 0x33E := by decide
theorem dqW2_end : blockEnd p384DecompressCode 0x50E dqW2 = some 0x522 := by decide

theorem cp_accV {M M' : Word → BitVec 8} {S : Word} {d c : Nat} (hd : d + 48 ≤ 0xA50) (hc : c + 48 ≤ 0xA50)
    (h : ∀ i, i < 12 → memLoad32 M' (S + BitVec.ofNat 32 (d + 4 * i)) = memLoad32 M (S + BitVec.ofNat 32 (c + 4 * i))) :
    accV M' (S + BitVec.ofNat 32 d) 12 = accV M (S + BitVec.ofNat 32 c) 12 :=
  accV_congr2 12 fun i hi => by rw [add_ofNat_assoc, add_ofNat_assoc, h i hi]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The squarings of a window**, from 0x328 to 0x52C: `z` at `S + 0x95C` is
squared four times in Montgomery form, through the working value at
`S + 0x98C`, with the window's index kept at `S + 0x20`. -/
theorem dq_win_sq {M : Word → BitVec 8} {S : Word} {n : Machine} {w : Word} (C : DqCode M) (F : DqFrame S)
    (s : St M DP n 0x328 (reg n)) (rsp : reg n sp = S) (ra3 : reg n a3 = w)
    (r25 : reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x98C) (r22 : reg n (22 : Fin 32) = 12)
    (r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x9BC) (r23 : reg n (23 : Fin 32) = 0xFFFFFFFF)
    (r21 : reg n (21 : Fin 32) = S + BitVec.ofNat 32 0x138) (r26 : reg n (26 : Fin 32) = S + BitVec.ofNat 32 0x990)
    (r18 : reg n (18 : Fin 32) = S + BitVec.ofNat 32 0x9C0)
    (hN0 : memLoad32 M (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF) (hN : accV M (S + BitVec.ofNat 32 0x134) 12 = p384)
    (hz : accV M (S + BitVec.ofNat 32 0x95C) 12 < p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x52C (reg n') ∧ DqCode n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = iter msq 4 (accV M (S + BitVec.ofNat 32 0x95C) 12) ∧
      reg n' a3 = w ∧ reg n' (18 : Fin 32) = S + BitVec.ofNat 32 0x9C0 ∧
      (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep (S + BitVec.ofNat 32 0x20) 4 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
        Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 → Sep (S + BitVec.ofNat 32 0x95C) 0xC0 x 1 → n'.mem x = M x) ∧
      ∀ q, sqKeep q = true → reg n' q = reg n q := by
  have hz0 := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb50 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide)
  have b16 : ∀ c, c + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFFF0) 16 := fun c hc =>
    (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have w48 : ∀ c, c + 48 ≤ 0xA50 → (S + BitVec.ofNat 32 c).toNat + 48 < 2 ^ 32 := fun c hc => by
    rw [F.at c (by omega)]; omega
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16 : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  -- save the window's index
  obtain ⟨n1, d1, u1⟩ := s.sw C.self dp_at_328 (off' := 0x32A) (by decide)
    (by rw [rsp]; show (S + BitVec.ofNat 32 0x20).toNat % 4 = 0; rw [F.at 0x20 (by decide)]; omega)
  rw [rsp, ra3] at u1
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 M (S + BitVec.ofNat 32 0x20) w = M1 := ⟨_, rfl⟩
  have u1' : St M1 DP n1 0x32A (reg n1) := by rw [← hM1]; exact u1.self
  have h1hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M1 x = M x := fun x hx => by
    rw [← hM1]; exact memStore32_get_sep (F.hiOut (c := 0x20) (n := 4) (by decide) hx)
  have C1 := C.hi h1hi
  have g1 : ∀ q, reg n1 q = reg n q := fun q => by rw [u1.regs]
  -- copy z to the working value
  obtain ⟨n2, c2, u2⟩ := u1'.block dqW1 C1.self dqW1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r2 : ∀ q, reg n2 q = (runBlock dqW1 (M1, reg n1)).2 q := fun q => by rw [u2.regs]
  have sp1 : reg n1 sp = S := by rw [g1]; exact rsp
  obtain ⟨n3, c3, u3, fr3, k3⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x98C) (src := S + BitVec.ofNat 32 0x95C)
    (S := S) (N := 48) (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St M1 DP n2 0x33E (reg n2)) C1 dp_at_33e dp_at_342
    (by decide) (by decide) (by rw [r2, runBlock_reg _ _ _ sp u1'.zero (by decide)]; exact sp1)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqW1, upd, ↓reduceIte]; rw [sp1, spo]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqW1, upd, ↓reduceIte]; rw [sp1, spo]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqW1, upd, ↓reduceIte]; (try rw [u1'.zero]); try rfl)
    ⟨C1.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have h3hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n3.mem x = M x := fun x hx => by
    rw [fr3 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x98C) (n := 48) (by decide) hx) (Nat.le_refl _), h1hi x hx]
  have C3 := C.hi h3hi
  have k3' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n3 q = reg n q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ dqW1.filterMap BInstr.dst := by simp only [dqW1]; revert h0 h1 h2; revert q; decide
      rw [k3 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r2, runBlock_reg _ _ _ q u1'.zero hb, g1]
  have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 8, 9] → reg n3 q = reg n q :=
    fun q hq => k3' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  obtain ⟨n4, d4, u4⟩ := u3.aluImm C3.self dp_at_346 (off' := 0x348) (by decide)
  have g4 : ∀ q, q ≠ a1 → reg n4 q = reg n3 q := fun q h => by rw [u4.regs, updz u3.zero h]
  -- the frame so far, and what the squarings read
  have fr3' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x20) 4 x 1 →
      Sep (S + BitVec.ofNat 32 0x98C) 48 x 1 → n3.mem x = M x := fun x h16 h20 h98 => by
    rw [fr3 x h16, copyBytes_sep h98 (Nat.le_refl _), ← hM1]; exact memStore32_get_sep h20
  have m3 : ∀ d, d + 4 ≤ 0xA50 → (d + 4 ≤ 0x20 ∨ 0x24 ≤ d) → (d + 4 ≤ 0x98C ∨ 0x9BC ≤ d) →
      memLoad32 n3.mem (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := fun d h1 h2 h3 =>
    memLoad32_congr fun q hq => fr3' _ ((l16 d h1).subR (c := q) (l := 1) (by omega))
      ((sepS S (c := 0x20) (n := 4) (d := d) (k := 4) (by omega) (by decide) (by omega)).subR (c := q) (l := 1) (by omega))
      ((sepS S (c := 0x98C) (n := 48) (d := d) (k := 4) (by omega) (by decide) (by omega)).subR (c := q) (l := 1)
        (by omega))
  have hN3 : accV n3.mem (S + BitVec.ofNat 32 0x134) 12 = p384 := by
    rw [← hN]; exact accV_congr2 12 fun i hi => by rw [add_ofNat_assoc, m3 _ (by omega) (.inr (by omega)) (.inl (by omega))]
  have hN03 : memLoad32 n3.mem (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF := by
    rw [m3 _ (by decide) (.inr (by decide)) (.inl (by decide)), hN0]
  have hW3 : accV n3.mem (S + BitVec.ofNat 32 0x98C) 12 = accV M (S + BitVec.ofNat 32 0x95C) 12 := by
    refine cp_accV (by decide) (by decide) fun i hi => ?_
    rw [load_frame fr3 (l16 _ (by omega)), ← add_ofNat_assoc S 0x98C, cp_word (by omega) (by decide), add_ofNat_assoc, ← hM1,
      memLoad32_store32_sep (sepS S (c := 0x20) (n := 4) (d := 0x95C + 4 * i) (k := 4) (.inl (by omega)) (by decide)
        (by omega))]
  obtain ⟨n5, c5, u5, C5, hv5, h185, fr5, k5⟩ := dq_sqr4 F 4 0 (by decide) C3
    (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem DP n4 0x348 (reg n4))
    (by rw [g4 sp (by decide), kk sp (by decide)]; exact rsp) (by rw [u4.regs]; simp +decide [upd]; rw [u3.zero]; rfl)
    (by rw [g4 25 (by decide), kk 25 (by decide)]; exact r25) (by rw [g4 22 (by decide), kk 22 (by decide)]; exact r22)
    (by rw [g4 19 (by decide), kk 19 (by decide)]; exact r19) (by rw [g4 23 (by decide), kk 23 (by decide)]; exact r23)
    (by rw [g4 21 (by decide), kk 21 (by decide)]; exact r21) (by rw [g4 26 (by decide), kk 26 (by decide)]; exact r26)
    (by rw [g4 18 (by decide), kk 18 (by decide)]; exact r18) hN03 hN3 (by rw [hW3]; exact hz)
  rw [hW3] at hv5
  have sp5 : reg n5 sp = S := by rw [k5 sp rfl, g4 sp (by decide), kk sp (by decide)]; exact rsp
  -- copy the working value back to z
  obtain ⟨n6, c6, u6⟩ := u5.block dqW2 C5.self dqW2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock dqW2 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  obtain ⟨n7, c7, u7, fr7, k7⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x95C) (src := S + BitVec.ofNat 32 0x98C)
    (S := S) (N := 48) (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem DP n6 0x522 (reg n6)) C5 dp_at_522 dp_at_526
    (by decide) (by decide) (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqW2, upd, ↓reduceIte]; rw [sp5, spo]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqW2, upd, ↓reduceIte]; rw [sp5, spo]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqW2, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    ⟨C5.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have h7hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n7.mem x = M x := fun x hx => by
    rw [fr7 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x95C) (n := 48) (by decide) hx) (Nat.le_refl _)]
    exact (fr5 x (sep_of_le (by rw [hb50]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x3C) (n := 4) (by decide) hx)
      (F.hiOut (c := 0x62C) (n := 48) (by decide) hx) (F.hiOut (c := 0x98C) (n := 0x90) (by decide) hx)).trans (h3hi x hx)
  have C7 := C.hi h7hi
  have k7' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n7 q = reg n5 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ dqW2.filterMap BInstr.dst := by simp only [dqW2]; revert h0 h1 h2; revert q; decide
      rw [k7 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r6, runBlock_reg _ _ _ q u5.zero hb]
  have sp7 : reg n7 sp = S := by
    rw [k7' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp5
  -- the frame
  have frame : ∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep (S + BitVec.ofNat 32 0x20) 4 x 1 →
      Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 →
      Sep (S + BitVec.ofNat 32 0x95C) 0xC0 x 1 → n7.mem x = M x := by
    intro x h50 h20 h3C h62 h95
    have h16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
      have := h50.sub (c := 0x40) (l := 16) (by decide)
      rwa [show S + 0xFFFFFFB0 + BitVec.ofNat 32 0x40 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
    have h9548 : Sep (S + BitVec.ofNat 32 0x95C) 48 x 1 := by
      have := h95.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
    have h98 : Sep (S + BitVec.ofNat 32 0x98C) 0x90 x 1 := by
      have := h95.sub (c := 0x30) (l := 0x90) (by decide); rwa [add_ofNat_assoc] at this
    have h9848 : Sep (S + BitVec.ofNat 32 0x98C) 48 x 1 := by
      have := h95.sub (c := 0x30) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr7 x h16, copyBytes_sep h9548 (Nat.le_refl _), fr5 x h50 h3C h62 h98, fr3' x h16 h20 h9848]
  have l50 : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFB0) 0x50 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb50, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  -- reload the window's index
  obtain ⟨n8, d8, u8⟩ := u7.lw C7.self dp_at_52a (off' := 0x52C) (by decide)
    (by rw [sp7]; show (S + BitVec.ofNat 32 0x20).toNat % 4 = 0; rw [F.at 0x20 (by decide)]; omega)
  have w20 : memLoad32 n7.mem (S + BitVec.ofNat 32 0x20) = w := by
    have e : memLoad32 n7.mem (S + BitVec.ofNat 32 0x20) = memLoad32 M1 (S + BitVec.ofNat 32 0x20) := by
      rw [load_frame fr7 (l16 _ (by decide)), cp_word_out (sepS S (.inr (by decide)) (by decide) (by decide))]
      refine memLoad32_congr fun q hq => ?_
      rw [fr5 _ ((l50 0x20 (by decide)).subR (c := q) (l := 1) (by omega))
        ((sepS S (c := 0x3C) (n := 4) (d := 0x20) (k := 4) (.inr (by decide)) (by decide) (by decide)).subR (c := q)
          (l := 1) (by omega))
        ((sepS S (c := 0x62C) (n := 48) (d := 0x20) (k := 4) (.inr (by decide)) (by decide) (by decide)).subR (c := q)
          (l := 1) (by omega))
        ((sepS S (c := 0x98C) (n := 0x90) (d := 0x20) (k := 4) (.inr (by decide)) (by decide) (by decide)).subR (c := q)
          (l := 1) (by omega)), fr3 _ ((l16 0x20 (by decide)).subR (c := q) (l := 1) (by omega)),
        copyBytes_sep ((sepS S (c := 0x98C) (n := 48) (d := 0x20) (k := 4) (.inr (by decide)) (by decide)
          (by decide)).subR (c := q) (l := 1) (by omega)) (Nat.le_refl _)]
    rw [e, ← hM1, memLoad32_store32_same]
  refine ⟨n8, .cons d1 (c2.trans (c3.trans (.cons d4 (c5.trans (c6.trans (c7.trans (.single d8))))))),
    ⟨u8.pc, by rw [u8.mem], fun _ => rfl⟩, by rw [u8.mem]; exact C7, ?_, ?_, ?_, fun x h50 h20 h3C h62 h95 => by
      rw [u8.mem]; exact frame x h50 h20 h3C h62 h95, fun q hq => ?_⟩
  · rw [u8.mem, ← hv5]
    refine cp_accV (by decide) (by decide) fun i hi => ?_
    rw [load_frame fr7 (l16 _ (by omega)), ← add_ofNat_assoc S 0x95C, cp_word (by omega) (by decide), add_ofNat_assoc]
  · rw [u8.regs]; simp +decide only [upd, ↓reduceIte]; rw [sp7]; exact w20
  · rw [u8.regs, updz u7.zero (by decide), k7' 18 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h185
  · have hq3 : q ≠ a3 := pkeep_ne (r := a3) hq rfl
    rw [u8.regs, updz u7.zero hq3, k7' q (pkeep_ne (r := a0) hq rfl) (pkeep_ne (r := a1) hq rfl) (pkeep_ne (r := a2) hq rfl)
      hq3 (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := a6) hq rfl) (pkeep_ne (r := a7) hq rfl)
      (pkeep_ne (r := t0) hq rfl) (pkeep_ne (r := t1) hq rfl) (pkeep_ne (r := 7) hq rfl) (pkeep_ne (r := 28) hq rfl)
      (pkeep_ne (r := 29) hq rfl) (pkeep_ne (r := 30) hq rfl) (pkeep_ne (r := ra) hq rfl), k5 q hq,
      g4 q (pkeep_ne (r := a1) hq rfl), kk q (by revert hq; revert q; decide)]

/-! ## Multiplications -/

theorem mm_mset : MM + 0x1B0C = MSET := by decide
theorem mm_bsub : mmBsub MM = BSUB := by decide
theorem mm_sel : MM + 0x18E = SEL := by decide
theorem mm_stub : MM + 0x1B74 = MCS := by decide
theorem mm_body : MM + 0x1B7C = MCS + 8 := by decide

set_option maxRecDepth 100000 in
/-- A call to `mul_montgomery_form::<12>` from `decompress` with the modulus
at `S + 0x134` and factor 1: the 12 words at `out` become the Montgomery
product of the words at `xp` and `yp`. -/
theorem dq_mm {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out xp yp S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = MM) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp) (ha2 : g a2 = yp)
    (ha3 : g a3 = S + BitVec.ofNat 32 0x134) (ha4 : g a4 = 1)
    {co cx cy : Nat} (hco : co + 48 ≤ 0xA50) (hcx : cx + 48 ≤ 0xA50) (hcy : cy + 48 ≤ 0xA50)
    (eo : out = S + BitVec.ofNat 32 co) (ex : xp = S + BitVec.ofNat 32 cx) (ey : yp = S + BitVec.ofNat 32 cy)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (acy : cy % 4 = 0)
    (hN0 : memLoad32 Mx (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF) (hN : accV Mx (S + BitVec.ofNat 32 0x134) 12 = p384)
    (hY : accV Mx yp 12 < p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      accV n'.mem out 12 = p3fm (accV Mx xp 12) (accV Mx yp 12) ∧
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frS : ∀ (cz : Nat), cz + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 cz) 48 (S + 0xFFFFFF10) 0xF0 := fun cz h =>
    (sep_of_le (by rw [hbF, F.at cz (by omega)]; omega) (by rw [F.at cz (by omega)]; omega)).symm
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFF10) 0xF0 b len :=
    fun b len hb hl => sep_of_le (by rw [hbF]; omega) hl
  have E : MMEnv n1.mem MM (reg n1 sp) out xp yp (S + BitVec.ofNat 32 0x134) := by
    rw [sp1, mem1]
    refine ⟨by decide, C.mm, by rw [mm_mset]; exact C.mset, by rw [mm_bsub]; exact C.bsub, by rw [mm_sel]; exact C.sel,
      by rw [mm_stub]; exact C.stub, by rw [mm_body]; exact C.body, by omega, by omega, ?_, ?_, ?_, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [mm_mset]; decide) (by rw [mm_mset]; decide),
      frC _ _ (by rw [mm_bsub]; decide) (by rw [mm_bsub]; decide), frC _ _ (by rw [mm_sel]; decide) (by rw [mm_sel]; decide),
      frC _ _ (by rw [mm_stub]; decide) (by rw [mm_stub]; decide), frC _ _ (by rw [mm_body]; decide)
        (by rw [mm_body]; decide), ?_, ?_, ?_, ?_, ?_, ?_, frS _ (by decide)⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ex, F.at cx (by omega)]; omega
    · rw [ey, F.at cy (by omega)]; omega
    · rw [F.at 0x134 (by decide)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact frS co hco
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, mm_sel]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, mm_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [ex]; exact frS cx hcx
    · rw [ey]; exact frS cy hcy
  obtain ⟨n2, c2, pc2, sp2, hlt, hcg, fr2, k2⟩ := mulMont12_correct (K := 1) n1 E pc1
    (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    (by rw [r1 a4 (by decide)]; exact ha4) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) rfl
    (by rw [mem1, hN0]; decide) (by rw [mem1, hN]; exact hY)
  rw [mem1, hN] at hlt hcg
  rw [mem1] at fr2
  rw [sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, p3_mont hlt hcg, fr2, by rw [sp2, sp1],
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩

/-! ## A window's digit -/

/-- The digit `decompress` reads for window `w` of limb `i`: two bits for
the top window, four otherwise. -/
def dqDig (i w : Nat) (limb : Word) : Word :=
  aluEval .and (if i = 11 ∧ w = 7 then 3 else 15) (aluEval .srl limb (aluEval .sll (BitVec.ofNat 32 w) 2))

theorem dqDig_le (i w : Nat) (limb : Word) : (dqDig i w limb).toNat ≤ 15 := by
  unfold dqDig
  show ((if i = 11 ∧ w = 7 then (3 : Word) else 15) &&& _).toNat ≤ 15
  rw [BitVec.toNat_and]
  refine Nat.le_trans Nat.and_le_left ?_
  by_cases h : i = 11 ∧ w = 7
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

theorem top_test : ∀ i : Nat, i < 12 → ∀ w : Nat, w < 8 →
    branchTaken .beq (aluEval .or (aluEval .xor 7 (BitVec.ofNat 32 w)) (aluEval .xor 11 (BitVec.ofNat 32 i))) 0 =
      decide (i = 11 ∧ w = 7) := by decide

theorem bnd13 : ∀ i : Nat, i < 12 → branchTaken .bgeu (BitVec.ofNat 32 (i + 1)) 13 = false := by decide

def dqD1 : List BInstr := [.lw a0 sp 0x2C, .aluImm .add a1 x0 0xD]
def dqD2 : List BInstr :=
  [.lw a0 sp 0x34, .lw a1 sp 0x38, .alu .xor a0 a0 a1, .lw a1 sp 0x30, .alu .xor a1 a1 a3, .alu .or a1 a1 a0,
   .lw a0 sp 0x24]
def dqD3 : List BInstr := [.lw a1 sp 0x28, .lw a1 a1 0x0, .aluImm .sll a2 a3 0x2, .alu .srl a1 a1 a2, .alu .and a0 a0 a1]

theorem dqD1_end : blockEnd p384DecompressCode 0x52C dqD1 = some 0x530 := by decide
theorem dqD2_end : blockEnd p384DecompressCode 0x534 dqD2 = some 0x542 := by decide
theorem dqD3_end : blockEnd p384DecompressCode 0x546 dqD3 = some 0x554 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A window's digit**, from 0x52C to the test at 0x554: `a0` gets digit
`w` of limb `i` of the exponent, which `S + 0x28` points to. -/
theorem dq_digit {M : Word → BitVec 8} {S : Word} {n : Machine} {i w : Nat} (C : DqCode M) (F : DqFrame S)
    (s : St M DP n 0x52C (reg n)) (rsp : reg n sp = S) (ra3 : reg n a3 = BitVec.ofNat 32 w) (hi : i < 12) (hw : w < 8)
    (s2C : memLoad32 M (S + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 (i + 1))
    (s34 : memLoad32 M (S + BitVec.ofNat 32 0x34) = 11) (s38 : memLoad32 M (S + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 i)
    (s30 : memLoad32 M (S + BitVec.ofNat 32 0x30) = 7) (s24 : memLoad32 M (S + BitVec.ofNat 32 0x24) = 3)
    (s28 : memLoad32 M (S + BitVec.ofNat 32 0x28) = S + BitVec.ofNat 32 (0x5FC + 4 * i)) :
    ∃ n', Steps n n' ∧ St M DP n' 0x554 (reg n') ∧
      reg n' a0 = dqDig i w (memLoad32 M (S + BitVec.ofNat 32 (0x5FC + 4 * i))) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have al : ∀ c, c + 4 ≤ 0xA50 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block dqD1 C.self dqD1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqD1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp]; exact al 0x2C (by decide) (by decide))
  have r1 : ∀ q, reg n1 q = (runBlock dqD1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have t1 : St M DP n1 0x530 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := t1.notTaken C.self 0x534 dp_at_530 (by decide) (by
    rw [r1, r1]; simp +decide only [runBlock, BInstr.run, dqD1, upd, ↓reduceIte]; rw [rsp]
    show branchTaken .bgeu (memLoad32 M (S + BitVec.ofNat 32 0x2C)) 13 = false
    rw [s2C]; exact bnd13 i hi)
  have g2 : ∀ q, reg n2 q = reg n1 q := fun q => by rw [u2.regs]
  have sp2 : reg n2 sp = S := by rw [g2, r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp
  have a32 : reg n2 a3 = BitVec.ofNat 32 w := by rw [g2, r1, runBlock_reg _ _ _ a3 hz (by decide)]; exact ra3
  have t2 : St M DP n2 0x534 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := t2.block dqD2 C.self dqD2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqD2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp2]; exact ⟨al 0x34 (by decide) (by decide), al 0x38 (by decide) (by decide), al 0x30 (by decide) (by decide),
      al 0x24 (by decide) (by decide)⟩)
  have r3 : ∀ q, reg n3 q = (runBlock dqD2 (M, reg n2)).2 q := fun q => by rw [u3.regs]
  have e31 : reg n3 a1 = aluEval .or (aluEval .xor 7 (BitVec.ofNat 32 w)) (aluEval .xor 11 (BitVec.ofNat 32 i)) := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, dqD2, upd, ↓reduceIte]; rw [sp2, a32]
    show aluEval .or (aluEval .xor (memLoad32 M (S + BitVec.ofNat 32 0x30)) _)
      (aluEval .xor (memLoad32 M (S + BitVec.ofNat 32 0x34)) (memLoad32 M (S + BitVec.ofNat 32 0x38))) = _
    rw [s30, s34, s38]
  have e30 : reg n3 a0 = 3 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, dqD2, upd, ↓reduceIte]; rw [sp2]
    show memLoad32 M (S + BitVec.ofNat 32 0x24) = 3; exact s24
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → reg n3 q = reg n2 q := fun q h0 h1 => by
    rw [r3, runBlock_reg _ _ _ q t2.zero (by simp only [dqD2]; revert h0 h1; revert q; decide)]
  have t3 : St M DP n3 0x542 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  -- the mask, along either path to 0x546
  obtain ⟨n4, c4, t4, e40, k4⟩ : ∃ n4, Steps n3 n4 ∧ St M DP n4 0x546 (reg n4) ∧
      reg n4 a0 = (if i = 11 ∧ w = 7 then 3 else 15) ∧ ∀ q, q ≠ a0 → reg n4 q = reg n3 q := by
    have hb := top_test i hi w hw
    rw [← e31, ← t3.zero] at hb
    by_cases ht : i = 11 ∧ w = 7
    · obtain ⟨n4, d4, u4⟩ := t3.taken C.self 0x546 dp_at_542 (by decide) (by rw [hb]; exact decide_eq_true ht)
      exact ⟨n4, .single d4, ⟨u4.pc, u4.mem, fun _ => rfl⟩, by rw [u4.regs, e30, ite_eq_left ht],
        fun q _ => by rw [u4.regs]⟩
    · obtain ⟨n4, d4, u4⟩ := t3.notTaken C.self 0x544 dp_at_542 (by decide) (by rw [hb]; exact decide_eq_false ht)
      obtain ⟨n5, d5, u5⟩ := u4.self.aluImm C.self dp_at_544 (off' := 0x546) (by decide)
      refine ⟨n5, .cons d4 (.single d5), ⟨u5.pc, u5.mem, fun _ => rfl⟩, ?_, fun q h => ?_⟩
      · rw [u5.regs, ite_eq_right ht]; simp +decide only [upd, ↓reduceIte]; rw [u4.self.zero]; rfl
      · rw [u5.regs, updz u4.self.zero h, u4.regs]
  have sp4 : reg n4 sp = S := by rw [k4 sp (by decide), k3 sp (by decide) (by decide), sp2]
  have a34 : reg n4 a3 = BitVec.ofNat 32 w := by rw [k4 a3 (by decide), k3 a3 (by decide) (by decide), a32]
  obtain ⟨n5, c5, u5⟩ := t4.block dqD3 C.self dqD3_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqD3]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp4]
    refine ⟨al 0x28 (by decide) (by decide), ?_⟩
    show (memLoad32 M (S + BitVec.ofNat 32 0x28) + 0).toNat % 4 = 0
    rw [s28, add_lit_zero]; exact al _ (by omega) (by omega))
  refine ⟨n5, c1.trans (.cons d2 (c3.trans (c4.trans c5))), ⟨u5.pc, u5.mem, fun _ => rfl⟩, ?_, fun q h0 h1 h2 => ?_⟩
  · rw [u5.regs]; simp +decide only [runBlock, BInstr.run, dqD3, upd, ↓reduceIte]
    rw [sp4, a34, e40]
    show aluEval .and _ (aluEval .srl (memLoad32 M (memLoad32 M (S + BitVec.ofNat 32 0x28) + 0)) _) = _
    rw [s28, add_lit_zero]; rfl
  · rw [u5.regs, runBlock_reg _ _ _ q t4.zero (by simp only [dqD3]; revert h0 h1 h2; revert q; decide), k4 q h0,
      k3 q h0 h1, g2, r1, runBlock_reg _ _ _ q hz (by simp only [dqD1]; revert h0 h1; revert q; decide)]

def dqM1 : List BInstr :=
  [.aluImm .add a1 x0 0x30, .alu .mul a2 a0 a1, .aluImm .add a0 sp 0x2FC, .alu .add a2 a2 a0, .aluImm .add a0 sp 0x62C,
   .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x15D, .aluImm .add a4 x0 0x1, .alu .add (8 : Fin 32) x0 a3,
   .aluImm .add a3 sp 0x134]
def dqM2 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x15D, .aluImm .add a1 sp 0x62C, .aluImm .add a2 x0 0x30]

theorem dqM1_end : blockEnd p384DecompressCode 0x558 dqM1 = some 0x576 := by decide
theorem dqM2_end : blockEnd p384DecompressCode 0x57E dqM2 = some 0x58E := by decide

theorem tbl_addr {S d : Word} (F : DqFrame S) (hd : d.toNat ≤ 15) :
    aluEval .add (aluEval .mul d (aluEval .add 0 0x30)) (aluEval .add S 0x2FC) =
      S + BitVec.ofNat 32 (0x2FC + 48 * d.toNat) := by
  have := F.hi
  rw [show aluEval .add 0 0x30 = (0x30 : Word) from rfl]
  apply BitVec.eq_of_toNat_eq
  show (d * 0x30 + (S + BitVec.ofNat 32 0x2FC)).toNat = (S + BitVec.ofNat 32 (0x2FC + 48 * d.toNat)).toNat
  rw [F.at _ (by omega), BitVec.toNat_add, BitVec.toNat_mul, F.at 0x2FC (by decide),
    show (0x30 : Word).toNat = 48 from rfl]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A window's multiplication**, from the digit's test at 0x554 back to the
window loop at 0x314: unless the digit `d` in `a0` is zero, `z` at
`S + 0x95C` becomes its Montgomery product with table entry `d`. -/
theorem dq_win_mul {M : Word → BitVec 8} {S : Word} {n : Machine} {w d : Word} {A : Nat} (C : DqCode M)
    (F : DqFrame S) (s : St M DP n 0x554 (reg n)) (rsp : reg n sp = S) (ra0 : reg n a0 = d) (hd : d.toNat ≤ 15)
    (ra3 : reg n a3 = w) (hN0 : memLoad32 M (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF)
    (hN : accV M (S + BitVec.ofNat 32 0x134) 12 = p384)
    (hpw : ∀ k, k < 16 → accV M (S + BitVec.ofNat 32 (0x2FC + 48 * k)) 12 = mpow A k) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x314 (reg n') ∧ DqCode n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 =
        (if d = 0 then accV M (S + BitVec.ofNat 32 0x95C) 12 else p3fm (accV M (S + BitVec.ofNat 32 0x95C) 12) (mpow A d.toNat)) ∧
      reg n' a3 = w ∧
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 →
        Sep (S + BitVec.ofNat 32 0x95C) 48 x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  by_cases h0 : d = 0
  · obtain ⟨n1, d1, u1⟩ := s.taken C.self 0x314 dp_at_554 (by decide) (by
      show (reg n a0 == reg n x0) = true; rw [ra0, hz, h0]; rfl)
    exact ⟨n1, .single d1, ⟨u1.pc, by rw [u1.mem], fun _ => rfl⟩, by rw [u1.mem]; exact C, by rw [u1.mem, ite_eq_left h0],
      by rw [u1.regs]; exact ra3, fun x _ _ _ => by rw [u1.mem], fun q _ => by rw [u1.regs]⟩
  obtain ⟨n1, d1, u1⟩ := s.notTaken C.self 0x558 dp_at_554 (by decide) (by
    show (reg n a0 == reg n x0) = false; rw [ra0, hz]; exact beq_false_of_ne h0)
  have v1 : St M DP n1 0x558 (reg n1) := u1.self
  have g1 : ∀ q, reg n1 q = reg n q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2⟩ := v1.block dqM1 C.self dqM1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial, trivial, trivial⟩
  have r2 : ∀ q, reg n2 q = (runBlock dqM1 (M, reg n1)).2 q := fun q => by rw [u2.regs]
  have sp1 : reg n1 sp = S := by rw [g1]; exact rsp
  have hk : d.toNat < 16 := by omega
  obtain ⟨n3, c3, u3, hv3, fr3, sp3, k3⟩ := dq_mm (out := S + BitVec.ofNat 32 0x62C) (xp := S + BitVec.ofNat 32 0x95C)
    (yp := S + BitVec.ofNat 32 (0x2FC + 48 * d.toNat)) (S := S) (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St M DP n2 0x576 (reg n2))
    C F dp_at_576 dp_at_57a (by decide) (by decide)
    (by rw [r2, runBlock_reg _ _ _ sp v1.zero (by decide)]; exact sp1)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqM1, upd, ↓reduceIte]; rw [sp1]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqM1, upd, ↓reduceIte]; rw [sp1, spo]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqM1, upd, ↓reduceIte]; rw [sp1, g1, ra0, v1.zero]
        exact tbl_addr F hd)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqM1, upd, ↓reduceIte]; rw [sp1]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqM1, upd, ↓reduceIte]; (try rw [v1.zero]); try rfl)
    (co := 0x62C) (cx := 0x95C) (cy := 0x2FC + 48 * d.toNat) (by decide) (by decide) (by omega) rfl rfl rfl
    (by decide) (by decide) (by omega) hN0 hN (by rw [hpw _ hk]; exact mpow_lt A _)
  rw [hpw _ hk] at hv3
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have h3hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n3.mem x = M x := fun x hx =>
    fr3 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x62C) (n := 48) (by decide) hx)
  have C3 := C.hi h3hi
  have k3' : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n q := fun q hq => by
    have hb : q ∉ dqM1.filterMap BInstr.dst := by simp only [dqM1]; revert hq; revert q; decide
    rw [k3 q (by revert hq; revert q; decide), r2, runBlock_reg _ _ _ q v1.zero hb, g1]
  have e8 : reg n3 (8 : Fin 32) = w := by
    rw [k3 8 (by decide), r2]; simp +decide only [runBlock, BInstr.run, dqM1, upd, ↓reduceIte]; rw [g1, ra3]
    exact BitVec.zero_add _
  -- copy the product to z
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide)
  have b16 : ∀ c, c + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFFF0) 16 := fun c hc =>
    (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have w48 : ∀ c, c + 48 ≤ 0xA50 → (S + BitVec.ofNat 32 c).toNat + 48 < 2 ^ 32 := fun c hc => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n4, c4, u4⟩ := u3.block dqM2 C3.self dqM2_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock dqM2 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  obtain ⟨n5, c5, u5, fr5, k5⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x95C) (src := S + BitVec.ofNat 32 0x62C)
    (S := S) (N := 48) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem DP n4 0x58E (reg n4)) C3 dp_at_58e dp_at_592
    (by decide) (by decide) (by rw [r4, runBlock_reg _ _ _ sp u3.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqM2, upd, ↓reduceIte]; rw [sp3, spo]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqM2, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqM2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    ⟨C3.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have k5' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n5 q = reg n3 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ dqM2.filterMap BInstr.dst := by simp only [dqM2]; revert h0 h1 h2; revert q; decide
      rw [k5 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r4, runBlock_reg _ _ _ q u3.zero hb]
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have h5hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n5.mem x = M x := fun x hx => by
    rw [fr5 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x95C) (n := 48) (by decide) hx) (Nat.le_refl _), h3hi x hx]
  have C5 := C.hi h5hi
  obtain ⟨n6, d6, u6⟩ := u5.alu C5.self dp_at_596 (off' := 0x598) (by decide)
  obtain ⟨n7, d7, u7⟩ := u6.self.jump C5.self dp_at_598 (off' := 0x314) (by decide) (by rw [u6.self.pc]; decide)
  have l16 : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  refine ⟨n7, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (.single d7)))))),
    ⟨u7.pc, by rw [u7.mem], fun _ => rfl⟩, by rw [u7.mem]; exact C5, ?_, ?_, fun x hF h62 h95 => ?_,
    fun q hq => ?_⟩
  · rw [ite_eq_right h0, u7.mem, ← hv3]
    refine cp_accV (by decide) (by decide) fun i hi => ?_
    rw [load_frame fr5 (l16 _ (by omega)), ← add_ofNat_assoc S 0x95C, cp_word (by omega) (by decide), add_ofNat_assoc]
  · rw [u7.regs, u6.regs]; simp +decide only [upd, ↓reduceIte]; rw [u5.zero, k5' 8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), e8]; exact BitVec.zero_add _
  · have h16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
      have := hF.sub (c := 0xE0) (l := 16) (by decide)
      rwa [show S + 0xFFFFFF10 + BitVec.ofNat 32 0xE0 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
    rw [u7.mem, fr5 x h16, copyBytes_sep h95 (Nat.le_refl _), fr3 x hF h62]
  · have hq3 : q ≠ a3 := by revert hq; revert q; decide
    rw [u7.regs, u6.regs, updz u5.zero hq3, k5' q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) hq3 (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
    by_cases hs : q = sp
    · subst hs; rw [sp3, rsp]
    · exact k3' q (by revert hs hq; revert q; decide)

/-! ## The exponent -/

/-- The square-root exponent `(p + 1) / 4`. -/
def sqrtExp : Nat := (p384 + 1) / 4

/-- Limb `i` of `sqrtExp`. -/
def expLimb (i : Nat) : Word := BitVec.ofNat 32 (sqrtExp / 2 ^ (32 * i) % 2 ^ 32)

set_option exponentiation.threshold 600 in
set_option maxRecDepth 100000 in
theorem exp_digit : ∀ i, i < 12 → ∀ w, w < 8 →
    (dqDig i w (expLimb i)).toNat = sqrtExp / 2 ^ (4 * (8 * i + w)) % 16 := by
  unfold sqrtExp expLimb p384; decide

set_option exponentiation.threshold 600 in
theorem exp_top : sqrtExp / 2 ^ (4 * 96) = 0 := by unfold sqrtExp p384; decide

theorem div16 (x g : Nat) : x / 2 ^ (4 * g) = 16 * (x / 2 ^ (4 * (g + 1))) + x / 2 ^ (4 * g) % 16 := by
  have e : x / 2 ^ (4 * (g + 1)) = x / 2 ^ (4 * g) / 16 := by
    rw [Nat.div_div_eq_div_mul, show 4 * (g + 1) = 4 * g + 4 by omega, Nat.pow_add]
  rw [e]; exact (Nat.div_add_mod _ 16).symm

/-! ## The window loop's invariant -/

/-- What the window loop keeps in `decompress`'s frame while it works on
limb `i`: the modulus, the table of `A`'s first 16 Montgomery powers, the
exponent, and the loop's spilled counters. -/
structure DqWin (M : Word → BitVec 8) (S : Word) (A i : Nat) : Prop where
  N0 : memLoad32 M (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF
  N : accV M (S + BitVec.ofNat 32 0x134) 12 = p384
  pw : ∀ k, k < 16 → accV M (S + BitVec.ofNat 32 (0x2FC + 48 * k)) 12 = mpow A k
  ex : ∀ j, j < 12 → memLoad32 M (S + BitVec.ofNat 32 (0x5FC + 4 * j)) = expLimb j
  s2C : memLoad32 M (S + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 (i + 1)
  s34 : memLoad32 M (S + BitVec.ofNat 32 0x34) = 11
  s38 : memLoad32 M (S + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 i
  s30 : memLoad32 M (S + BitVec.ofNat 32 0x30) = 7
  s24 : memLoad32 M (S + BitVec.ofNat 32 0x24) = 3
  s28 : memLoad32 M (S + BitVec.ofNat 32 0x28) = S + BitVec.ofNat 32 (0x5FC + 4 * i)

/-- The registers that hold the squarings' pointers and constants. -/
structure DqRegs (n : Machine) (S : Word) : Prop where
  sp : reg n sp = S
  r25 : reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x98C
  r22 : reg n (22 : Fin 32) = 12
  r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x9BC
  r23 : reg n (23 : Fin 32) = 0xFFFFFFFF
  r21 : reg n (21 : Fin 32) = S + BitVec.ofNat 32 0x138
  r26 : reg n (26 : Fin 32) = S + BitVec.ofNat 32 0x990
  r18 : reg n (18 : Fin 32) = S + BitVec.ofNat 32 0x9C0

/-- A window changes only these parts of memory. -/
def WinFrame (S : Word) (M' M : Word → BitVec 8) : Prop :=
  ∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep (S + BitVec.ofNat 32 0x20) 4 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
    Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 → Sep (S + BitVec.ofNat 32 0x95C) 0xC0 x 1 → M' x = M x

theorem WinFrame.trans {S : Word} {M1 M2 M3 : Word → BitVec 8} (h1 : WinFrame S M2 M1) (h2 : WinFrame S M3 M2) :
    WinFrame S M3 M1 := fun x a b c d e => (h2 x a b c d e).trans (h1 x a b c d e)

/-- A word at frame offset `d` that a window does not change. -/
theorem WinFrame.word {S : Word} {M' M : Word → BitVec 8} (F : DqFrame S) (h : WinFrame S M' M) {d : Nat}
    (hd : (0x24 ≤ d ∧ d + 4 ≤ 0x3C) ∨ (0x40 ≤ d ∧ d + 4 ≤ 0x62C) ∨ (0x65C ≤ d ∧ d + 4 ≤ 0x95C) ∨ d + 4 ≤ 0x20) :
    memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := by
  have hSl := F.lo; have hSh := F.hi
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  refine memLoad32_congr fun q hq => ?_
  rw [add_ofNat_assoc]
  have hF : Sep (S + 0xFFFFFF10) 0xF0 (S + BitVec.ofNat 32 (d + q)) 1 :=
    sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)
  have hx : ∀ c l, c + l ≤ 0xA50 → (c + l ≤ d + q ∨ d + q + 1 ≤ c) → Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 (d + q)) 1 :=
    fun c l h1 h2 => sepS S h2 (by omega) (by omega)
  exact h _ hF (hx 0x20 4 (by decide) (by omega)) (hx 0x3C 4 (by decide) (by omega)) (hx 0x62C 48 (by decide) (by omega))
    (hx 0x95C 0xC0 (by decide) (by omega))

theorem DqWin.frame {M M' : Word → BitVec 8} {S : Word} {A i : Nat} (F : DqFrame S) (W : DqWin M S A i)
    (h : WinFrame S M' M) : DqWin M' S A i := by
  have wd := fun d hd => WinFrame.word (d := d) F h hd
  have lo : ∀ d, 0x24 ≤ d → d + 4 ≤ 0x3C → memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => wd d (.inl ⟨h1, h2⟩)
  have mid : ∀ d, 0x40 ≤ d → d + 4 ≤ 0x62C → memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => wd d (.inr (.inl ⟨h1, h2⟩))
  refine ⟨?_, ?_, fun k hk => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mid 0x134 (by decide) (by decide)]; exact W.N0
  · rw [← W.N]; exact accV_congr2 12 fun j hj => by rw [add_ofNat_assoc, mid _ (by omega) (by omega)]
  · rw [← W.pw k hk]; exact accV_congr2 12 fun j hj => by rw [add_ofNat_assoc, mid _ (by omega) (by omega)]
  · rw [mid _ (by omega) (by omega)]; exact W.ex j hj
  · rw [lo 0x2C (by decide) (by decide)]; exact W.s2C
  · rw [lo 0x34 (by decide) (by decide)]; exact W.s34
  · rw [lo 0x38 (by decide) (by decide)]; exact W.s38
  · rw [lo 0x30 (by decide) (by decide)]; exact W.s30
  · rw [lo 0x24 (by decide) (by decide)]; exact W.s24
  · rw [lo 0x28 (by decide) (by decide)]; exact W.s28

theorem win_ne0 : ∀ c : Nat, c < 8 → (BitVec.ofNat 32 (c + 1) == (0 : Word)) = false := by decide
theorem win_dec : ∀ c : Nat, c < 8 → BitVec.ofNat 32 (c + 1) + 0xFFFFFFFF = BitVec.ofNat 32 c := by decide
theorem limb_ne : ∀ i : Nat, i < 12 → branchTaken .bne (BitVec.ofNat 32 i) 11 = decide (i ≠ 11) := by decide
theorem win_eq7 : ∀ c : Nat, c < 8 → branchTaken .beq (BitVec.ofNat 32 c) 7 = decide (c = 7) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **One window**, from the window loop's head at 0x314 with `c + 1`
windows of limb `i` left to its head again with `c` left: `z` at
`S + 0x95C` goes from `A^⌊e / 16^(8i + c + 1)⌋` to `A^⌊e / 16^(8i + c)⌋`
in Montgomery form, for the square-root exponent `e`. -/
theorem dq_window {M : Word → BitVec 8} {S : Word} {n : Machine} {i c A : Nat} (C : DqCode M) (F : DqFrame S)
    (W : DqWin M S A i) (R : DqRegs n S) (s : St M DP n 0x314 (reg n)) (ra3 : reg n a3 = BitVec.ofNat 32 (c + 1))
    (hc : c < 8) (hi : i < 12)
    (hz : accV M (S + BitVec.ofNat 32 0x95C) 12 = mpow A (sqrtExp / 2 ^ (4 * (8 * i + c + 1)))) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x314 (reg n') ∧ DqCode n'.mem ∧ WinFrame S n'.mem M ∧ DqRegs n' S ∧
      reg n' a3 = BitVec.ofNat 32 c ∧
      accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = mpow A (sqrtExp / 2 ^ (4 * (8 * i + c))) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz0 := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have al : ∀ c, c + 4 ≤ 0xA50 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  -- the head: count the window, and skip the squarings for the top one
  obtain ⟨n1, d1, u1⟩ := s.notTaken C.self 0x318 dp_at_314 (by decide) (by
    show (reg n a3 == reg n x0) = false; rw [ra3, hz0]; exact win_ne0 c hc)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm C.self dp_at_318 (off' := 0x31A) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.lw C.self dp_at_31a (off' := 0x31C) (by decide)
    (by rw [u2.regs, updz u1.self.zero (by decide), u1.regs, R.sp]; exact al 0x34 (by decide) (by decide))
  obtain ⟨n4, d4, u4⟩ := u3.self.lw C.self dp_at_31c (off' := 0x31E) (by decide)
    (by rw [u3.regs, updz u2.self.zero (by decide), u2.regs, updz u1.self.zero (by decide), u1.regs, R.sp]
        exact al 0x38 (by decide) (by decide))
  have g4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → reg n4 q = reg n q := fun q h0 h1 h3 => by
    rw [u4.regs, updz u3.self.zero h1, u3.regs, updz u2.self.zero h0, u2.regs, updz u1.self.zero h3, u1.regs]
  have e43 : reg n4 a3 = BitVec.ofNat 32 c := by
    rw [u4.regs, updz u3.self.zero (by decide), u3.regs, updz u2.self.zero (by decide), u2.regs]
    simp +decide only [upd, ↓reduceIte]; rw [u1.regs, ra3]; exact win_dec c hc
  have e40 : reg n4 a0 = 11 := by
    rw [u4.regs, updz u3.self.zero (by decide), u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [u2.regs, updz u1.self.zero (by decide), u1.regs, R.sp]; exact W.s34
  have e41 : reg n4 a1 = BitVec.ofNat 32 i := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [u3.regs, updz u2.self.zero (by decide), u2.regs, updz u1.self.zero (by decide), u1.regs, R.sp]
    exact W.s38
  have t4 : St M DP n4 0x31E (reg n4) := u4.self
  obtain ⟨n5, c5, t5, e53, k5⟩ : ∃ n5, Steps n4 n5 ∧
      St M DP n5 (if i = 11 ∧ c = 7 then 0x52C else 0x328) (reg n5) ∧ reg n5 a3 = BitVec.ofNat 32 c ∧
      ∀ q, q ≠ a0 → reg n5 q = reg n4 q := by
    have hb := limb_ne i hi
    rw [← e41, ← e40] at hb
    by_cases h11 : i = 11
    · obtain ⟨n5, d5, u5⟩ := t4.notTaken C.self 0x322 dp_at_31e (by decide) (by rw [hb]; exact decide_eq_false (fun h => h h11))
      obtain ⟨n6, d6, u6⟩ := u5.self.lw C.self dp_at_322 (off' := 0x324) (by decide)
        (by rw [u5.regs, g4 sp (by decide) (by decide) (by decide), R.sp]; exact al 0x30 (by decide) (by decide))
      have e63 : reg n6 a3 = BitVec.ofNat 32 c := by rw [u6.regs, updz u5.self.zero (by decide), u5.regs, e43]
      have e60 : reg n6 a0 = 7 := by
        rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
        rw [u5.regs, g4 sp (by decide) (by decide) (by decide), R.sp]; exact W.s30
      have hb7 := win_eq7 c hc
      rw [← e63, ← e60] at hb7
      by_cases h7 : c = 7
      · obtain ⟨n7, d7, u7⟩ := u6.self.taken C.self 0x52C dp_at_324 (by decide) (by rw [hb7]; exact decide_eq_true h7)
        refine ⟨n7, .cons d5 (.cons d6 (.single d7)), by rw [ite_eq_left ⟨h11, h7⟩]; exact u7.self, by rw [u7.regs, e63],
          fun q h => by rw [u7.regs, u6.regs, updz u5.self.zero h, u5.regs]⟩
      · obtain ⟨n7, d7, u7⟩ := u6.self.notTaken C.self 0x328 dp_at_324 (by decide) (by rw [hb7]; exact decide_eq_false h7)
        refine ⟨n7, .cons d5 (.cons d6 (.single d7)), by rw [ite_eq_right (fun h => h7 h.2)]; exact u7.self,
          by rw [u7.regs, e63], fun q h => by rw [u7.regs, u6.regs, updz u5.self.zero h, u5.regs]⟩
    · obtain ⟨n5, d5, u5⟩ := t4.taken C.self 0x328 dp_at_31e (by decide) (by rw [hb]; exact decide_eq_true h11)
      exact ⟨n5, .single d5, by rw [ite_eq_right (fun h => h11 h.1)]; exact u5.self, by rw [u5.regs, e43],
        fun q _ => by rw [u5.regs]⟩
  have k5' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → reg n5 q = reg n q := fun q h0 h1 h3 => by
    rw [k5 q h0, g4 q h0 h1 h3]
  have R5 : DqRegs n5 S := ⟨by rw [k5' sp (by decide) (by decide) (by decide)]; exact R.sp,
    by rw [k5' 25 (by decide) (by decide) (by decide)]; exact R.r25, by rw [k5' 22 (by decide) (by decide) (by decide)]; exact R.r22,
    by rw [k5' 19 (by decide) (by decide) (by decide)]; exact R.r19, by rw [k5' 23 (by decide) (by decide) (by decide)]; exact R.r23,
    by rw [k5' 21 (by decide) (by decide) (by decide)]; exact R.r21, by rw [k5' 26 (by decide) (by decide) (by decide)]; exact R.r26,
    by rw [k5' 18 (by decide) (by decide) (by decide)]; exact R.r18⟩
  -- the squarings, unless this is the top window
  obtain ⟨n6, c6, t6, C6, fr6, R6, e63, hz6, k6⟩ : ∃ n6, Steps n5 n6 ∧ St n6.mem DP n6 0x52C (reg n6) ∧ DqCode n6.mem ∧
      WinFrame S n6.mem M ∧ DqRegs n6 S ∧ reg n6 a3 = BitVec.ofNat 32 c ∧
      accV n6.mem (S + BitVec.ofNat 32 0x95C) 12 = mpow A (16 * (sqrtExp / 2 ^ (4 * (8 * i + c + 1)))) ∧
      ∀ q : Fin 32, q.val ∈ [3, 4] → reg n6 q = reg n5 q := by
    by_cases ht : i = 11 ∧ c = 7
    · rw [ite_eq_left ht] at t5
      obtain ⟨h11, h7⟩ := ht
      subst h11; subst h7
      refine ⟨n5, .refl _, ⟨t5.pc, by rw [t5.mem], fun _ => rfl⟩, by rw [t5.mem]; exact C,
        fun x _ _ _ _ _ => by rw [t5.mem], R5, e53, ?_, fun q _ => rfl⟩
      rw [t5.mem, hz, show 4 * (8 * 11 + 7 + 1) = 4 * 96 from rfl, exp_top]
    · rw [ite_eq_right ht] at t5
      obtain ⟨n6, c6, u6, C6, hv6, a36, h186, fr6, k6⟩ := dq_win_sq (w := BitVec.ofNat 32 c) C F t5 R5.sp e53 R5.r25 R5.r22
        R5.r19 R5.r23 R5.r21 R5.r26 R5.r18 W.N0 W.N (by rw [hz]; exact mpow_lt A _)
      refine ⟨n6, c6, u6, C6, fun x hF h20 h3C h62 h95 => fr6 x ?_ h20 h3C h62 h95, ⟨by rw [k6 sp rfl]; exact R5.sp,
        by rw [k6 25 rfl]; exact R5.r25, by rw [k6 22 rfl]; exact R5.r22, by rw [k6 19 rfl]; exact R5.r19,
        by rw [k6 23 rfl]; exact R5.r23, by rw [k6 21 rfl]; exact R5.r21, by rw [k6 26 rfl]; exact R5.r26, h186⟩, a36,
        by rw [hv6, hz, iter_msq_mpow]; try rfl, fun q hq => k6 q (by revert hq; revert q; decide)⟩
      have := hF.sub (c := 0xA0) (l := 0x50) (by decide)
      rwa [show S + 0xFFFFFF10 + BitVec.ofNat 32 0xA0 = S + 0xFFFFFFB0 by rw [BitVec.add_assoc]; rfl] at this
  have W6 := W.frame F fr6
  -- the digit and the multiplication
  obtain ⟨n7, c7, t7, e70, k7⟩ := dq_digit (i := i) (w := c) C6 F t6 R6.sp e63 hi hc W6.s2C W6.s34 W6.s38 W6.s30 W6.s24
    W6.s28
  rw [W6.ex i hi] at e70
  have sp7 : reg n7 sp = S := by rw [k7 sp (by decide) (by decide) (by decide)]; exact R6.sp
  have a37 : reg n7 a3 = BitVec.ofNat 32 c := by rw [k7 a3 (by decide) (by decide) (by decide)]; exact e63
  obtain ⟨n8, c8, u8, C8, hv8, a38, fr8, k8⟩ := dq_win_mul (A := A) C6 F t7 sp7 e70 (dqDig_le i c _) a37
    W6.N0 W6.N W6.pw
  have k78 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 22, 23, 25, 26] → reg n8 q = reg n6 q := fun q hq => by
    rw [k8 q (by revert hq; revert q; decide), k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)]
  have hd := exp_digit i hi c hc
  refine ⟨n8, .cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans (c6.trans (c7.trans c8)))))),
    u8, C8, fr6.trans (fun x hF h20 h3C h62 h95 => fr8 x hF h62 (by
      have := h95.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this)),
    ⟨by rw [k78 sp (by decide)]; exact R6.sp, by rw [k78 25 (by decide)]; exact R6.r25,
      by rw [k78 22 (by decide)]; exact R6.r22, by rw [k78 19 (by decide)]; exact R6.r19,
      by rw [k78 23 (by decide)]; exact R6.r23, by rw [k78 21 (by decide)]; exact R6.r21,
      by rw [k78 26 (by decide)]; exact R6.r26, by rw [k78 18 (by decide)]; exact R6.r18⟩, a38, ?_,
    by rw [k78 3 (by decide), k6 3 (by decide), k5' 3 (by decide) (by decide) (by decide)],
    by rw [k78 4 (by decide), k6 4 (by decide), k5' 4 (by decide) (by decide) (by decide)]⟩
  rw [hv8, hz6, show 8 * i + c + 1 = (8 * i + c) + 1 from rfl, div16 sqrtExp (8 * i + c)]
  by_cases h0 : dqDig i c (expLimb i) = 0
  · rw [ite_eq_left h0, ← hd, h0]; rfl
  · rw [ite_eq_right h0, mpow_add, ← hd]

set_option maxRecDepth 100000 in
/-- **The windows of limb `i`**, from the window loop's head with `c`
windows left to its head with none left. -/
theorem dq_windows {S : Word} {i A : Nat} (F : DqFrame S) (hi : i < 12) :
    ∀ c, c ≤ 8 → ∀ {M : Word → BitVec 8} {n : Machine}, DqCode M → DqWin M S A i → DqRegs n S →
      St M DP n 0x314 (reg n) → reg n a3 = BitVec.ofNat 32 c →
      accV M (S + BitVec.ofNat 32 0x95C) 12 = mpow A (sqrtExp / 2 ^ (4 * (8 * i + c))) →
      ∃ n', Steps n n' ∧ St n'.mem DP n' 0x314 (reg n') ∧ DqCode n'.mem ∧ WinFrame S n'.mem M ∧ DqRegs n' S ∧
        reg n' a3 = 0 ∧ accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = mpow A (sqrtExp / 2 ^ (4 * (8 * i))) ∧
        reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  intro c
  induction c with
  | zero =>
    intro _ M n C _ R s ra3 hz
    exact ⟨n, .refl _, by rw [s.mem]; exact s, by rw [s.mem]; exact C, fun x _ _ _ _ _ => by rw [s.mem], R, ra3,
      by rw [s.mem, hz]; rfl, rfl, rfl⟩
  | succ c ih =>
    intro hc M n C W R s ra3 hz
    obtain ⟨n1, c1, u1, C1, fr1, R1, a31, hz1, g31, g41⟩ := dq_window C F W R s ra3 (by omega) hi
      (by rw [hz]; rfl)
    obtain ⟨n2, c2, u2, C2, fr2, R2, a32, hz2, g32, g42⟩ := ih (by omega) C1 (W.frame F fr1) R1 u1 a31 hz1
    exact ⟨n2, c1.trans c2, u2, C2, fr1.trans fr2, R2, a32, hz2, by rw [g32, g31], by rw [g42, g41]⟩

/-! ## The limb loop -/

/-- What the whole exponentiation keeps in `decompress`'s frame. -/
structure DqBase (M : Word → BitVec 8) (S : Word) (A : Nat) : Prop where
  N0 : memLoad32 M (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF
  N : accV M (S + BitVec.ofNat 32 0x134) 12 = p384
  pw : ∀ k, k < 16 → accV M (S + BitVec.ofNat 32 (0x2FC + 48 * k)) 12 = mpow A k
  ex : ∀ j, j < 12 → memLoad32 M (S + BitVec.ofNat 32 (0x5FC + 4 * j)) = expLimb j
  s1C : memLoad32 M (S + BitVec.ofNat 32 0x1C) = 8
  s34 : memLoad32 M (S + BitVec.ofNat 32 0x34) = 11
  s30 : memLoad32 M (S + BitVec.ofNat 32 0x30) = 7
  s24 : memLoad32 M (S + BitVec.ofNat 32 0x24) = 3

theorem DqBase.frame {M M' : Word → BitVec 8} {S : Word} {A : Nat} (F : DqFrame S) (B : DqBase M S A)
    (h : WinFrame S M' M) : DqBase M' S A := by
  have wd := fun d hd => WinFrame.word (d := d) F h hd
  have lo : ∀ d, 0x24 ≤ d → d + 4 ≤ 0x3C → memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => wd d (.inl ⟨h1, h2⟩)
  have mid : ∀ d, 0x40 ≤ d → d + 4 ≤ 0x62C → memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => wd d (.inr (.inl ⟨h1, h2⟩))
  refine ⟨?_, ?_, fun k hk => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [mid 0x134 (by decide) (by decide)]; exact B.N0
  · rw [← B.N]; exact accV_congr2 12 fun j hj => by rw [add_ofNat_assoc, mid _ (by omega) (by omega)]
  · rw [← B.pw k hk]; exact accV_congr2 12 fun j hj => by rw [add_ofNat_assoc, mid _ (by omega) (by omega)]
  · rw [mid _ (by omega) (by omega)]; exact B.ex j hj
  · rw [wd 0x1C (.inr (.inr (.inr (by decide))))]; exact B.s1C
  · rw [lo 0x34 (by decide) (by decide)]; exact B.s34
  · rw [lo 0x30 (by decide) (by decide)]; exact B.s30
  · rw [lo 0x24 (by decide) (by decide)]; exact B.s24

/-- The parts of memory the exponentiation's loops change. -/
def LoopFrame (S : Word) (M' M : Word → BitVec 8) : Prop :=
  ∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep (S + BitVec.ofNat 32 0x20) 0x20 x 1 →
    Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 → Sep (S + BitVec.ofNat 32 0x95C) 0xC0 x 1 → M' x = M x

theorem LoopFrame.trans {S : Word} {M1 M2 M3 : Word → BitVec 8} (h1 : LoopFrame S M2 M1) (h2 : LoopFrame S M3 M2) :
    LoopFrame S M3 M1 := fun x a b c d => (h2 x a b c d).trans (h1 x a b c d)

theorem WinFrame.loop {S : Word} {M' M : Word → BitVec 8} (h : WinFrame S M' M) : LoopFrame S M' M := fun x a b c d =>
  h x a (by have := b.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
    (by have := b.sub (c := 0x1C) (l := 4) (by decide); rwa [add_ofNat_assoc] at this) c d

def dqH1 : List BInstr :=
  [.sw sp (9 : Fin 32) 0x2C, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, .lw a3 sp 0x1C, .lw a0 sp 0x34,
   .sw sp (9 : Fin 32) 0x38]
def dqH2 : List BInstr := [.lw a0 sp 0x38, .aluImm .sll a0 a0 0x2, .aluImm .add a1 sp 0x5FC, .alu .add a0 a0 a1, .sw sp a0 0x28]

theorem dqH1_end : blockEnd p384DecompressCode 0x2F8 dqH1 = some 0x302 := by decide
theorem dqH2_end : blockEnd p384DecompressCode 0x308 dqH2 = some 0x314 := by decide

theorem lsucc_dec : ∀ i : Nat, i < 12 → BitVec.ofNat 32 (i + 1) + 0xFFFFFFFF = BitVec.ofNat 32 i := by decide
theorem limb_addr {S : Word} (F : DqFrame S) {i : Nat} (hi : i < 12) :
    aluEval .add (aluEval .sll (BitVec.ofNat 32 i) 2) (aluEval .add S 0x5FC) = S + BitVec.ofNat 32 (0x5FC + 4 * i) := by
  have := F.hi
  rw [sll12 i hi]
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 (4 * i) + (S + BitVec.ofNat 32 0x5FC)).toNat = (S + BitVec.ofNat 32 (0x5FC + 4 * i)).toNat
  rw [F.at _ (by omega), BitVec.toNat_add, F.at 0x5FC (by decide), BitVec.toNat_ofNat]
  omega

theorem slot_word {M : Word → BitVec 8} {S v : Word} {c d : Nat} (hc : c + 4 ≤ 0xA50) (hd : d + 4 ≤ 0xA50)
    (h : c + 4 ≤ d ∨ d + 4 ≤ c) :
    memLoad32 (memStore32 M (S + BitVec.ofNat 32 c) v) (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
  memLoad32_store32_sep (sepS S h (by omega) (by omega))

/-- A store to one of the limb loop's counters keeps `DqBase`. -/
theorem DqBase.store {M : Word → BitVec 8} {S v : Word} {A c : Nat} (B : DqBase M S A) (h1 : 0x28 ≤ c)
    (h2 : c + 4 ≤ 0x3C) (h3 : c + 4 ≤ 0x30 ∨ 0x38 ≤ c) : DqBase (memStore32 M (S + BitVec.ofNat 32 c) v) S A := by
  refine ⟨?_, ?_, fun k hk => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [slot_word (by omega) (by decide) (.inl (by omega))]; exact B.N0
  · rw [← B.N]; exact accV_congr2 12 fun j hj => by rw [add_ofNat_assoc, slot_word (by omega) (by omega) (.inl (by omega))]
  · rw [← B.pw k hk]; exact accV_congr2 12 fun j hj => by
      rw [add_ofNat_assoc, slot_word (by omega) (by omega) (.inl (by omega))]
  · rw [slot_word (by omega) (by omega) (.inl (by omega))]; exact B.ex j hj
  · rw [slot_word (by omega) (by decide) (.inr (by omega))]; exact B.s1C
  · rw [slot_word (by omega) (by decide) (by rcases h3 with h | h; exact .inl (by omega); exact .inr (by omega))]; exact B.s34
  · rw [slot_word (by omega) (by decide) (by rcases h3 with h | h; exact .inl (by omega); exact .inr (by omega))]; exact B.s30
  · rw [slot_word (by omega) (by decide) (.inr (by omega))]; exact B.s24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The start of limb `i`**, from 0x2F8 with `s1 = i + 1` to the window
loop's head with eight windows to go: spill the counters for limb `i`. -/
theorem dq_lhead {M : Word → BitVec 8} {S : Word} {n : Machine} {i A : Nat} (C : DqCode M) (F : DqFrame S)
    (B : DqBase M S A) (s : St M DP n 0x2F8 (reg n)) (rsp : reg n sp = S)
    (r9 : reg n (9 : Fin 32) = BitVec.ofNat 32 (i + 1)) (hi : i < 12) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x314 (reg n') ∧ DqCode n'.mem ∧ DqBase n'.mem S A ∧ DqWin n'.mem S A i ∧
      reg n' a3 = 8 ∧ LoopFrame S n'.mem M ∧
      accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = accV M (S + BitVec.ofNat 32 0x95C) 12 ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have al : ∀ c, c + 4 ≤ 0xA50 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block dqH1 C.self dqH1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqH1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp]
    exact ⟨⟨al 0x2C (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩, al 0x1C (by decide) (by decide),
      al 0x34 (by decide) (by decide), al 0x38 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 M (S + BitVec.ofNat 32 0x2C) (BitVec.ofNat 32 (i + 1)))
      (S + BitVec.ofNat 32 0x38) (BitVec.ofNat 32 i) = M1 := ⟨_, rfl⟩
  have m1 : n1.mem = M1 := by
    rw [u1.mem, ← hM1]; simp +decide only [runBlock, BInstr.run, dqH1, upd, ↓reduceIte]; rw [rsp, r9,
      show aluEval .add (BitVec.ofNat 32 (i + 1)) 0xFFFFFFFF = BitVec.ofNat 32 i from lsucc_dec i hi]; rfl
  have r1 : ∀ q, reg n1 q = (runBlock dqH1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have B1 : DqBase M1 S A := by
    rw [← hM1]; exact (B.store (c := 0x2C) (by decide) (by decide) (.inl (by decide))).store (by decide) (by decide)
      (.inr (by decide))
  have e19 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 i := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, dqH1, upd, ↓reduceIte]; rw [r9]; exact lsucc_dec i hi
  have e1a3 : reg n1 a3 = 8 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, dqH1, upd, ↓reduceIte]; rw [rsp]
    show memLoad32 (memStore32 M (S + BitVec.ofNat 32 0x2C) _) (S + BitVec.ofNat 32 0x1C) = 8
    rw [slot_word (by decide) (by decide) (.inr (by decide))]; exact B.s1C
  have e1a0 : reg n1 a0 = 11 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, dqH1, upd, ↓reduceIte]; rw [rsp]
    show memLoad32 (memStore32 M (S + BitVec.ofNat 32 0x2C) _) (S + BitVec.ofNat 32 0x34) = 11
    rw [slot_word (by decide) (by decide) (.inl (by decide))]; exact B.s34
  have k1 : ∀ q, q ≠ a0 → q ≠ a3 → q ≠ (9 : Fin 32) → reg n1 q = reg n q := fun q h0 h3 h9 => by
    rw [r1, runBlock_reg _ _ _ q hz (by simp only [dqH1]; revert h0 h3 h9; revert q; decide)]
  have t1 : St M1 DP n1 0x302 (reg n1) := ⟨u1.pc, m1, fun _ => rfl⟩
  have C1 : DqCode M1 := C.hi fun x hx => by
    rw [← hM1, memStore32_get_sep (F.hiOut (c := 0x38) (n := 4) (by decide) hx),
      memStore32_get_sep (F.hiOut (c := 0x2C) (n := 4) (by decide) hx)]
  -- eight windows either way
  obtain ⟨n2, c2, t2, e2a3, k2⟩ : ∃ n2, Steps n1 n2 ∧ St M1 DP n2 0x308 (reg n2) ∧ reg n2 a3 = 8 ∧
      ∀ q, q ≠ a3 → reg n2 q = reg n1 q := by
    by_cases h11 : i = 11
    · obtain ⟨n2, d2, u2⟩ := t1.taken C1.self 0x308 dp_at_302 (by decide) (by
        show (reg n1 (9 : Fin 32) == reg n1 a0) = true; rw [e19, e1a0, h11]; rfl)
      exact ⟨n2, .single d2, u2.self, by rw [u2.regs, e1a3], fun q _ => by rw [u2.regs]⟩
    · obtain ⟨n2, d2, u2⟩ := t1.notTaken C1.self 0x306 dp_at_302 (by decide) (by
        show (reg n1 (9 : Fin 32) == reg n1 a0) = false; rw [e19, e1a0]
        have : ∀ i : Nat, i < 12 → i ≠ 11 → (BitVec.ofNat 32 i == (11 : Word)) = false := by decide
        exact this i hi h11)
      obtain ⟨n3, d3, u3⟩ := u2.self.aluImm C1.self dp_at_306 (off' := 0x308) (by decide)
      exact ⟨n3, .cons d2 (.single d3), ⟨u3.pc, by rw [u3.mem], fun _ => rfl⟩,
        by rw [u3.regs]; simp +decide only [upd, ↓reduceIte]; rw [u2.self.zero]; rfl,
        fun q h => by rw [u3.regs, updz u2.self.zero h, u2.regs]⟩
  have sp2 : reg n2 sp = S := by rw [k2 sp (by decide), k1 sp (by decide) (by decide) (by decide)]; exact rsp
  obtain ⟨n3, c3, u3⟩ := t2.block dqH2 C1.self dqH2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqH2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp2]
    exact ⟨al 0x38 (by decide) (by decide), al 0x28 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  have s38 : memLoad32 M1 (S + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 i := by rw [← hM1, memLoad32_store32_same]
  have m3 : n3.mem = memStore32 M1 (S + BitVec.ofNat 32 0x28) (S + BitVec.ofNat 32 (0x5FC + 4 * i)) := by
    rw [u3.mem]; simp +decide only [runBlock, BInstr.run, dqH2, upd, ↓reduceIte]; rw [sp2]
    show memStore32 M1 (S + BitVec.ofNat 32 0x28) (aluEval .add (aluEval .sll (memLoad32 M1 (S + BitVec.ofNat 32 0x38)) 2)
      (aluEval .add S 0x5FC)) = _
    rw [s38, limb_addr F hi]
  refine ⟨n3, c1.trans (c2.trans c3), ⟨u3.pc, rfl, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun q h0 h1 h3 h9 => ?_⟩
  · exact C.hi fun x hx => by
      rw [m3, memStore32_get_sep (F.hiOut (c := 0x28) (n := 4) (by decide) hx), ← hM1,
        memStore32_get_sep (F.hiOut (c := 0x38) (n := 4) (by decide) hx),
        memStore32_get_sep (F.hiOut (c := 0x2C) (n := 4) (by decide) hx)]
  · rw [m3]; exact B1.store (by decide) (by decide) (.inl (by decide))
  · have B3 : DqBase n3.mem S A := by rw [m3]; exact B1.store (by decide) (by decide) (.inl (by decide))
    refine ⟨B3.N0, B3.N, B3.pw, B3.ex, ?_, B3.s34, ?_, B3.s30, B3.s24, ?_⟩
    · rw [m3, slot_word (by decide) (by decide) (.inl (by decide)), ← hM1, slot_word (by decide) (by decide) (.inr (by decide)),
        memLoad32_store32_same]
    · rw [m3, slot_word (by decide) (by decide) (.inl (by decide)), s38]
    · rw [m3, memLoad32_store32_same]
  · rw [u3.regs]; simp +decide only [runBlock, BInstr.run, dqH2, upd, ↓reduceIte]; exact e2a3
  · intro x hF h20 h62 h95
    have h28 : Sep (S + BitVec.ofNat 32 0x28) 4 x 1 := by
      have := h20.sub (c := 8) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
    have h2C : Sep (S + BitVec.ofNat 32 0x2C) 4 x 1 := by
      have := h20.sub (c := 0xC) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
    have h38 : Sep (S + BitVec.ofNat 32 0x38) 4 x 1 := by
      have := h20.sub (c := 0x18) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
    rw [m3, memStore32_get_sep h28, ← hM1, memStore32_get_sep h38, memStore32_get_sep h2C]
  · exact accV_congr2 12 fun j hj => by
      rw [add_ofNat_assoc, m3, slot_word (by decide) (by omega) (.inl (by omega)), ← hM1,
        slot_word (by decide) (by omega) (.inl (by omega)), slot_word (by decide) (by omega) (.inl (by omega))]
  · rw [u3.regs, runBlock_reg _ _ _ q t2.zero (by simp only [dqH2]; revert h0 h1; revert q; decide), k2 q h3,
      k1 q h0 h3 h9]

theorem lim_ne0 : ∀ i : Nat, i < 12 → branchTaken .bne (BitVec.ofNat 32 i) 0 = decide (i ≠ 0) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The limb loop**, from the start of limb `i` at 0x2F8 to the loop's
exit at 0x5A0: `z` at `S + 0x95C` goes from `A^⌊e / 16^(8i + 8)⌋` to
`A^e` in Montgomery form, for the square-root exponent `e`. -/
theorem dq_limbs {S : Word} {A : Nat} (F : DqFrame S) :
    ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine}, DqCode M → DqBase M S A → DqRegs n S →
      St M DP n 0x2F8 (reg n) → reg n (9 : Fin 32) = BitVec.ofNat 32 (i + 1) →
      accV M (S + BitVec.ofNat 32 0x95C) 12 = mpow A (sqrtExp / 2 ^ (4 * (8 * i + 8))) →
      ∃ n', Steps n n' ∧ St n'.mem DP n' 0x5A0 (reg n') ∧ DqCode n'.mem ∧ DqBase n'.mem S A ∧ LoopFrame S n'.mem M ∧
        DqRegs n' S ∧ accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = mpow A sqrtExp ∧
        reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  intro i
  induction i with
  | zero => exact fun hi => step 0 hi (fun k h => absurd h.symm (Nat.succ_ne_zero k))
  | succ k ih => exact fun hi => step (k + 1) hi (fun k' h => by
      obtain rfl : k = k' := Nat.succ.inj h
      exact ih (by omega))
where
  step (i : Nat) (hi : i < 12)
      (ih : ∀ k, i = k + 1 → ∀ {M : Word → BitVec 8} {n : Machine}, DqCode M → DqBase M S A → DqRegs n S →
        St M DP n 0x2F8 (reg n) → reg n (9 : Fin 32) = BitVec.ofNat 32 (k + 1) →
        accV M (S + BitVec.ofNat 32 0x95C) 12 = mpow A (sqrtExp / 2 ^ (4 * (8 * k + 8))) →
        ∃ n', Steps n n' ∧ St n'.mem DP n' 0x5A0 (reg n') ∧ DqCode n'.mem ∧ DqBase n'.mem S A ∧ LoopFrame S n'.mem M ∧
          DqRegs n' S ∧ accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = mpow A sqrtExp ∧
          reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32))
      {M : Word → BitVec 8} {n : Machine} (C : DqCode M) (B : DqBase M S A) (R : DqRegs n S)
      (s : St M DP n 0x2F8 (reg n)) (r9 : reg n (9 : Fin 32) = BitVec.ofNat 32 (i + 1))
      (hz : accV M (S + BitVec.ofNat 32 0x95C) 12 = mpow A (sqrtExp / 2 ^ (4 * (8 * i + 8)))) :
      ∃ n', Steps n n' ∧ St n'.mem DP n' 0x5A0 (reg n') ∧ DqCode n'.mem ∧ DqBase n'.mem S A ∧ LoopFrame S n'.mem M ∧
        DqRegs n' S ∧ accV n'.mem (S + BitVec.ofNat 32 0x95C) 12 = mpow A sqrtExp ∧
        reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
    have hSl := F.lo; have hSh := F.hi; have hSa := F.al
    obtain ⟨n1, c1, u1, C1, B1, W1, a31, fr1, hz1, k1⟩ := dq_lhead C F B s R.sp r9 hi
    have kk1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 22, 23, 25, 26] → reg n1 q = reg n q := fun q hq =>
      k1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide)
    have R1 : DqRegs n1 S := ⟨by rw [kk1 sp (by decide)]; exact R.sp, by rw [kk1 25 (by decide)]; exact R.r25,
      by rw [kk1 22 (by decide)]; exact R.r22, by rw [kk1 19 (by decide)]; exact R.r19, by rw [kk1 23 (by decide)]; exact R.r23,
      by rw [kk1 21 (by decide)]; exact R.r21, by rw [kk1 26 (by decide)]; exact R.r26, by rw [kk1 18 (by decide)]; exact R.r18⟩
    obtain ⟨n2, c2, u2, C2, fr2, R2, a32, hz2, g32, g42⟩ := dq_windows F hi 8 (Nat.le_refl 8) C1 W1 R1 u1 a31
      (by rw [hz1, hz])
    have W2 := W1.frame F fr2
    have B2 := B1.frame F fr2
    -- the end of the limb
    obtain ⟨n3, d3, u3⟩ := u2.taken C2.self 0x59A dp_at_314 (by decide) (by
      show (reg n2 a3 == reg n2 x0) = true; rw [a32, u2.zero]; rfl)
    obtain ⟨n4, d4, u4⟩ := u3.self.lw C2.self dp_at_59a (off' := 0x59C) (by decide)
      (by rw [u3.regs, R2.sp]; show (S + BitVec.ofNat 32 0x38).toNat % 4 = 0; rw [F.at _ (by decide)]; omega)
    have e49 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 i := by
      rw [u4.regs]; simp +decide only [upd, ↓reduceIte]; rw [u3.regs, R2.sp]; exact W2.s38
    have g4 : ∀ q, q ≠ (9 : Fin 32) → reg n4 q = reg n2 q := fun q h => by rw [u4.regs, updz u3.self.zero h, u3.regs]
    have R4 : DqRegs n4 S := ⟨by rw [g4 sp (by decide)]; exact R2.sp, by rw [g4 25 (by decide)]; exact R2.r25,
      by rw [g4 22 (by decide)]; exact R2.r22, by rw [g4 19 (by decide)]; exact R2.r19, by rw [g4 23 (by decide)]; exact R2.r23,
      by rw [g4 21 (by decide)]; exact R2.r21, by rw [g4 26 (by decide)]; exact R2.r26, by rw [g4 18 (by decide)]; exact R2.r18⟩
    have m4 : n4.mem = n2.mem := u4.mem
    have fr12 : LoopFrame S n2.mem M := fr1.trans fr2.loop
    have hb := lim_ne0 i hi
    rw [← e49, ← u4.self.zero] at hb
    by_cases h0 : i = 0
    · obtain ⟨n5, d5, u5⟩ := u4.self.notTaken C2.self 0x5A0 dp_at_59c (by decide) (by rw [hb]; exact decide_eq_false (fun h => h h0))
      subst h0
      refine ⟨n5, c1.trans (c2.trans (.cons d3 (.cons d4 (.single d5)))), ⟨u5.pc, by rw [u5.mem], fun _ => rfl⟩,
        by rw [u5.mem]; exact C2, by rw [u5.mem]; exact B2, by rw [u5.mem]; exact fr12,
        ⟨by rw [u5.regs]; exact R4.sp, by rw [u5.regs]; exact R4.r25, by rw [u5.regs]; exact R4.r22,
          by rw [u5.regs]; exact R4.r19, by rw [u5.regs]; exact R4.r23, by rw [u5.regs]; exact R4.r21,
          by rw [u5.regs]; exact R4.r26, by rw [u5.regs]; exact R4.r18⟩, by rw [u5.mem, hz2]; rfl, ?_, ?_⟩
      · rw [u5.regs, g4 3 (by decide), g32, kk1 3 (by decide)]
      · rw [u5.regs, g4 4 (by decide), g42, kk1 4 (by decide)]
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      obtain ⟨n5, d5, u5⟩ := u4.self.taken C2.self 0x2F8 dp_at_59c (by decide) (by rw [hb]; exact decide_eq_true h0)
      have R5 : DqRegs n5 S := ⟨by rw [u5.regs]; exact R4.sp, by rw [u5.regs]; exact R4.r25, by rw [u5.regs]; exact R4.r22,
        by rw [u5.regs]; exact R4.r19, by rw [u5.regs]; exact R4.r23, by rw [u5.regs]; exact R4.r21,
        by rw [u5.regs]; exact R4.r26, by rw [u5.regs]; exact R4.r18⟩
      obtain ⟨n6, c6, u6, C6, B6, fr6, R6, hz6, g36, g46⟩ := ih k rfl C2 B2 R5
        ⟨u5.pc, by rw [u5.mem], fun _ => rfl⟩ (by rw [u5.regs, e49])
        (by rw [hz2, show 8 * (k + 1) = 8 * k + 8 by omega])
      refine ⟨n6, c1.trans (c2.trans (.cons d3 (.cons d4 (.cons d5 c6)))), u6, C6, B6, fr12.trans fr6, R6, hz6, ?_, ?_⟩
      · rw [g36, u5.regs, g4 3 (by decide), g32, kk1 3 (by decide)]
      · rw [g46, u5.regs, g4 4 (by decide), g42, kk1 4 (by decide)]

end C3.RV32.Dq
