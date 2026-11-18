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
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧
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
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, p3_mont hlt hcg, fr2,
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

end C3.RV32.Dq
