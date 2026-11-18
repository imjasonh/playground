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

end C3.RV32.Dq
