import C3BootProofs.Proofs.Dec256Sq2

/-!
# P-256 point decompression: the windowed exponentiation

`decompress` computes `(x³ + ax + b)^((p + 1) / 4)` in Montgomery form with
crypto-bigint's fixed-window exponentiation: a table of the first 16 powers,
then, for each 4-bit window of the exponent from the top, four squarings
and a multiplication by the table entry the window selects. This is the
8-limb counterpart of `Dec384Pow.lean`.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2

set_option maxRecDepth 20000

/-- A Montgomery squaring. -/
def msq2 (w : Nat) : Nat := p2fm w w

theorem iter_msq2_lt (k : Nat) : ∀ w, w < p256 → iter msq2 k w < p256 := by
  induction k with
  | zero => intro w h; exact h
  | succ k ih => intro w _; rw [iter]; exact ih _ (p2fm_lt w w)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The four squarings**, from the loop's head at 0x31C with `j` passes
done to its exit at 0x4BA: the working value at `S + 0x67C` is squared
`4 - j` more times in Montgomery form. -/
theorem gd_sqr4 {S : Word} (F : Fr S 0x710) :
    ∀ k j, j + k = 4 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → St M GD n 0x31C (reg n) →
      reg n sp = S → reg n a1 = BitVec.ofNat 32 j →
      reg n (27 : Fin 32) = 8 →
      reg n (18 : Fin 32) = S + BitVec.ofNat 32 0x69C → reg n (22 : Fin 32) = 0xFFFFFFFF →
      reg n (21 : Fin 32) = S + BitVec.ofNat 32 0xE8 → reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x680 →
      reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x6A0 →
      memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF → accV M (S + BitVec.ofNat 32 0xE4) 8 = p256 →
      accV M (S + BitVec.ofNat 32 0x67C) 8 < p256 →
      ∃ n', Steps n n' ∧ St n'.mem GD n' 0x4BA (reg n') ∧ GdCode n'.mem ∧
        accV n'.mem (S + BitVec.ofNat 32 0x67C) 8 = iter msq2 k (accV M (S + BitVec.ofNat 32 0x67C) 8) ∧
        reg n' (19 : Fin 32) = S + BitVec.ofNat 32 0x6A0 ∧
        (∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
          Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → Sep (S + BitVec.ofNat 32 0x67C) 0x60 x 1 → n'.mem x = M x) ∧
        ∀ q, gdSqKeep q = true → reg n' q = reg n q := by
  intro k
  induction k with
  | zero =>
    intro j hj M n C s rsp ra1 r27 r18 r22 r21 r25 r19 hN0 hN hW
    have j4 : j = 4 := by omega
    subst j4
    obtain ⟨n1, d1, u1⟩ := s.aluImm C.self gd_at_31c (off' := 0x31E) (by decide)
    have e1 : reg n1 a1 = 4 := by rw [u1.regs, updz s.zero (by decide), ra1]; rfl
    have e0 : reg n1 a0 = 4 := by rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [s.zero]; rfl
    obtain ⟨n2, d2, u2⟩ := u1.self.taken C.self 0x4BA gd_at_31e (by decide) (by
      show (reg n1 a1 == reg n1 a0) = true; rw [e1, e0]; rfl)
    refine ⟨n2, .cons d1 (.single d2), ⟨u2.pc, by rw [u2.mem], fun _ => rfl⟩, by rw [u2.mem]; exact C,
      by rw [u2.mem]; rfl, by rw [u2.regs, u1.regs, updz s.zero (by decide)]; exact r19,
      fun x _ _ _ _ => by rw [u2.mem], fun q hq => ?_⟩
    rw [u2.regs, u1.regs, updz s.zero (pkeep_ne (r := a0) hq rfl)]
  | succ k ih =>
    intro j hj M n C s rsp ra1 r27 r18 r22 r21 r25 r19 hN0 hN hW
    obtain ⟨n1, d1, u1⟩ := s.aluImm C.self gd_at_31c (off' := 0x31E) (by decide)
    have e1 : reg n1 a1 = BitVec.ofNat 32 j := by rw [u1.regs, updz s.zero (by decide), ra1]
    have e0 : reg n1 a0 = 4 := by rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [s.zero]; rfl
    have hj4 : j < 4 := by omega
    obtain ⟨n2, d2, u2⟩ := u1.self.notTaken C.self 0x322 gd_at_31e (by decide) (by
      show (reg n1 a1 == reg n1 a0) = false
      rw [e1, e0]
      have : ∀ j : Nat, j < 4 → (BitVec.ofNat 32 j == (4 : Word)) = false := by decide
      exact this j hj4)
    have g2 : ∀ q, q ≠ a0 → reg n2 q = reg n q := fun q h => by rw [u2.regs, u1.regs, updz s.zero h]
    have s2 : St M GD n2 0x322 (reg n2) := ⟨u2.pc, by rw [u2.mem], fun _ => rfl⟩
    obtain ⟨n3, c3, u3, C3, hlt, hsq, ha13, fr3, k3⟩ := gd_sq (j := j) C F s2 (by rw [g2 sp (by decide)]; exact rsp)
      (by rw [g2 a1 (by decide)]; exact ra1) (by rw [g2 27 (by decide)]; exact r27)
      (by rw [g2 18 (by decide)]; exact r18) (by rw [g2 22 (by decide)]; exact r22) (by rw [g2 21 (by decide)]; exact r21)
      (by rw [g2 25 (by decide)]; exact r25) (by rw [g2 19 (by decide)]; exact r19) hN0 (by rw [hN]; exact hW)
    rw [hN] at hlt hsq
    have hv := p2_mont hlt hsq
    have hb16 : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
    have hSl := F.lo; have hSh := F.hi
    have sq : ∀ c l d, c + l ≤ 0x710 → d + 1 ≤ 0x710 → (c + l ≤ d ∨ d + 1 ≤ c) →
        Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
    have s50 : ∀ d, d + 1 ≤ 0x710 → Sep (S + 0xFFFFFFC0) 0x40 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
      sep_of_le (by rw [hb16, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)
    have nfr : ∀ i, i < 8 → memLoad32 n3.mem (S + BitVec.ofNat 32 0xE4 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M (S + BitVec.ofNat 32 0xE4 + BitVec.ofNat 32 (4 * i)) := fun i hi => by
      rw [add_ofNat_assoc]
      refine memLoad32_congr fun q hq => ?_
      rw [add_ofNat_assoc]
      exact fr3 _ (s50 _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
        (sq _ _ _ (by decide) (by omega) (.inr (by omega))) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
    have hN3 : accV n3.mem (S + BitVec.ofNat 32 0xE4) 8 = p256 := by rw [← hN]; exact accV_congr2 8 nfr
    have hN03 : memLoad32 n3.mem (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF := by
      have := nfr 0 (by decide); rw [Nat.mul_zero, add_ofNat_zero] at this; rw [this, hN0]
    obtain ⟨n4, c4, u4, C4, hv4, h184, fr4, k4⟩ := ih (j + 1) (by omega) C3 u3
      (by rw [k3 sp rfl, g2 sp (by decide)]; exact rsp) (by rw [ha13, ofNat_succ])
      (by rw [k3 27 rfl, g2 27 (by decide)]; exact r27)
      (by rw [k3 18 rfl, g2 18 (by decide)]; exact r18) (by rw [k3 22 rfl, g2 22 (by decide)]; exact r22)
      (by rw [k3 21 rfl, g2 21 (by decide)]; exact r21) (by rw [k3 25 rfl, g2 25 (by decide)]; exact r25) (by rw [k3 19 rfl, g2 19 (by decide)]; exact r19) hN03 hN3
      (by rw [hv]; exact p2fm_lt _ _)
    refine ⟨n4, .cons d1 (.cons d2 (c3.trans c4)), u4, C4, by rw [hv4, hv, iter]; rfl, h184,
      fun x h50 h3C h62 h98 => by rw [fr4 x h50 h3C h62 h98, fr3 x h50 h3C h62 h98],
      fun q hq => by rw [k4 q hq, k3 q hq, g2 q (pkeep_ne (r := a0) hq rfl)]⟩
/-! ## Montgomery powers -/

/-- The Montgomery form of 1. -/
def p2one : Nat := 2 ^ 256 % p256

/-- A Montgomery multiplication by `A`. -/
def mmul2 (A z : Nat) : Nat := p2fm z A

/-- `A` to the `n` in Montgomery form, as repeated multiplication from 1. -/
def mpow2 (A n : Nat) : Nat := iter (mmul2 A) n p2one

set_option exponentiation.threshold 600 in
theorem p2one_lt : p2one < p256 := by unfold p2one p256; decide

set_option exponentiation.threshold 600 in
theorem p2one_inv : p2one * p2RInv % p256 = 1 := by unfold p2one p256 p2RInv; decide

theorem iter_mmul2 (A n : Nat) : ∀ z, z < p256 → iter (mmul2 A) n z = z * (A * p2RInv) ^ n % p256 := by
  induction n with
  | zero => intro z h; rw [iter, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt h]
  | succ n ih =>
    intro z _
    rw [iter, ih _ (show mmul2 A z < p256 from p2fm_lt z A)]
    unfold mmul2 p2fm
    rw [Nat.mod_mul_mod, Nat.pow_succ]
    congr 1
    ac_rfl

theorem mpow2_val (A n : Nat) : mpow2 A n = p2one * (A * p2RInv) ^ n % p256 := iter_mmul2 A n _ p2one_lt

theorem mpow2_lt (A n : Nat) : mpow2 A n < p256 := by rw [mpow2_val]; exact Nat.mod_lt _ p256_pos

theorem mod3 (X Y R p : Nat) : X % p * (Y % p) * R % p = X * Y * R % p := by
  rw [Nat.mul_mod, Nat.mul_mod (X * Y), Nat.mul_mod X Y]

theorem mpow2_add (A a b : Nat) : p2fm (mpow2 A a) (mpow2 A b) = mpow2 A (a + b) := by
  rw [mpow2_val, mpow2_val, mpow2_val]
  unfold p2fm
  rw [mod3, show p2one * (A * p2RInv) ^ a * (p2one * (A * p2RInv) ^ b) * p2RInv =
      (p2one * p2RInv) * (p2one * (A * p2RInv) ^ (a + b)) by rw [Nat.pow_add]; ac_rfl,
    Nat.mul_mod, p2one_inv, Nat.one_mul, Nat.mod_mod]

theorem mpow2_one (A : Nat) (h : A < p256) : mpow2 A 1 = A := by
  rw [mpow2_val, Nat.pow_one, show p2one * (A * p2RInv) = A * (p2one * p2RInv) by ac_rfl, Nat.mul_mod, p2one_inv,
    Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt h]

theorem iter_msq2_mpow (A k : Nat) : ∀ a, iter msq2 k (mpow2 A a) = mpow2 A (2 ^ k * a) := by
  induction k with
  | zero => intro a; rw [iter, Nat.pow_zero, Nat.one_mul]
  | succ k ih =>
    intro a
    have h2 : msq2 (mpow2 A a) = mpow2 A (2 * a) := by unfold msq2; rw [mpow2_add, Nat.two_mul]
    rw [iter, h2, ih, Nat.pow_succ, Nat.mul_assoc]

/-! ## One window -/

def gdW1 : List BInstr := [.aluImm .add a0 sp 0x67C, .aluImm .add a1 sp 0x65C, .aluImm .add a2 x0 0x20]
def gdW2 : List BInstr := [.aluImm .add a0 sp 0x65C, .aluImm .add a1 sp 0x67C, .aluImm .add a2 x0 0x20]

theorem gdW1_end : blockEnd p256DecompressCode 0x306 gdW1 = some 0x312 := by decide
theorem gdW2_end : blockEnd p256DecompressCode 0x4BA gdW2 = some 0x4C6 := by decide

theorem cp_accV8 {M M' : Word → BitVec 8} {S : Word} {d c : Nat} (_hd : d + 32 ≤ 0x710) (_hc : c + 32 ≤ 0x710)
    (h : ∀ i, i < 8 → memLoad32 M' (S + BitVec.ofNat 32 (d + 4 * i)) = memLoad32 M (S + BitVec.ofNat 32 (c + 4 * i))) :
    accV M' (S + BitVec.ofNat 32 d) 8 = accV M (S + BitVec.ofNat 32 c) 8 :=
  accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, add_ofNat_assoc, h i hi]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The squarings of a window**, from 0x304 to 0x4D0: `z` at `S + 0x65C` is
squared four times in Montgomery form, through the working value at
`S + 0x67C`, with the window's index kept at `S + 0x20`. -/
theorem gd_win_sq {M : Word → BitVec 8} {S : Word} {n : Machine} {w : Word} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0x304 (reg n)) (rsp : reg n sp = S) (ra3 : reg n a3 = w)
    (r27 : reg n (27 : Fin 32) = 8)
    (r18 : reg n (18 : Fin 32) = S + BitVec.ofNat 32 0x69C) (r22 : reg n (22 : Fin 32) = 0xFFFFFFFF)
    (r21 : reg n (21 : Fin 32) = S + BitVec.ofNat 32 0xE8) (r25 : reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x680)
    (r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x6A0)
    (hN0 : memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF) (hN : accV M (S + BitVec.ofNat 32 0xE4) 8 = p256)
    (hz : accV M (S + BitVec.ofNat 32 0x65C) 8 < p256) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x4D0 (reg n') ∧ GdCode n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 = iter msq2 4 (accV M (S + BitVec.ofNat 32 0x65C) 8) ∧
      reg n' a3 = w ∧ reg n' (19 : Fin 32) = S + BitVec.ofNat 32 0x6A0 ∧
      (∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x20) 4 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
        Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → Sep (S + BitVec.ofNat 32 0x65C) 0x80 x 1 → n'.mem x = M x) ∧
      ∀ q, gdSqKeep q = true → reg n' q = reg n q := by
  have hz0 := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb50 : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = (img% memcpyBodyAddress) from rfl]; omega) (by decide)
  have b16 : ∀ c, c + 32 ≤ 0x710 → Sep (S + BitVec.ofNat 32 c) 32 (S + 0xFFFFFFF0) 16 := fun c hc =>
    (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have w48 : ∀ c, c + 32 ≤ 0x710 → (S + BitVec.ofNat 32 c).toNat + 32 < 2 ^ 32 := fun c hc => by
    rw [F.at c (by omega)]; omega
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  -- save the window's index
  obtain ⟨n1, d1, u1⟩ := s.sw C.self gd_at_304 (off' := 0x306) (by decide)
    (by rw [rsp]; show (S + BitVec.ofNat 32 0x20).toNat % 4 = 0; rw [F.at 0x20 (by decide)]; omega)
  rw [rsp, ra3] at u1
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 M (S + BitVec.ofNat 32 0x20) w = M1 := ⟨_, rfl⟩
  have u1' : St M1 GD n1 0x306 (reg n1) := by rw [← hM1]; exact u1.self
  have h1hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M1 x = M x := fun x hx => by
    rw [← hM1]; exact memStore32_get_sep (F.hiOut (c := 0x20) (n := 4) (by decide) hx)
  have C1 := C.hi h1hi
  have g1 : ∀ q, reg n1 q = reg n q := fun q => by rw [u1.regs]
  -- copy z to the working value
  obtain ⟨n2, c2, u2⟩ := u1'.block gdW1 C1.self gdW1_end ⟨trivial, trivial, trivial, trivial⟩
  have r2 : ∀ q, reg n2 q = (runBlock gdW1 (M1, reg n1)).2 q := fun q => by rw [u2.regs]
  have sp1 : reg n1 sp = S := by rw [g1]; exact rsp
  obtain ⟨n3, c3, u3, fr3, k3⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x67C) (src := S + BitVec.ofNat 32 0x65C)
    (S := S) (N := 32) (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St M1 GD n2 0x312 (reg n2)) C1.self C1.K.K gd_at_312 gd_at_316
    (by decide) (by decide) (by rw [r2, runBlock_reg _ _ _ sp u1'.zero (by decide)]; exact sp1)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdW1, upd, ↓reduceIte]; rw [sp1]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdW1, upd, ↓reduceIte]; rw [sp1]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdW1, upd, ↓reduceIte]; (try rw [u1'.zero]); try rfl)
    ⟨C1.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have h3hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n3.mem x = M x := fun x hx => by
    rw [fr3 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x67C) (n := 32) (by decide) hx) (Nat.le_refl _), h1hi x hx]
  have C3 := C.hi h3hi
  have k3' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n3 q = reg n q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ gdW1.filterMap BInstr.dst := by simp only [gdW1]; revert h0 h1 h2; revert q; decide
      rw [k3 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r2, runBlock_reg _ _ _ q u1'.zero hb, g1]
  have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 8, 9] → reg n3 q = reg n q :=
    fun q hq => k3' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  obtain ⟨n4, d4, u4⟩ := u3.aluImm C3.self gd_at_31a (off' := 0x31C) (by decide)
  have g4 : ∀ q, q ≠ a1 → reg n4 q = reg n3 q := fun q h => by rw [u4.regs, updz u3.zero h]
  -- the frame so far, and what the squarings read
  have fr3' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x20) 4 x 1 →
      Sep (S + BitVec.ofNat 32 0x67C) 32 x 1 → n3.mem x = M x := fun x h16 h20 h98 => by
    rw [fr3 x h16, copyBytes_sep h98 (Nat.le_refl _), ← hM1]; exact memStore32_get_sep h20
  have m3 : ∀ d, d + 4 ≤ 0x710 → (d + 4 ≤ 0x20 ∨ 0x24 ≤ d) → (d + 4 ≤ 0x67C ∨ 0x69C ≤ d) →
      memLoad32 n3.mem (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := fun d h1 h2 h3 =>
    memLoad32_congr fun q hq => fr3' _ ((l16 d h1).subR (c := q) (l := 1) (by omega))
      ((sepS S (c := 0x20) (n := 4) (d := d) (k := 4) (by omega) (by decide) (by omega)).subR (c := q) (l := 1) (by omega))
      ((sepS S (c := 0x67C) (n := 32) (d := d) (k := 4) (by omega) (by decide) (by omega)).subR (c := q) (l := 1)
        (by omega))
  have hN3 : accV n3.mem (S + BitVec.ofNat 32 0xE4) 8 = p256 := by
    rw [← hN]; exact accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, m3 _ (by omega) (.inr (by omega)) (.inl (by omega))]
  have hN03 : memLoad32 n3.mem (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF := by
    rw [m3 _ (by decide) (.inr (by decide)) (.inl (by decide)), hN0]
  have hW3 : accV n3.mem (S + BitVec.ofNat 32 0x67C) 8 = accV M (S + BitVec.ofNat 32 0x65C) 8 := by
    refine cp_accV8 (by decide) (by decide) fun i hi => ?_
    rw [load_frame fr3 (l16 _ (by omega)), ← add_ofNat_assoc S 0x67C, cp_word (by omega) (by decide), add_ofNat_assoc, ← hM1,
      memLoad32_store32_sep (sepS S (c := 0x20) (n := 4) (d := 0x65C + 4 * i) (k := 4) (.inl (by omega)) (by decide)
        (by omega))]
  obtain ⟨n5, c5, u5, C5, hv5, h185, fr5, k5⟩ := gd_sqr4 F 4 0 (by decide) C3
    (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem GD n4 0x31C (reg n4))
    (by rw [g4 sp (by decide), kk sp (by decide)]; exact rsp) (by rw [u4.regs]; simp +decide [upd]; rw [u3.zero]; rfl)
    (by rw [g4 27 (by decide), kk 27 (by decide)]; exact r27)
    (by rw [g4 18 (by decide), kk 18 (by decide)]; exact r18) (by rw [g4 22 (by decide), kk 22 (by decide)]; exact r22)
    (by rw [g4 21 (by decide), kk 21 (by decide)]; exact r21) (by rw [g4 25 (by decide), kk 25 (by decide)]; exact r25)
    (by rw [g4 19 (by decide), kk 19 (by decide)]; exact r19) hN03 hN3 (by rw [hW3]; exact hz)
  rw [hW3] at hv5
  have sp5 : reg n5 sp = S := by rw [k5 sp rfl, g4 sp (by decide), kk sp (by decide)]; exact rsp
  -- copy the working value back to z
  obtain ⟨n6, c6, u6⟩ := u5.block gdW2 C5.self gdW2_end ⟨trivial, trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock gdW2 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  obtain ⟨n7, c7, u7, fr7, k7⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x65C) (src := S + BitVec.ofNat 32 0x67C)
    (S := S) (N := 32) (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem GD n6 0x4C6 (reg n6)) C5.self C5.K.K gd_at_4c6 gd_at_4ca
    (by decide) (by decide) (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdW2, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdW2, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdW2, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    ⟨C5.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have h7hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n7.mem x = M x := fun x hx => by
    rw [fr7 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x65C) (n := 32) (by decide) hx) (Nat.le_refl _)]
    exact (fr5 x (sep_of_le (by rw [hb50]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x3C) (n := 4) (by decide) hx)
      (F.hiOut (c := 0x43C) (n := 32) (by decide) hx) (F.hiOut (c := 0x67C) (n := 0x60) (by decide) hx)).trans (h3hi x hx)
  have C7 := C.hi h7hi
  have k7' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n7 q = reg n5 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ gdW2.filterMap BInstr.dst := by simp only [gdW2]; revert h0 h1 h2; revert q; decide
      rw [k7 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r6, runBlock_reg _ _ _ q u5.zero hb]
  have sp7 : reg n7 sp = S := by
    rw [k7' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp5
  -- the frame
  have frame : ∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x20) 4 x 1 →
      Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 →
      Sep (S + BitVec.ofNat 32 0x65C) 0x80 x 1 → n7.mem x = M x := by
    intro x h50 h20 h3C h62 h95
    have h16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
      have := h50.sub (c := 0x30) (l := 16) (by decide)
      rwa [show S + 0xFFFFFFC0 + BitVec.ofNat 32 0x30 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
    have h9548 : Sep (S + BitVec.ofNat 32 0x65C) 32 x 1 := by
      have := h95.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    have h98 : Sep (S + BitVec.ofNat 32 0x67C) 0x60 x 1 := by
      have := h95.sub (c := 0x20) (l := 0x60) (by decide); rwa [add_ofNat_assoc] at this
    have h9848 : Sep (S + BitVec.ofNat 32 0x67C) 32 x 1 := by
      have := h95.sub (c := 0x20) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr7 x h16, copyBytes_sep h9548 (Nat.le_refl _), fr5 x h50 h3C h62 h98, fr3' x h16 h20 h9848]
  have l50 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFC0) 0x40 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb50, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  -- reload the window's index
  obtain ⟨n8, d8, u8⟩ := u7.lw C7.self gd_at_4ce (off' := 0x4D0) (by decide)
    (by rw [sp7]; show (S + BitVec.ofNat 32 0x20).toNat % 4 = 0; rw [F.at 0x20 (by decide)]; omega)
  have w20 : memLoad32 n7.mem (S + BitVec.ofNat 32 0x20) = w := by
    have e : memLoad32 n7.mem (S + BitVec.ofNat 32 0x20) = memLoad32 M1 (S + BitVec.ofNat 32 0x20) := by
      rw [load_frame fr7 (l16 _ (by decide)), cp_word_out (sepS S (.inr (by decide)) (by decide) (by decide))]
      refine memLoad32_congr fun q hq => ?_
      rw [fr5 _ ((l50 0x20 (by decide)).subR (c := q) (l := 1) (by omega))
        ((sepS S (c := 0x3C) (n := 4) (d := 0x20) (k := 4) (.inr (by decide)) (by decide) (by decide)).subR (c := q)
          (l := 1) (by omega))
        ((sepS S (c := 0x43C) (n := 32) (d := 0x20) (k := 4) (.inr (by decide)) (by decide) (by decide)).subR (c := q)
          (l := 1) (by omega))
        ((sepS S (c := 0x67C) (n := 0x60) (d := 0x20) (k := 4) (.inr (by decide)) (by decide) (by decide)).subR (c := q)
          (l := 1) (by omega)), fr3 _ ((l16 0x20 (by decide)).subR (c := q) (l := 1) (by omega)),
        copyBytes_sep ((sepS S (c := 0x67C) (n := 32) (d := 0x20) (k := 4) (.inr (by decide)) (by decide)
          (by decide)).subR (c := q) (l := 1) (by omega)) (Nat.le_refl _)]
    rw [e, ← hM1, memLoad32_store32_same]
  refine ⟨n8, .cons d1 (c2.trans (c3.trans (.cons d4 (c5.trans (c6.trans (c7.trans (.single d8))))))),
    ⟨u8.pc, by rw [u8.mem], fun _ => rfl⟩, by rw [u8.mem]; exact C7, ?_, ?_, ?_, fun x h50 h20 h3C h62 h95 => by
      rw [u8.mem]; exact frame x h50 h20 h3C h62 h95, fun q hq => ?_⟩
  · rw [u8.mem, ← hv5]
    refine cp_accV8 (by decide) (by decide) fun i hi => ?_
    rw [load_frame fr7 (l16 _ (by omega)), ← add_ofNat_assoc S 0x65C, cp_word (by omega) (by decide), add_ofNat_assoc]
  · rw [u8.regs]; simp +decide only [upd, ↓reduceIte]; rw [sp7]; exact w20
  · rw [u8.regs, updz u7.zero (by decide), k7' 19 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact h185
  · have hq3 : q ≠ a3 := pkeep_ne (r := a3) hq rfl
    rw [u8.regs, updz u7.zero hq3, k7' q (pkeep_ne (r := a0) hq rfl) (pkeep_ne (r := a1) hq rfl) (pkeep_ne (r := a2) hq rfl)
      hq3 (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := a6) hq rfl) (pkeep_ne (r := a7) hq rfl)
      (pkeep_ne (r := t0) hq rfl) (pkeep_ne (r := t1) hq rfl) (pkeep_ne (r := 7) hq rfl) (pkeep_ne (r := 28) hq rfl)
      (pkeep_ne (r := 29) hq rfl) (pkeep_ne (r := 30) hq rfl) (pkeep_ne (r := ra) hq rfl), k5 q hq,
      g4 q (pkeep_ne (r := a1) hq rfl), kk q (by revert hq; revert q; decide)]

/-! ## Multiplications -/

set_option maxRecDepth 100000 in
/-- A call to `mul_montgomery_form::<8>` from `decompress` with the modulus
at `S + 0xE4` and factor 1: the 8 words at `out` become the Montgomery
product of the words at `xp` and `yp`. -/
theorem gd_mm {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out xp yp S : Word}
    (s : St Mx GD n off g) (C : GdCode Mx) (F : Fr S 0x710)
    (h1 : fetchRel p256DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : GD + BitVec.ofNat 32 off + imm + o = MM8) (he8 : (GD + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = xp) (ha2 : g a2 = yp)
    (ha3 : g a3 = S + BitVec.ofNat 32 0xE4) (ha4 : g a4 = 1)
    {co cx cy : Nat} (hco : co + 32 ≤ 0x710) (hcx : cx + 32 ≤ 0x710) (hcy : cy + 32 ≤ 0x710)
    (eo : out = S + BitVec.ofNat 32 co) (ex : xp = S + BitVec.ofNat 32 cx) (ey : yp = S + BitVec.ofNat 32 cy)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (acy : cy % 4 = 0)
    (hN0 : memLoad32 Mx (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF) (hN : accV Mx (S + BitVec.ofNat 32 0xE4) 8 = p256)
    (hY : accV Mx yp 8 < p256) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' (off + 8) (reg n') ∧
      accV n'.mem out 8 = p2fm (accV Mx xp 8) (accV Mx yp 8) ∧
      (∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep out 32 x 1 → n'.mem x = Mx x) ∧ reg n' sp = S ∧
      ∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = g q := by
  obtain ⟨n2, c2, u2, hlt, hcg, fr2, sp2, k2⟩ := c2_mm (np := S + BitVec.ofNat 32 0xE4) (Kv := 1) s C.self C.K F h1 h2 hb he8
    hsp ha0 ha1 ha2 ha3 ha4 hco hcx hcy (cn := 0xE4) (by decide) eo ex ey rfl aco acx acy (by decide)
    (by rw [hN0]; decide) (by rw [hN]; exact hY)
  rw [hN] at hlt hcg
  exact ⟨n2, c2, u2, p2_mont hlt hcg, fr2, sp2, k2⟩

/-! ## A window's digit -/

/-- The digit `decompress` reads for window `w` of limb `i`: two bits for
the top window, four otherwise. -/
def gdDig (i w : Nat) (limb : Word) : Word :=
  aluEval .and (if i = 7 ∧ w = 7 then 3 else 15) (aluEval .srl limb (aluEval .sll (BitVec.ofNat 32 w) 2))

theorem gdDig_le (i w : Nat) (limb : Word) : (gdDig i w limb).toNat ≤ 15 := by
  unfold gdDig
  show ((if i = 7 ∧ w = 7 then (3 : Word) else 15) &&& _).toNat ≤ 15
  rw [BitVec.toNat_and]
  refine Nat.le_trans Nat.and_le_left ?_
  by_cases h : i = 7 ∧ w = 7
  · rw [ite_eq_left h]; decide
  · rw [ite_eq_right h]; decide

theorem top_test8 : ∀ i : Nat, i < 8 → ∀ w : Nat, w < 8 →
    branchTaken .beq (aluEval .or (aluEval .xor 7 (BitVec.ofNat 32 w)) (aluEval .xor 7 (BitVec.ofNat 32 i))) 0 =
      decide (i = 7 ∧ w = 7) := by decide

theorem bnd9 : ∀ i : Nat, i < 8 → branchTaken .bgeu (BitVec.ofNat 32 (i + 1)) 9 = false := by decide

def gdD1 : List BInstr := [.lw a0 sp 0x2C, .aluImm .add a1 x0 0x9]
def gdD2 : List BInstr :=
  [.lw a0 sp 0x34, .lw a1 sp 0x38, .alu .xor a0 a0 a1, .lw a1 sp 0x30, .alu .xor a1 a1 a3, .alu .or a1 a1 a0,
   .lw a0 sp 0x24]
def gdD3 : List BInstr := [.lw a1 sp 0x28, .lw a1 a1 0x0, .aluImm .sll a2 a3 0x2, .alu .srl a1 a1 a2, .alu .and a0 a0 a1]

theorem gdD1_end : blockEnd p256DecompressCode 0x4D0 gdD1 = some 0x4D4 := by decide
theorem gdD2_end : blockEnd p256DecompressCode 0x4D8 gdD2 = some 0x4E6 := by decide
theorem gdD3_end : blockEnd p256DecompressCode 0x4EA gdD3 = some 0x4F8 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A window's digit**, from 0x4D0 to the test at 0x4F8: `a0` gets digit
`w` of limb `i` of the exponent, which `S + 0x28` points to. -/
theorem gd_digit {M : Word → BitVec 8} {S : Word} {n : Machine} {i w : Nat} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0x4D0 (reg n)) (rsp : reg n sp = S) (ra3 : reg n a3 = BitVec.ofNat 32 w) (hi : i < 8) (hw : w < 8)
    (s2C : memLoad32 M (S + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 (i + 1))
    (s34 : memLoad32 M (S + BitVec.ofNat 32 0x34) = 7) (s38 : memLoad32 M (S + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 i)
    (s30 : memLoad32 M (S + BitVec.ofNat 32 0x30) = 7) (s24 : memLoad32 M (S + BitVec.ofNat 32 0x24) = 3)
    (s28 : memLoad32 M (S + BitVec.ofNat 32 0x28) = S + BitVec.ofNat 32 (0x41C + 4 * i)) :
    ∃ n', Steps n n' ∧ St M GD n' 0x4F8 (reg n') ∧
      reg n' a0 = gdDig i w (memLoad32 M (S + BitVec.ofNat 32 (0x41C + 4 * i))) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have al : ∀ c, c + 4 ≤ 0x710 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block gdD1 C.self gdD1_end (by
    simp only [BlockOk, BInstr.ok, gdD1]; simp +decide only [and_true]
    rw [rsp]; exact al 0x2C (by decide) (by decide))
  have r1 : ∀ q, reg n1 q = (runBlock gdD1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have t1 : St M GD n1 0x4D4 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := t1.notTaken C.self 0x4D8 gd_at_4d4 (by decide) (by
    rw [r1, r1]; simp +decide only [runBlock, BInstr.run, gdD1, upd, ↓reduceIte]; rw [rsp]
    show branchTaken .bgeu (memLoad32 M (S + BitVec.ofNat 32 0x2C)) 9 = false
    rw [s2C]; exact bnd9 i hi)
  have g2 : ∀ q, reg n2 q = reg n1 q := fun q => by rw [u2.regs]
  have sp2 : reg n2 sp = S := by rw [g2, r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp
  have a32 : reg n2 a3 = BitVec.ofNat 32 w := by rw [g2, r1, runBlock_reg _ _ _ a3 hz (by decide)]; exact ra3
  have t2 : St M GD n2 0x4D8 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := t2.block gdD2 C.self gdD2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdD2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp2]; exact ⟨al 0x34 (by decide) (by decide), al 0x38 (by decide) (by decide), al 0x30 (by decide) (by decide),
      al 0x24 (by decide) (by decide)⟩)
  have r3 : ∀ q, reg n3 q = (runBlock gdD2 (M, reg n2)).2 q := fun q => by rw [u3.regs]
  have e31 : reg n3 a1 = aluEval .or (aluEval .xor 7 (BitVec.ofNat 32 w)) (aluEval .xor 7 (BitVec.ofNat 32 i)) := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, gdD2, upd, ↓reduceIte]; rw [sp2, a32]
    show aluEval .or (aluEval .xor (memLoad32 M (S + BitVec.ofNat 32 0x30)) _)
      (aluEval .xor (memLoad32 M (S + BitVec.ofNat 32 0x34)) (memLoad32 M (S + BitVec.ofNat 32 0x38))) = _
    rw [s30, s34, s38]
  have e30 : reg n3 a0 = 3 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, gdD2, upd, ↓reduceIte]; rw [sp2]
    show memLoad32 M (S + BitVec.ofNat 32 0x24) = 3; exact s24
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → reg n3 q = reg n2 q := fun q h0 h1 => by
    rw [r3, runBlock_reg _ _ _ q t2.zero (by simp only [gdD2]; revert h0 h1; revert q; decide)]
  have t3 : St M GD n3 0x4E6 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  -- the mask, along either path to 0x4EA
  obtain ⟨n4, c4, t4, e40, k4⟩ : ∃ n4, Steps n3 n4 ∧ St M GD n4 0x4EA (reg n4) ∧
      reg n4 a0 = (if i = 7 ∧ w = 7 then 3 else 15) ∧ ∀ q, q ≠ a0 → reg n4 q = reg n3 q := by
    have hb := top_test8 i hi w hw
    rw [← e31, ← t3.zero] at hb
    by_cases ht : i = 7 ∧ w = 7
    · obtain ⟨n4, d4, u4⟩ := t3.taken C.self 0x4EA gd_at_4e6 (by decide) (by rw [hb]; exact decide_eq_true ht)
      exact ⟨n4, .single d4, ⟨u4.pc, u4.mem, fun _ => rfl⟩, by rw [u4.regs, e30, ite_eq_left ht],
        fun q _ => by rw [u4.regs]⟩
    · obtain ⟨n4, d4, u4⟩ := t3.notTaken C.self 0x4E8 gd_at_4e6 (by decide) (by rw [hb]; exact decide_eq_false ht)
      obtain ⟨n5, d5, u5⟩ := u4.self.aluImm C.self gd_at_4e8 (off' := 0x4EA) (by decide)
      refine ⟨n5, .cons d4 (.single d5), ⟨u5.pc, u5.mem, fun _ => rfl⟩, ?_, fun q h => ?_⟩
      · rw [u5.regs, ite_eq_right ht]; simp +decide only [upd, ↓reduceIte]; rw [u4.self.zero]; rfl
      · rw [u5.regs, updz u4.self.zero h, u4.regs]
  have sp4 : reg n4 sp = S := by rw [k4 sp (by decide), k3 sp (by decide) (by decide), sp2]
  have a34 : reg n4 a3 = BitVec.ofNat 32 w := by rw [k4 a3 (by decide), k3 a3 (by decide) (by decide), a32]
  obtain ⟨n5, c5, u5⟩ := t4.block gdD3 C.self gdD3_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdD3]; simp +decide only [upd, ↓reduceIte, and_true]
    rw [sp4]
    refine ⟨al 0x28 (by decide) (by decide), ?_⟩
    show (memLoad32 M (S + BitVec.ofNat 32 0x28) + 0).toNat % 4 = 0
    rw [s28, add_lit_zero]; exact al _ (by omega) (by omega))
  refine ⟨n5, c1.trans (.cons d2 (c3.trans (c4.trans c5))), ⟨u5.pc, u5.mem, fun _ => rfl⟩, ?_, fun q h0 h1 h2 => ?_⟩
  · rw [u5.regs]; simp +decide only [runBlock, BInstr.run, gdD3, upd, ↓reduceIte]
    rw [sp4, a34, e40]
    show aluEval .and _ (aluEval .srl (memLoad32 M (memLoad32 M (S + BitVec.ofNat 32 0x28) + 0)) _) = _
    rw [s28, add_lit_zero]; rfl
  · rw [u5.regs, runBlock_reg _ _ _ q t4.zero (by simp only [gdD3]; revert h0 h1 h2; revert q; decide), k4 q h0,
      k3 q h0 h1, g2, r1, runBlock_reg _ _ _ q hz (by simp only [gdD1]; revert h0 h1; revert q; decide)]

def gdM1 : List BInstr :=
  [.aluImm .sll a0 a0 0x5, .aluImm .add a2 sp 0x21C, .alu .add a2 a2 a0, .aluImm .add a0 sp 0x43C,
   .aluImm .add a1 sp 0x65C, .aluImm .add a4 x0 0x1, .alu .add (8 : Fin 32) x0 a3, .aluImm .add a3 sp 0xE4]
def gdM2 : List BInstr := [.aluImm .add a0 sp 0x65C, .aluImm .add a1 sp 0x43C, .aluImm .add a2 x0 0x20]

theorem gdM1_end : blockEnd p256DecompressCode 0x4FC gdM1 = some 0x510 := by decide
theorem gdM2_end : blockEnd p256DecompressCode 0x518 gdM2 = some 0x524 := by decide

theorem tbl_addr8 {S d : Word} (F : Fr S 0x710) (hd : d.toNat ≤ 15) :
    aluEval .add (aluEval .add S 0x21C) (aluEval .sll d 5) = S + BitVec.ofNat 32 (0x21C + 32 * d.toNat) := by
  have := F.hi
  apply BitVec.eq_of_toNat_eq
  show ((S + BitVec.ofNat 32 0x21C) + d <<< ((5 : Word).toNat % 32)).toNat = (S + BitVec.ofNat 32 (0x21C + 32 * d.toNat)).toNat
  rw [F.at _ (by omega), BitVec.toNat_add, BitVec.toNat_shiftLeft, F.at 0x21C (by decide),
    show (5 : Word).toNat % 32 = 5 from rfl, Nat.shiftLeft_eq]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **A window's multiplication**, from the digit's test at 0x4F8 back to the
window loop at 0x2F0: unless the digit `d` in `a0` is zero, `z` at
`S + 0x65C` becomes its Montgomery product with table entry `d`. -/
theorem gd_win_mul {M : Word → BitVec 8} {S : Word} {n : Machine} {w d : Word} {A : Nat} (C : GdCode M)
    (F : Fr S 0x710) (s : St M GD n 0x4F8 (reg n)) (rsp : reg n sp = S) (ra0 : reg n a0 = d) (hd : d.toNat ≤ 15)
    (ra3 : reg n a3 = w) (hN0 : memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF)
    (hN : accV M (S + BitVec.ofNat 32 0xE4) 8 = p256)
    (hpw : ∀ k, k < 16 → accV M (S + BitVec.ofNat 32 (0x21C + 32 * k)) 8 = mpow2 A k) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x2F0 (reg n') ∧ GdCode n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 =
        (if d = 0 then accV M (S + BitVec.ofNat 32 0x65C) 8 else p2fm (accV M (S + BitVec.ofNat 32 0x65C) 8) (mpow2 A d.toNat)) ∧
      reg n' a3 = w ∧
      (∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 →
        Sep (S + BitVec.ofNat 32 0x65C) 32 x 1 → n'.mem x = M x) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  by_cases h0 : d = 0
  · obtain ⟨n1, d1, u1⟩ := s.taken C.self 0x2F0 gd_at_4f8 (by decide) (by
      show (reg n a0 == reg n x0) = true; rw [ra0, hz, h0]; rfl)
    exact ⟨n1, .single d1, ⟨u1.pc, by rw [u1.mem], fun _ => rfl⟩, by rw [u1.mem]; exact C, by rw [u1.mem, ite_eq_left h0],
      by rw [u1.regs]; exact ra3, fun x _ _ _ => by rw [u1.mem], fun q _ => by rw [u1.regs]⟩
  obtain ⟨n1, d1, u1⟩ := s.notTaken C.self 0x4FC gd_at_4f8 (by decide) (by
    show (reg n a0 == reg n x0) = false; rw [ra0, hz]; exact beq_false_of_ne h0)
  have v1 : St M GD n1 0x4FC (reg n1) := u1.self
  have g1 : ∀ q, reg n1 q = reg n q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2⟩ := v1.block gdM1 C.self gdM1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial⟩
  have r2 : ∀ q, reg n2 q = (runBlock gdM1 (M, reg n1)).2 q := fun q => by rw [u2.regs]
  have sp1 : reg n1 sp = S := by rw [g1]; exact rsp
  have hk : d.toNat < 16 := by omega
  obtain ⟨n3, c3, u3, hv3, fr3, sp3, k3⟩ := gd_mm (out := S + BitVec.ofNat 32 0x43C) (xp := S + BitVec.ofNat 32 0x65C)
    (yp := S + BitVec.ofNat 32 (0x21C + 32 * d.toNat)) (S := S) (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St M GD n2 0x510 (reg n2))
    C F gd_at_510 gd_at_514 (by decide) (by decide)
    (by rw [r2, runBlock_reg _ _ _ sp v1.zero (by decide)]; exact sp1)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdM1, upd, ↓reduceIte]; rw [sp1]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdM1, upd, ↓reduceIte]; rw [sp1]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdM1, upd, ↓reduceIte]; rw [sp1, g1, ra0]
        exact tbl_addr8 F hd)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdM1, upd, ↓reduceIte]; rw [sp1]; rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdM1, upd, ↓reduceIte]; (try rw [v1.zero]); try rfl)
    (co := 0x43C) (cx := 0x65C) (cy := 0x21C + 32 * d.toNat) (by decide) (by decide) (by omega) rfl rfl rfl
    (by decide) (by decide) (by omega) hN0 hN (by rw [hpw _ hk]; exact mpow2_lt A _)
  rw [hpw _ hk] at hv3
  have hbF : (S + 0xFFFFFF40).toNat = S.toNat - 0xC0 := F.below 0xC0 (by decide) (by decide)
  have h3hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n3.mem x = M x := fun x hx =>
    fr3 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x43C) (n := 32) (by decide) hx)
  have C3 := C.hi h3hi
  have k3' : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n q := fun q hq => by
    have hb : q ∉ gdM1.filterMap BInstr.dst := by simp only [gdM1]; revert hq; revert q; decide
    rw [k3 q (by revert hq; revert q; decide), r2, runBlock_reg _ _ _ q v1.zero hb, g1]
  have e8 : reg n3 (8 : Fin 32) = w := by
    rw [k3 8 (by decide), r2]; simp +decide only [runBlock, BInstr.run, gdM1, upd, ↓reduceIte]; rw [g1, ra3]
    exact BitVec.zero_add _
  -- copy the product to z
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = (img% memcpyBodyAddress) from rfl]; omega) (by decide)
  have b16 : ∀ c, c + 32 ≤ 0x710 → Sep (S + BitVec.ofNat 32 c) 32 (S + 0xFFFFFFF0) 16 := fun c hc =>
    (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have w48 : ∀ c, c + 32 ≤ 0x710 → (S + BitVec.ofNat 32 c).toNat + 32 < 2 ^ 32 := fun c hc => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n4, c4, u4⟩ := u3.block gdM2 C3.self gdM2_end ⟨trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock gdM2 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  obtain ⟨n5, c5, u5, fr5, k5⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x65C) (src := S + BitVec.ofNat 32 0x43C)
    (S := S) (N := 32) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem GD n4 0x524 (reg n4)) C3.self C3.K.K gd_at_524 gd_at_528
    (by decide) (by decide) (by rw [r4, runBlock_reg _ _ _ sp u3.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdM2, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdM2, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdM2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    ⟨C3.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have k5' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n5 q = reg n3 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ gdM2.filterMap BInstr.dst := by simp only [gdM2]; revert h0 h1 h2; revert q; decide
      rw [k5 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r4, runBlock_reg _ _ _ q u3.zero hb]
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have h5hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n5.mem x = M x := fun x hx => by
    rw [fr5 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x65C) (n := 32) (by decide) hx) (Nat.le_refl _), h3hi x hx]
  have C5 := C.hi h5hi
  obtain ⟨n6, d6, u6⟩ := u5.alu C5.self gd_at_52c (off' := 0x52E) (by decide)
  obtain ⟨n7, d7, u7⟩ := u6.self.jump C5.self gd_at_52e (off' := 0x2F0) (by decide) (by rw [u6.self.pc]; decide)
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  refine ⟨n7, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (.single d7)))))),
    ⟨u7.pc, by rw [u7.mem], fun _ => rfl⟩, by rw [u7.mem]; exact C5, ?_, ?_, fun x hF h62 h95 => ?_,
    fun q hq => ?_⟩
  · rw [ite_eq_right h0, u7.mem, ← hv3]
    refine cp_accV8 (by decide) (by decide) fun i hi => ?_
    rw [load_frame fr5 (l16 _ (by omega)), ← add_ofNat_assoc S 0x65C, cp_word (by omega) (by decide), add_ofNat_assoc]
  · rw [u7.regs, u6.regs]; simp +decide only [upd, ↓reduceIte]; rw [u5.zero, k5' 8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), e8]; exact BitVec.zero_add _
  · have h16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
      have := hF.sub (c := 0xB0) (l := 16) (by decide)
      rwa [show S + 0xFFFFFF40 + BitVec.ofNat 32 0xB0 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
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
def sqrtExp2 : Nat := (p256 + 1) / 4

/-- Limb `i` of `sqrtExp2`. -/
def expLimb2 (i : Nat) : Word := BitVec.ofNat 32 (sqrtExp2 / 2 ^ (32 * i) % 2 ^ 32)

set_option exponentiation.threshold 600 in
set_option maxRecDepth 100000 in
theorem exp_digit2 : ∀ i, i < 8 → ∀ w, w < 8 →
    (gdDig i w (expLimb2 i)).toNat = sqrtExp2 / 2 ^ (4 * (8 * i + w)) % 16 := by
  unfold sqrtExp2 expLimb2 p256; decide

set_option exponentiation.threshold 600 in
theorem exp_top2 : sqrtExp2 / 2 ^ (4 * 64) = 0 := by unfold sqrtExp2 p256; decide

theorem div16 (x g : Nat) : x / 2 ^ (4 * g) = 16 * (x / 2 ^ (4 * (g + 1))) + x / 2 ^ (4 * g) % 16 := by
  have e : x / 2 ^ (4 * (g + 1)) = x / 2 ^ (4 * g) / 16 := by
    rw [Nat.div_div_eq_div_mul, show 4 * (g + 1) = 4 * g + 4 by omega, Nat.pow_add]
  rw [e]; exact (Nat.div_add_mod _ 16).symm

/-! ## The window loop's invariant -/

/-- What the window loop keeps in `decompress`'s frame while it works on
limb `i`: the modulus, the table of `A`'s first 16 Montgomery powers, the
exponent, and the loop's spilled counters. -/
structure GdWin (M : Word → BitVec 8) (S : Word) (A i : Nat) : Prop where
  N0 : memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF
  N : accV M (S + BitVec.ofNat 32 0xE4) 8 = p256
  pw : ∀ k, k < 16 → accV M (S + BitVec.ofNat 32 (0x21C + 32 * k)) 8 = mpow2 A k
  ex : ∀ j, j < 8 → memLoad32 M (S + BitVec.ofNat 32 (0x41C + 4 * j)) = expLimb2 j
  s2C : memLoad32 M (S + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 (i + 1)
  s34 : memLoad32 M (S + BitVec.ofNat 32 0x34) = 7
  s38 : memLoad32 M (S + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 i
  s30 : memLoad32 M (S + BitVec.ofNat 32 0x30) = 7
  s24 : memLoad32 M (S + BitVec.ofNat 32 0x24) = 3
  s28 : memLoad32 M (S + BitVec.ofNat 32 0x28) = S + BitVec.ofNat 32 (0x41C + 4 * i)

/-- The registers that hold the squarings' pointers and constants. -/
structure GdRegs (n : Machine) (S : Word) : Prop where
  sp : reg n sp = S
  r27 : reg n (27 : Fin 32) = 8
  r18 : reg n (18 : Fin 32) = S + BitVec.ofNat 32 0x69C
  r22 : reg n (22 : Fin 32) = 0xFFFFFFFF
  r21 : reg n (21 : Fin 32) = S + BitVec.ofNat 32 0xE8
  r25 : reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x680
  r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x6A0

/-- A window changes only these parts of memory. -/
def GdWinFrame (S : Word) (M' M : Word → BitVec 8) : Prop :=
  ∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep (S + BitVec.ofNat 32 0x20) 4 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
    Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → Sep (S + BitVec.ofNat 32 0x65C) 0x80 x 1 → M' x = M x

theorem GdWinFrame.trans {S : Word} {M1 M2 M3 : Word → BitVec 8} (h1 : GdWinFrame S M2 M1) (h2 : GdWinFrame S M3 M2) :
    GdWinFrame S M3 M1 := fun x a b c d e => (h2 x a b c d e).trans (h1 x a b c d e)

/-- A word at frame offset `d` that a window does not change. -/
theorem GdWinFrame.word {S : Word} {M' M : Word → BitVec 8} (F : Fr S 0x710) (h : GdWinFrame S M' M) {d : Nat}
    (hd : (0x24 ≤ d ∧ d + 4 ≤ 0x3C) ∨ (0x40 ≤ d ∧ d + 4 ≤ 0x43C) ∨ (0x45C ≤ d ∧ d + 4 ≤ 0x65C) ∨ d + 4 ≤ 0x20) :
    memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := by
  have hSl := F.lo; have hSh := F.hi
  have hbF : (S + 0xFFFFFF40).toNat = S.toNat - 0xC0 := F.below 0xC0 (by decide) (by decide)
  refine memLoad32_congr fun q hq => ?_
  rw [add_ofNat_assoc]
  have hF : Sep (S + 0xFFFFFF40) 0xC0 (S + BitVec.ofNat 32 (d + q)) 1 :=
    sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega)
  have hx : ∀ c l, c + l ≤ 0x710 → (c + l ≤ d + q ∨ d + q + 1 ≤ c) → Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 (d + q)) 1 :=
    fun c l h1 h2 => sepS S h2 (by omega) (by omega)
  exact h _ hF (hx 0x20 4 (by decide) (by omega)) (hx 0x3C 4 (by decide) (by omega)) (hx 0x43C 32 (by decide) (by omega))
    (hx 0x65C 0x80 (by decide) (by omega))

theorem GdWin.frame {M M' : Word → BitVec 8} {S : Word} {A i : Nat} (F : Fr S 0x710) (W : GdWin M S A i)
    (h : GdWinFrame S M' M) : GdWin M' S A i := by
  have wd := fun d hd => GdWinFrame.word (d := d) F h hd
  have lo : ∀ d, 0x24 ≤ d → d + 4 ≤ 0x3C → memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => wd d (.inl ⟨h1, h2⟩)
  have mid : ∀ d, 0x40 ≤ d → d + 4 ≤ 0x43C → memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => wd d (.inr (.inl ⟨h1, h2⟩))
  refine ⟨?_, ?_, fun k hk => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mid 0xE4 (by decide) (by decide)]; exact W.N0
  · rw [← W.N]; exact accV_congr2 8 fun j hj => by rw [add_ofNat_assoc, mid _ (by omega) (by omega)]
  · rw [← W.pw k hk]; exact accV_congr2 8 fun j hj => by rw [add_ofNat_assoc, mid _ (by omega) (by omega)]
  · rw [mid _ (by omega) (by omega)]; exact W.ex j hj
  · rw [lo 0x2C (by decide) (by decide)]; exact W.s2C
  · rw [lo 0x34 (by decide) (by decide)]; exact W.s34
  · rw [lo 0x38 (by decide) (by decide)]; exact W.s38
  · rw [lo 0x30 (by decide) (by decide)]; exact W.s30
  · rw [lo 0x24 (by decide) (by decide)]; exact W.s24
  · rw [lo 0x28 (by decide) (by decide)]; exact W.s28

theorem win_ne0 : ∀ c : Nat, c < 8 → (BitVec.ofNat 32 (c + 1) == (0 : Word)) = false := by decide
theorem win_dec : ∀ c : Nat, c < 8 → BitVec.ofNat 32 (c + 1) + 0xFFFFFFFF = BitVec.ofNat 32 c := by decide
theorem limb_ne8 : ∀ i : Nat, i < 8 → branchTaken .bne (BitVec.ofNat 32 i) 7 = decide (i ≠ 7) := by decide
theorem win_eq7 : ∀ c : Nat, c < 8 → branchTaken .beq (BitVec.ofNat 32 c) 7 = decide (c = 7) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **One window**, from the window loop's head at 0x2F0 with `c + 1`
windows of limb `i` left to its head again with `c` left: `z` at
`S + 0x65C` goes from `A^⌊e / 16^(8i + c + 1)⌋` to `A^⌊e / 16^(8i + c)⌋`
in Montgomery form, for the square-root exponent `e`. -/
theorem gd_window {M : Word → BitVec 8} {S : Word} {n : Machine} {i c A : Nat} (C : GdCode M) (F : Fr S 0x710)
    (W : GdWin M S A i) (R : GdRegs n S) (s : St M GD n 0x2F0 (reg n)) (ra3 : reg n a3 = BitVec.ofNat 32 (c + 1))
    (hc : c < 8) (hi : i < 8)
    (hz : accV M (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (sqrtExp2 / 2 ^ (4 * (8 * i + c + 1)))) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x2F0 (reg n') ∧ GdCode n'.mem ∧ GdWinFrame S n'.mem M ∧ GdRegs n' S ∧
      reg n' a3 = BitVec.ofNat 32 c ∧
      accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (sqrtExp2 / 2 ^ (4 * (8 * i + c))) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz0 := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have al : ∀ c, c + 4 ≤ 0x710 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  -- the head: count the window, and skip the squarings for the top one
  obtain ⟨n1, d1, u1⟩ := s.notTaken C.self 0x2F4 gd_at_2f0 (by decide) (by
    show (reg n a3 == reg n x0) = false; rw [ra3, hz0]; exact win_ne0 c hc)
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm C.self gd_at_2f4 (off' := 0x2F6) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.lw C.self gd_at_2f6 (off' := 0x2F8) (by decide)
    (by rw [u2.regs, updz u1.self.zero (by decide), u1.regs, R.sp]; exact al 0x34 (by decide) (by decide))
  obtain ⟨n4, d4, u4⟩ := u3.self.lw C.self gd_at_2f8 (off' := 0x2FA) (by decide)
    (by rw [u3.regs, updz u2.self.zero (by decide), u2.regs, updz u1.self.zero (by decide), u1.regs, R.sp]
        exact al 0x38 (by decide) (by decide))
  have g4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → reg n4 q = reg n q := fun q h0 h1 h3 => by
    rw [u4.regs, updz u3.self.zero h1, u3.regs, updz u2.self.zero h0, u2.regs, updz u1.self.zero h3, u1.regs]
  have e43 : reg n4 a3 = BitVec.ofNat 32 c := by
    rw [u4.regs, updz u3.self.zero (by decide), u3.regs, updz u2.self.zero (by decide), u2.regs]
    simp +decide only [upd, ↓reduceIte]; rw [u1.regs, ra3]; exact win_dec c hc
  have e40 : reg n4 a0 = 7 := by
    rw [u4.regs, updz u3.self.zero (by decide), u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [u2.regs, updz u1.self.zero (by decide), u1.regs, R.sp]; exact W.s34
  have e41 : reg n4 a1 = BitVec.ofNat 32 i := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [u3.regs, updz u2.self.zero (by decide), u2.regs, updz u1.self.zero (by decide), u1.regs, R.sp]
    exact W.s38
  have t4 : St M GD n4 0x2FA (reg n4) := u4.self
  obtain ⟨n5, c5, t5, e53, k5⟩ : ∃ n5, Steps n4 n5 ∧
      St M GD n5 (if i = 7 ∧ c = 7 then 0x4D0 else 0x304) (reg n5) ∧ reg n5 a3 = BitVec.ofNat 32 c ∧
      ∀ q, q ≠ a0 → reg n5 q = reg n4 q := by
    have hb := limb_ne8 i hi
    rw [← e41, ← e40] at hb
    by_cases h11 : i = 7
    · obtain ⟨n5, d5, u5⟩ := t4.notTaken C.self 0x2FE gd_at_2fa (by decide) (by rw [hb]; exact decide_eq_false (fun h => h h11))
      obtain ⟨n6, d6, u6⟩ := u5.self.lw C.self gd_at_2fe (off' := 0x300) (by decide)
        (by rw [u5.regs, g4 sp (by decide) (by decide) (by decide), R.sp]; exact al 0x30 (by decide) (by decide))
      have e63 : reg n6 a3 = BitVec.ofNat 32 c := by rw [u6.regs, updz u5.self.zero (by decide), u5.regs, e43]
      have e60 : reg n6 a0 = 7 := by
        rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
        rw [u5.regs, g4 sp (by decide) (by decide) (by decide), R.sp]; exact W.s30
      have hb7 := win_eq7 c hc
      rw [← e63, ← e60] at hb7
      by_cases h7 : c = 7
      · obtain ⟨n7, d7, u7⟩ := u6.self.taken C.self 0x4D0 gd_at_300 (by decide) (by rw [hb7]; exact decide_eq_true h7)
        refine ⟨n7, .cons d5 (.cons d6 (.single d7)), by rw [ite_eq_left ⟨h11, h7⟩]; exact u7.self, by rw [u7.regs, e63],
          fun q h => by rw [u7.regs, u6.regs, updz u5.self.zero h, u5.regs]⟩
      · obtain ⟨n7, d7, u7⟩ := u6.self.notTaken C.self 0x304 gd_at_300 (by decide) (by rw [hb7]; exact decide_eq_false h7)
        refine ⟨n7, .cons d5 (.cons d6 (.single d7)), by rw [ite_eq_right (fun h => h7 h.2)]; exact u7.self,
          by rw [u7.regs, e63], fun q h => by rw [u7.regs, u6.regs, updz u5.self.zero h, u5.regs]⟩
    · obtain ⟨n5, d5, u5⟩ := t4.taken C.self 0x304 gd_at_2fa (by decide) (by rw [hb]; exact decide_eq_true h11)
      exact ⟨n5, .single d5, by rw [ite_eq_right (fun h => h11 h.1)]; exact u5.self, by rw [u5.regs, e43],
        fun q _ => by rw [u5.regs]⟩
  have k5' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → reg n5 q = reg n q := fun q h0 h1 h3 => by
    rw [k5 q h0, g4 q h0 h1 h3]
  have R5 : GdRegs n5 S := ⟨by rw [k5' sp (by decide) (by decide) (by decide)]; exact R.sp,
    by rw [k5' 27 (by decide) (by decide) (by decide)]; exact R.r27,
    by rw [k5' 18 (by decide) (by decide) (by decide)]; exact R.r18, by rw [k5' 22 (by decide) (by decide) (by decide)]; exact R.r22,
    by rw [k5' 21 (by decide) (by decide) (by decide)]; exact R.r21, by rw [k5' 25 (by decide) (by decide) (by decide)]; exact R.r25,
    by rw [k5' 19 (by decide) (by decide) (by decide)]; exact R.r19⟩
  -- the squarings, unless this is the top window
  obtain ⟨n6, c6, t6, C6, fr6, R6, e63, hz6, k6⟩ : ∃ n6, Steps n5 n6 ∧ St n6.mem GD n6 0x4D0 (reg n6) ∧ GdCode n6.mem ∧
      GdWinFrame S n6.mem M ∧ GdRegs n6 S ∧ reg n6 a3 = BitVec.ofNat 32 c ∧
      accV n6.mem (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (16 * (sqrtExp2 / 2 ^ (4 * (8 * i + c + 1)))) ∧
      ∀ q : Fin 32, q.val ∈ [3, 4] → reg n6 q = reg n5 q := by
    by_cases ht : i = 7 ∧ c = 7
    · rw [ite_eq_left ht] at t5
      obtain ⟨h11, h7⟩ := ht
      subst h11; subst h7
      refine ⟨n5, .refl _, ⟨t5.pc, by rw [t5.mem], fun _ => rfl⟩, by rw [t5.mem]; exact C,
        fun x _ _ _ _ _ => by rw [t5.mem], R5, e53, ?_, fun q _ => rfl⟩
      rw [t5.mem, hz, show 4 * (8 * 7 + 7 + 1) = 4 * 64 from rfl, exp_top2]
    · rw [ite_eq_right ht] at t5
      obtain ⟨n6, c6, u6, C6, hv6, a36, h186, fr6, k6⟩ := gd_win_sq (w := BitVec.ofNat 32 c) C F t5 R5.sp e53 R5.r27
        R5.r18 R5.r22 R5.r21 R5.r25 R5.r19 W.N0 W.N (by rw [hz]; exact mpow2_lt A _)
      refine ⟨n6, c6, u6, C6, fun x hF h20 h3C h62 h95 => fr6 x ?_ h20 h3C h62 h95, ⟨by rw [k6 sp rfl]; exact R5.sp,
        by rw [k6 27 rfl]; exact R5.r27, by rw [k6 18 rfl]; exact R5.r18,
        by rw [k6 22 rfl]; exact R5.r22, by rw [k6 21 rfl]; exact R5.r21, by rw [k6 25 rfl]; exact R5.r25, h186⟩, a36,
        by rw [hv6, hz, iter_msq2_mpow]; try rfl, fun q hq => k6 q (by revert hq; revert q; decide)⟩
      have := hF.sub (c := 0x80) (l := 0x40) (by decide)
      rwa [show S + 0xFFFFFF40 + BitVec.ofNat 32 0x80 = S + 0xFFFFFFC0 by rw [BitVec.add_assoc]; rfl] at this
  have W6 := W.frame F fr6
  -- the digit and the multiplication
  obtain ⟨n7, c7, t7, e70, k7⟩ := gd_digit (i := i) (w := c) C6 F t6 R6.sp e63 hi hc W6.s2C W6.s34 W6.s38 W6.s30 W6.s24
    W6.s28
  rw [W6.ex i hi] at e70
  have sp7 : reg n7 sp = S := by rw [k7 sp (by decide) (by decide) (by decide)]; exact R6.sp
  have a37 : reg n7 a3 = BitVec.ofNat 32 c := by rw [k7 a3 (by decide) (by decide) (by decide)]; exact e63
  obtain ⟨n8, c8, u8, C8, hv8, a38, fr8, k8⟩ := gd_win_mul (A := A) C6 F t7 sp7 e70 (gdDig_le i c _) a37
    W6.N0 W6.N W6.pw
  have k78 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 22, 25, 27] → reg n8 q = reg n6 q := fun q hq => by
    rw [k8 q (by revert hq; revert q; decide), k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)]
  have hd := exp_digit2 i hi c hc
  refine ⟨n8, .cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans (c6.trans (c7.trans c8)))))),
    u8, C8, fr6.trans (fun x hF h20 h3C h62 h95 => fr8 x hF h62 (by
      have := h95.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this)),
    ⟨by rw [k78 sp (by decide)]; exact R6.sp,
      by rw [k78 27 (by decide)]; exact R6.r27, by rw [k78 18 (by decide)]; exact R6.r18,
      by rw [k78 22 (by decide)]; exact R6.r22, by rw [k78 21 (by decide)]; exact R6.r21,
      by rw [k78 25 (by decide)]; exact R6.r25, by rw [k78 19 (by decide)]; exact R6.r19⟩, a38, ?_,
    by rw [k78 3 (by decide), k6 3 (by decide), k5' 3 (by decide) (by decide) (by decide)],
    by rw [k78 4 (by decide), k6 4 (by decide), k5' 4 (by decide) (by decide) (by decide)]⟩
  rw [hv8, hz6, show 8 * i + c + 1 = (8 * i + c) + 1 from rfl, div16 sqrtExp2 (8 * i + c)]
  by_cases h0 : gdDig i c (expLimb2 i) = 0
  · rw [ite_eq_left h0, ← hd, h0]; rfl
  · rw [ite_eq_right h0, mpow2_add, ← hd]

set_option maxRecDepth 100000 in
/-- **The windows of limb `i`**, from the window loop's head with `c`
windows left to its head with none left. -/
theorem gd_windows {S : Word} {i A : Nat} (F : Fr S 0x710) (hi : i < 8) :
    ∀ c, c ≤ 8 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → GdWin M S A i → GdRegs n S →
      St M GD n 0x2F0 (reg n) → reg n a3 = BitVec.ofNat 32 c →
      accV M (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (sqrtExp2 / 2 ^ (4 * (8 * i + c))) →
      ∃ n', Steps n n' ∧ St n'.mem GD n' 0x2F0 (reg n') ∧ GdCode n'.mem ∧ GdWinFrame S n'.mem M ∧ GdRegs n' S ∧
        reg n' a3 = 0 ∧ accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (sqrtExp2 / 2 ^ (4 * (8 * i))) ∧
        reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  intro c
  induction c with
  | zero =>
    intro _ M n C _ R s ra3 hz
    exact ⟨n, .refl _, by rw [s.mem]; exact s, by rw [s.mem]; exact C, fun x _ _ _ _ _ => by rw [s.mem], R, ra3,
      by rw [s.mem, hz]; rfl, rfl, rfl⟩
  | succ c ih =>
    intro hc M n C W R s ra3 hz
    obtain ⟨n1, c1, u1, C1, fr1, R1, a31, hz1, g31, g41⟩ := gd_window C F W R s ra3 (by omega) hi
      (by rw [hz]; rfl)
    obtain ⟨n2, c2, u2, C2, fr2, R2, a32, hz2, g32, g42⟩ := ih (by omega) C1 (W.frame F fr1) R1 u1 a31 hz1
    exact ⟨n2, c1.trans c2, u2, C2, fr1.trans fr2, R2, a32, hz2, by rw [g32, g31], by rw [g42, g41]⟩

/-! ## The limb loop -/

/-- What the whole exponentiation keeps in `decompress`'s frame. -/
structure GdBase (M : Word → BitVec 8) (S : Word) (A : Nat) : Prop where
  N0 : memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF
  N : accV M (S + BitVec.ofNat 32 0xE4) 8 = p256
  pw : ∀ k, k < 16 → accV M (S + BitVec.ofNat 32 (0x21C + 32 * k)) 8 = mpow2 A k
  ex : ∀ j, j < 8 → memLoad32 M (S + BitVec.ofNat 32 (0x41C + 4 * j)) = expLimb2 j
  s1C : memLoad32 M (S + BitVec.ofNat 32 0x1C) = 8
  s34 : memLoad32 M (S + BitVec.ofNat 32 0x34) = 7
  s30 : memLoad32 M (S + BitVec.ofNat 32 0x30) = 7
  s24 : memLoad32 M (S + BitVec.ofNat 32 0x24) = 3

theorem GdBase.frame {M M' : Word → BitVec 8} {S : Word} {A : Nat} (F : Fr S 0x710) (B : GdBase M S A)
    (h : GdWinFrame S M' M) : GdBase M' S A := by
  have wd := fun d hd => GdWinFrame.word (d := d) F h hd
  have lo : ∀ d, 0x24 ≤ d → d + 4 ≤ 0x3C → memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => wd d (.inl ⟨h1, h2⟩)
  have mid : ∀ d, 0x40 ≤ d → d + 4 ≤ 0x43C → memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => wd d (.inr (.inl ⟨h1, h2⟩))
  refine ⟨?_, ?_, fun k hk => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [mid 0xE4 (by decide) (by decide)]; exact B.N0
  · rw [← B.N]; exact accV_congr2 8 fun j hj => by rw [add_ofNat_assoc, mid _ (by omega) (by omega)]
  · rw [← B.pw k hk]; exact accV_congr2 8 fun j hj => by rw [add_ofNat_assoc, mid _ (by omega) (by omega)]
  · rw [mid _ (by omega) (by omega)]; exact B.ex j hj
  · rw [wd 0x1C (.inr (.inr (.inr (by decide))))]; exact B.s1C
  · rw [lo 0x34 (by decide) (by decide)]; exact B.s34
  · rw [lo 0x30 (by decide) (by decide)]; exact B.s30
  · rw [lo 0x24 (by decide) (by decide)]; exact B.s24

/-- The parts of memory the exponentiation's loops change. -/
def GdLoopFrame (S : Word) (M' M : Word → BitVec 8) : Prop :=
  ∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep (S + BitVec.ofNat 32 0x20) 0x20 x 1 →
    Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → Sep (S + BitVec.ofNat 32 0x65C) 0x80 x 1 → M' x = M x

theorem GdLoopFrame.trans {S : Word} {M1 M2 M3 : Word → BitVec 8} (h1 : GdLoopFrame S M2 M1) (h2 : GdLoopFrame S M3 M2) :
    GdLoopFrame S M3 M1 := fun x a b c d => (h2 x a b c d).trans (h1 x a b c d)

theorem GdWinFrame.loop {S : Word} {M' M : Word → BitVec 8} (h : GdWinFrame S M' M) : GdLoopFrame S M' M := fun x a b c d =>
  h x a (by have := b.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)
    (by have := b.sub (c := 0x1C) (l := 4) (by decide); rwa [add_ofNat_assoc] at this) c d

def gdH1 : List BInstr :=
  [.sw sp (9 : Fin 32) 0x2C, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, .lw a3 sp 0x1C, .lw a0 sp 0x34,
   .sw sp (9 : Fin 32) 0x38]
def gdH2 : List BInstr := [.lw a0 sp 0x38, .aluImm .sll a0 a0 0x2, .aluImm .add a1 sp 0x41C, .alu .add a0 a0 a1, .sw sp a0 0x28]

theorem gdH1_end : blockEnd p256DecompressCode 0x2D4 gdH1 = some 0x2DE := by decide
theorem gdH2_end : blockEnd p256DecompressCode 0x2E4 gdH2 = some 0x2F0 := by decide

theorem lsucc_dec8 : ∀ i : Nat, i < 8 → BitVec.ofNat 32 (i + 1) + 0xFFFFFFFF = BitVec.ofNat 32 i := by decide
theorem limb_addr8 {S : Word} (F : Fr S 0x710) {i : Nat} (hi : i < 8) :
    aluEval .add (aluEval .sll (BitVec.ofNat 32 i) 2) (aluEval .add S 0x41C) = S + BitVec.ofNat 32 (0x41C + 4 * i) := by
  have := F.hi
  rw [sll8 i hi]
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 (4 * i) + (S + BitVec.ofNat 32 0x41C)).toNat = (S + BitVec.ofNat 32 (0x41C + 4 * i)).toNat
  rw [F.at _ (by omega), BitVec.toNat_add, F.at 0x41C (by decide), BitVec.toNat_ofNat]
  omega

theorem slot_word8 {M : Word → BitVec 8} {S v : Word} {c d : Nat} (hc : c + 4 ≤ 0x710) (hd : d + 4 ≤ 0x710)
    (h : c + 4 ≤ d ∨ d + 4 ≤ c) :
    memLoad32 (memStore32 M (S + BitVec.ofNat 32 c) v) (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) :=
  memLoad32_store32_sep (sepS S h (by omega) (by omega))

/-- A store to one of the limb loop's counters keeps `GdBase`. -/
theorem GdBase.store {M : Word → BitVec 8} {S v : Word} {A c : Nat} (B : GdBase M S A) (h1 : 0x28 ≤ c)
    (h2 : c + 4 ≤ 0x3C) (h3 : c + 4 ≤ 0x30 ∨ 0x38 ≤ c) : GdBase (memStore32 M (S + BitVec.ofNat 32 c) v) S A := by
  refine ⟨?_, ?_, fun k hk => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [slot_word8 (by omega) (by decide) (.inl (by omega))]; exact B.N0
  · rw [← B.N]; exact accV_congr2 8 fun j hj => by rw [add_ofNat_assoc, slot_word8 (by omega) (by omega) (.inl (by omega))]
  · rw [← B.pw k hk]; exact accV_congr2 8 fun j hj => by
      rw [add_ofNat_assoc, slot_word8 (by omega) (by omega) (.inl (by omega))]
  · rw [slot_word8 (by omega) (by omega) (.inl (by omega))]; exact B.ex j hj
  · rw [slot_word8 (by omega) (by decide) (.inr (by omega))]; exact B.s1C
  · rw [slot_word8 (by omega) (by decide) (by rcases h3 with h | h; exact .inl (by omega); exact .inr (by omega))]; exact B.s34
  · rw [slot_word8 (by omega) (by decide) (by rcases h3 with h | h; exact .inl (by omega); exact .inr (by omega))]; exact B.s30
  · rw [slot_word8 (by omega) (by decide) (.inr (by omega))]; exact B.s24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The start of limb `i`**, from 0x2D4 with `s1 = i + 1` to the window
loop's head with eight windows to go: spill the counters for limb `i`. -/
theorem gd_lhead {M : Word → BitVec 8} {S : Word} {n : Machine} {i A : Nat} (C : GdCode M) (F : Fr S 0x710)
    (B : GdBase M S A) (s : St M GD n 0x2D4 (reg n)) (rsp : reg n sp = S)
    (r9 : reg n (9 : Fin 32) = BitVec.ofNat 32 (i + 1)) (hi : i < 8) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x2F0 (reg n') ∧ GdCode n'.mem ∧ GdBase n'.mem S A ∧ GdWin n'.mem S A i ∧
      reg n' a3 = 8 ∧ GdLoopFrame S n'.mem M ∧
      accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 = accV M (S + BitVec.ofNat 32 0x65C) 8 ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have al : ∀ c, c + 4 ≤ 0x710 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block gdH1 C.self gdH1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdH1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp]
    exact ⟨⟨al 0x2C (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩, al 0x1C (by decide) (by decide),
      al 0x34 (by decide) (by decide), al 0x38 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 M (S + BitVec.ofNat 32 0x2C) (BitVec.ofNat 32 (i + 1)))
      (S + BitVec.ofNat 32 0x38) (BitVec.ofNat 32 i) = M1 := ⟨_, rfl⟩
  have m1 : n1.mem = M1 := by
    rw [u1.mem, ← hM1]; simp +decide only [runBlock, BInstr.run, gdH1, upd, ↓reduceIte]; rw [rsp, r9,
      show aluEval .add (BitVec.ofNat 32 (i + 1)) 0xFFFFFFFF = BitVec.ofNat 32 i from lsucc_dec8 i hi]; rfl
  have r1 : ∀ q, reg n1 q = (runBlock gdH1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have B1 : GdBase M1 S A := by
    rw [← hM1]; exact (B.store (c := 0x2C) (by decide) (by decide) (.inl (by decide))).store (by decide) (by decide)
      (.inr (by decide))
  have e19 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 i := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gdH1, upd, ↓reduceIte]; rw [r9]; exact lsucc_dec8 i hi
  have e1a3 : reg n1 a3 = 8 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gdH1, upd, ↓reduceIte]; rw [rsp]
    show memLoad32 (memStore32 M (S + BitVec.ofNat 32 0x2C) _) (S + BitVec.ofNat 32 0x1C) = 8
    rw [slot_word8 (by decide) (by decide) (.inr (by decide))]; exact B.s1C
  have e1a0 : reg n1 a0 = 7 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, gdH1, upd, ↓reduceIte]; rw [rsp]
    show memLoad32 (memStore32 M (S + BitVec.ofNat 32 0x2C) _) (S + BitVec.ofNat 32 0x34) = 7
    rw [slot_word8 (by decide) (by decide) (.inl (by decide))]; exact B.s34
  have k1 : ∀ q, q ≠ a0 → q ≠ a3 → q ≠ (9 : Fin 32) → reg n1 q = reg n q := fun q h0 h3 h9 => by
    rw [r1, runBlock_reg _ _ _ q hz (by simp only [gdH1]; revert h0 h3 h9; revert q; decide)]
  have t1 : St M1 GD n1 0x2DE (reg n1) := ⟨u1.pc, m1, fun _ => rfl⟩
  have C1 : GdCode M1 := C.hi fun x hx => by
    rw [← hM1, memStore32_get_sep (F.hiOut (c := 0x38) (n := 4) (by decide) hx),
      memStore32_get_sep (F.hiOut (c := 0x2C) (n := 4) (by decide) hx)]
  -- eight windows either way
  obtain ⟨n2, c2, t2, e2a3, k2⟩ : ∃ n2, Steps n1 n2 ∧ St M1 GD n2 0x2E4 (reg n2) ∧ reg n2 a3 = 8 ∧
      ∀ q, q ≠ a3 → reg n2 q = reg n1 q := by
    by_cases h11 : i = 7
    · obtain ⟨n2, d2, u2⟩ := t1.taken C1.self 0x2E4 gd_at_2de (by decide) (by
        show (reg n1 (9 : Fin 32) == reg n1 a0) = true; rw [e19, e1a0, h11]; rfl)
      exact ⟨n2, .single d2, u2.self, by rw [u2.regs, e1a3], fun q _ => by rw [u2.regs]⟩
    · obtain ⟨n2, d2, u2⟩ := t1.notTaken C1.self 0x2E2 gd_at_2de (by decide) (by
        show (reg n1 (9 : Fin 32) == reg n1 a0) = false; rw [e19, e1a0]
        have : ∀ i : Nat, i < 8 → i ≠ 7 → (BitVec.ofNat 32 i == (7 : Word)) = false := by decide
        exact this i hi h11)
      obtain ⟨n3, d3, u3⟩ := u2.self.aluImm C1.self gd_at_2e2 (off' := 0x2E4) (by decide)
      exact ⟨n3, .cons d2 (.single d3), ⟨u3.pc, by rw [u3.mem], fun _ => rfl⟩,
        by rw [u3.regs]; simp +decide only [upd, ↓reduceIte]; rw [u2.self.zero]; rfl,
        fun q h => by rw [u3.regs, updz u2.self.zero h, u2.regs]⟩
  have sp2 : reg n2 sp = S := by rw [k2 sp (by decide), k1 sp (by decide) (by decide) (by decide)]; exact rsp
  obtain ⟨n3, c3, u3⟩ := t2.block gdH2 C1.self gdH2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdH2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp2]
    exact ⟨al 0x38 (by decide) (by decide), al 0x28 (by decide) (by decide), F.sepHi (by decide) (by decide) (by decide)⟩)
  have s38 : memLoad32 M1 (S + BitVec.ofNat 32 0x38) = BitVec.ofNat 32 i := by rw [← hM1, memLoad32_store32_same]
  have m3 : n3.mem = memStore32 M1 (S + BitVec.ofNat 32 0x28) (S + BitVec.ofNat 32 (0x41C + 4 * i)) := by
    rw [u3.mem]; simp +decide only [runBlock, BInstr.run, gdH2, upd, ↓reduceIte]; rw [sp2]
    show memStore32 M1 (S + BitVec.ofNat 32 0x28) (aluEval .add (aluEval .sll (memLoad32 M1 (S + BitVec.ofNat 32 0x38)) 2)
      (aluEval .add S 0x41C)) = _
    rw [s38, limb_addr8 F hi]
  refine ⟨n3, c1.trans (c2.trans c3), ⟨u3.pc, rfl, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun q h0 h1 h3 h9 => ?_⟩
  · exact C.hi fun x hx => by
      rw [m3, memStore32_get_sep (F.hiOut (c := 0x28) (n := 4) (by decide) hx), ← hM1,
        memStore32_get_sep (F.hiOut (c := 0x38) (n := 4) (by decide) hx),
        memStore32_get_sep (F.hiOut (c := 0x2C) (n := 4) (by decide) hx)]
  · rw [m3]; exact B1.store (by decide) (by decide) (.inl (by decide))
  · have B3 : GdBase n3.mem S A := by rw [m3]; exact B1.store (by decide) (by decide) (.inl (by decide))
    refine ⟨B3.N0, B3.N, B3.pw, B3.ex, ?_, B3.s34, ?_, B3.s30, B3.s24, ?_⟩
    · rw [m3, slot_word8 (by decide) (by decide) (.inl (by decide)), ← hM1, slot_word8 (by decide) (by decide) (.inr (by decide)),
        memLoad32_store32_same]
    · rw [m3, slot_word8 (by decide) (by decide) (.inl (by decide)), s38]
    · rw [m3, memLoad32_store32_same]
  · rw [u3.regs]; simp +decide only [runBlock, BInstr.run, gdH2, upd, ↓reduceIte]; exact e2a3
  · intro x hF h20 h62 h95
    have h28 : Sep (S + BitVec.ofNat 32 0x28) 4 x 1 := by
      have := h20.sub (c := 8) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
    have h2C : Sep (S + BitVec.ofNat 32 0x2C) 4 x 1 := by
      have := h20.sub (c := 0xC) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
    have h38 : Sep (S + BitVec.ofNat 32 0x38) 4 x 1 := by
      have := h20.sub (c := 0x18) (l := 4) (by decide); rwa [add_ofNat_assoc] at this
    rw [m3, memStore32_get_sep h28, ← hM1, memStore32_get_sep h38, memStore32_get_sep h2C]
  · exact accV_congr2 8 fun j hj => by
      rw [add_ofNat_assoc, m3, slot_word8 (by decide) (by omega) (.inl (by omega)), ← hM1,
        slot_word8 (by decide) (by omega) (.inl (by omega)), slot_word8 (by decide) (by omega) (.inl (by omega))]
  · rw [u3.regs, runBlock_reg _ _ _ q t2.zero (by simp only [gdH2]; revert h0 h1; revert q; decide), k2 q h3,
      k1 q h0 h3 h9]

theorem lim_ne08 : ∀ i : Nat, i < 8 → branchTaken .bne (BitVec.ofNat 32 i) 0 = decide (i ≠ 0) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The limb loop**, from the start of limb `i` at 0x2D4 to the loop's
exit at 0x536: `z` at `S + 0x65C` goes from `A^⌊e / 16^(8i + 8)⌋` to
`A^e` in Montgomery form, for the square-root exponent `e`. -/
theorem gd_limbs {S : Word} {A : Nat} (F : Fr S 0x710) :
    ∀ i, i < 8 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → GdBase M S A → GdRegs n S →
      St M GD n 0x2D4 (reg n) → reg n (9 : Fin 32) = BitVec.ofNat 32 (i + 1) →
      accV M (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (sqrtExp2 / 2 ^ (4 * (8 * i + 8))) →
      ∃ n', Steps n n' ∧ St n'.mem GD n' 0x536 (reg n') ∧ GdCode n'.mem ∧ GdBase n'.mem S A ∧ GdLoopFrame S n'.mem M ∧
        GdRegs n' S ∧ accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A sqrtExp2 ∧
        reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  intro i
  induction i with
  | zero => exact fun hi => step 0 hi (fun k h => absurd h.symm (Nat.succ_ne_zero k))
  | succ k ih => exact fun hi => step (k + 1) hi (fun k' h => by
      obtain rfl : k = k' := Nat.succ.inj h
      exact ih (by omega))
where
  step (i : Nat) (hi : i < 8)
      (ih : ∀ k, i = k + 1 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → GdBase M S A → GdRegs n S →
        St M GD n 0x2D4 (reg n) → reg n (9 : Fin 32) = BitVec.ofNat 32 (k + 1) →
        accV M (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (sqrtExp2 / 2 ^ (4 * (8 * k + 8))) →
        ∃ n', Steps n n' ∧ St n'.mem GD n' 0x536 (reg n') ∧ GdCode n'.mem ∧ GdBase n'.mem S A ∧ GdLoopFrame S n'.mem M ∧
          GdRegs n' S ∧ accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A sqrtExp2 ∧
          reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32))
      {M : Word → BitVec 8} {n : Machine} (C : GdCode M) (B : GdBase M S A) (R : GdRegs n S)
      (s : St M GD n 0x2D4 (reg n)) (r9 : reg n (9 : Fin 32) = BitVec.ofNat 32 (i + 1))
      (hz : accV M (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A (sqrtExp2 / 2 ^ (4 * (8 * i + 8)))) :
      ∃ n', Steps n n' ∧ St n'.mem GD n' 0x536 (reg n') ∧ GdCode n'.mem ∧ GdBase n'.mem S A ∧ GdLoopFrame S n'.mem M ∧
        GdRegs n' S ∧ accV n'.mem (S + BitVec.ofNat 32 0x65C) 8 = mpow2 A sqrtExp2 ∧
        reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
    have hSl := F.lo; have hSh := F.hi; have hSa := F.al
    obtain ⟨n1, c1, u1, C1, B1, W1, a31, fr1, hz1, k1⟩ := gd_lhead C F B s R.sp r9 hi
    have kk1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 21, 22, 25, 27] → reg n1 q = reg n q := fun q hq =>
      k1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide)
    have R1 : GdRegs n1 S := ⟨by rw [kk1 sp (by decide)]; exact R.sp,
      by rw [kk1 27 (by decide)]; exact R.r27, by rw [kk1 18 (by decide)]; exact R.r18, by rw [kk1 22 (by decide)]; exact R.r22,
      by rw [kk1 21 (by decide)]; exact R.r21, by rw [kk1 25 (by decide)]; exact R.r25, by rw [kk1 19 (by decide)]; exact R.r19⟩
    obtain ⟨n2, c2, u2, C2, fr2, R2, a32, hz2, g32, g42⟩ := gd_windows F hi 8 (Nat.le_refl 8) C1 W1 R1 u1 a31
      (by rw [hz1, hz])
    have W2 := W1.frame F fr2
    have B2 := B1.frame F fr2
    -- the end of the limb
    obtain ⟨n3, d3, u3⟩ := u2.taken C2.self 0x530 gd_at_2f0 (by decide) (by
      show (reg n2 a3 == reg n2 x0) = true; rw [a32, u2.zero]; rfl)
    obtain ⟨n4, d4, u4⟩ := u3.self.lw C2.self gd_at_530 (off' := 0x532) (by decide)
      (by rw [u3.regs, R2.sp]; show (S + BitVec.ofNat 32 0x38).toNat % 4 = 0; rw [F.at _ (by decide)]; omega)
    have e49 : reg n4 (9 : Fin 32) = BitVec.ofNat 32 i := by
      rw [u4.regs]; simp +decide only [upd, ↓reduceIte]; rw [u3.regs, R2.sp]; exact W2.s38
    have g4 : ∀ q, q ≠ (9 : Fin 32) → reg n4 q = reg n2 q := fun q h => by rw [u4.regs, updz u3.self.zero h, u3.regs]
    have R4 : GdRegs n4 S := ⟨by rw [g4 sp (by decide)]; exact R2.sp,
      by rw [g4 27 (by decide)]; exact R2.r27, by rw [g4 18 (by decide)]; exact R2.r18, by rw [g4 22 (by decide)]; exact R2.r22,
      by rw [g4 21 (by decide)]; exact R2.r21, by rw [g4 25 (by decide)]; exact R2.r25, by rw [g4 19 (by decide)]; exact R2.r19⟩
    have m4 : n4.mem = n2.mem := u4.mem
    have fr12 : GdLoopFrame S n2.mem M := fr1.trans fr2.loop
    have hb := lim_ne08 i hi
    rw [← e49, ← u4.self.zero] at hb
    by_cases h0 : i = 0
    · obtain ⟨n5, d5, u5⟩ := u4.self.notTaken C2.self 0x536 gd_at_532 (by decide) (by rw [hb]; exact decide_eq_false (fun h => h h0))
      subst h0
      refine ⟨n5, c1.trans (c2.trans (.cons d3 (.cons d4 (.single d5)))), ⟨u5.pc, by rw [u5.mem], fun _ => rfl⟩,
        by rw [u5.mem]; exact C2, by rw [u5.mem]; exact B2, by rw [u5.mem]; exact fr12,
        ⟨by rw [u5.regs]; exact R4.sp, by rw [u5.regs]; exact R4.r27,
          by rw [u5.regs]; exact R4.r18, by rw [u5.regs]; exact R4.r22, by rw [u5.regs]; exact R4.r21,
          by rw [u5.regs]; exact R4.r25, by rw [u5.regs]; exact R4.r19⟩, by rw [u5.mem, hz2]; rfl, ?_, ?_⟩
      · rw [u5.regs, g4 3 (by decide), g32, kk1 3 (by decide)]
      · rw [u5.regs, g4 4 (by decide), g42, kk1 4 (by decide)]
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      obtain ⟨n5, d5, u5⟩ := u4.self.taken C2.self 0x2D4 gd_at_532 (by decide) (by rw [hb]; exact decide_eq_true h0)
      have R5 : GdRegs n5 S := ⟨by rw [u5.regs]; exact R4.sp, by rw [u5.regs]; exact R4.r27,
        by rw [u5.regs]; exact R4.r18, by rw [u5.regs]; exact R4.r22, by rw [u5.regs]; exact R4.r21,
        by rw [u5.regs]; exact R4.r25, by rw [u5.regs]; exact R4.r19⟩
      obtain ⟨n6, c6, u6, C6, B6, fr6, R6, hz6, g36, g46⟩ := ih k rfl C2 B2 R5
        ⟨u5.pc, by rw [u5.mem], fun _ => rfl⟩ (by rw [u5.regs, e49])
        (by rw [hz2, show 8 * (k + 1) = 8 * k + 8 by omega])
      refine ⟨n6, c1.trans (c2.trans (.cons d3 (.cons d4 (.cons d5 c6)))), u6, C6, B6, fr12.trans fr6, R6, hz6, ?_, ?_⟩
      · rw [g36, u5.regs, g4 3 (by decide), g32, kk1 3 (by decide)]
      · rw [g46, u5.regs, g4 4 (by decide), g42, kk1 4 (by decide)]


end C3.RV32.Gd
