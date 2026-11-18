import C3BootProofs.Proofs.Dec384Main

/-!
# P-384 point decompression: after the exponentiation

From the end of the exponentiation at 0x5A0 to `decompress`'s return: check
that `β = α^((p + 1) / 4)` squares to `α`, pick `y = ±β` by the parity it
should have, and write the point.
-/

namespace C3.RV32.Dq

open C3.Image

set_option maxRecDepth 20000

/-- `α^((p + 1) / 4)` in Montgomery form: a square root of `α` when one exists. -/
def dqSqrt (A : Nat) : Nat := mpow A sqrtExp

/-- The square root `decompress` keeps: `β` when it squares to `α`, else 0. -/
def dqY0 (A : Nat) : Nat := if p3fm (dqSqrt A) (dqSqrt A) = A then dqSqrt A else 0

/-- What `ConstMontyForm::neg` computes. -/
def dqNeg (y : Nat) : Nat := if y = 0 then 0 else (p384 + 2 ^ 384 - y) % 2 ^ 384

/-- The `y` `decompress` returns for `α` and the requested parity: `y₀` when
its value is odd exactly when `yodd` is, else `-y₀`. -/
def dqY (A : Nat) (yodd : Word) : Nat :=
  if p3fm (dqY0 A) 1 % 2 = yodd.toNat % 2 then dqY0 A else dqNeg (dqY0 A)

theorem accV_words {M M' : Word → BitVec 8} {b b' : Word} :
    ∀ n, accV M b n = accV M' b' n → ∀ i, i < n →
      memLoad32 M (b + BitVec.ofNat 32 (4 * i)) = memLoad32 M' (b' + BitVec.ofNat 32 (4 * i))
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    rw [accV_succ1, accV_succ1] at h
    have l1 := accV_lt M b n; have l2 := accV_lt M' b' n
    have hm : accV M b n = accV M' b' n := by
      have := congrArg (· % 2 ^ (32 * n)) h
      simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this
      exact this
    by_cases hin : i < n
    · exact accV_words n hm i hin
    · obtain rfl : i = n := by omega
      apply BitVec.eq_of_toNat_eq
      have := congrArg (· / 2 ^ (32 * i)) h
      rwa [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt l1, Nat.div_eq_of_lt l2, Nat.zero_add, Nat.zero_add] at this

theorem eq12_iff {M : Word → BitVec 8} {p q : Word} :
    (∀ i : Nat, i < 12 → memLoad32 M (p + BitVec.ofNat 32 (4 * i)) = memLoad32 M (q + BitVec.ofNat 32 (4 * i))) ↔
      accV M p 12 = accV M q 12 :=
  ⟨fun h => (accV_congr2 12 fun i hi => (h i hi).symm).symm, fun h => accV_words 12 h⟩

def dqG1 : List BInstr := [.aluImm .add a0 sp 0x1D0, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x15D, .aluImm .add a2 x0 0x30]
def dqG2 : List BInstr := [.lw (19 : Fin 32) sp 0x18, .lw (20 : Fin 32) sp 0x14, .lw (21 : Fin 32) sp 0x10]
def dqG3 : List BInstr :=
  [.aluImm .add (8 : Fin 32) sp 0x200, .lui (9 : Fin 32) 0x3FCC5000, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFC8C,
   .aluImm .add a2 x0 0x9C, .alu .add a0 x0 (8 : Fin 32), .alu .add a1 x0 (9 : Fin 32)]
def dqG4 : List BInstr :=
  [.lw a0 sp 0x290, .alu .sub a3 x0 a0, .aluImm .add a0 sp 0x62C, .aluImm .add a1 sp 0x1D0, .alu .add a2 x0 (8 : Fin 32)]
def dqG5 : List BInstr := [.aluImm .add a0 sp 0x65C, .aluImm .add a2 x0 0x9C, .alu .add a1 x0 (9 : Fin 32)]
def dqG6 : List BInstr := [.aluImm .add a0 sp 0x62C, .aluImm .add a1 sp 0x104]
def dqG7 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0x62C, .aluImm .add a1 sp 0x1D0, .aluImm .add a2 x0 0x30]

theorem dqG1_end : blockEnd p384DecompressCode 0x5A0 dqG1 = some 0x5AE := by decide
theorem dqG2_end : blockEnd p384DecompressCode 0x5B6 dqG2 = some 0x5BC := by decide
theorem dqG3_end : blockEnd p384DecompressCode 0x5BC dqG3 = some 0x5CE := by decide
theorem dqG4_end : blockEnd p384DecompressCode 0x5D6 dqG4 = some 0x5E6 := by decide
theorem dqG5_end : blockEnd p384DecompressCode 0x5EE dqG5 = some 0x5F8 := by decide
theorem dqG6_end : blockEnd p384DecompressCode 0x600 dqG6 = some 0x606 := by decide
theorem dqG7_end : blockEnd p384DecompressCode 0x61A dqG7 = some 0x626 := by decide

def dqG6b : List BInstr := [.aluImm .and a0 a0 0xFF]
theorem dqG6b_end : blockEnd p384DecompressCode 0x60E dqG6b = some 0x612 := by decide

theorem params_zero : ∀ k, k < 3 → byteAt p384ParamsData (0x31 + k) = 0 := by decide

theorem params_k : wordAt p384ParamsData 0x90 0 = 0xFFFFFFFF := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Checking the square root**, from 0x5A0 to 0x62E: square `β`, compare
the square with `α`, and keep the answer in `s0` and `β` at `S + 0x62C`. -/
theorem dq_stG {M : Word → BitVec 8} {n : Machine} {S : Word} {A B : Nat} (C : DqCode M) (D : DqData M)
    (F : DqFrame S) (s : St M DP n 0x5A0 (reg n)) (R : DqRegs n S)
    (hB : accV M (S + BitVec.ofNat 32 0x95C) 12 = B) (hBp : B < p384) (hA : accV M (S + BitVec.ofNat 32 0x104) 12 = A) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x62E (reg n') ∧ DqCode n'.mem ∧ DqData n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x62C) 12 = B ∧
      reg n' (8 : Fin 32) = (if p3fm B B = A then 1 else 0) ∧
      reg n' (19 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x18) ∧
      reg n' (20 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x14) ∧
      reg n' (21 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x10) ∧ reg n' sp = S ∧
      (∀ k, k < 3 → n'.mem (S + BitVec.ofNat 32 (0x68D + k)) = BitVec.ofNat 8 0) ∧
      (∀ x, Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep (S + BitVec.ofNat 32 0x1D0) 0xCC x 1 →
        Sep (S + BitVec.ofNat 32 0x62C) 0xCC x 1 → n'.mem x = M x) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC, b16⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16b : ∀ d, d + 1 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have l16 : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0xBF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have below : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have sq : ∀ c l d, c + l ≤ 0xA50 → d + 1 ≤ 0xA50 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have al : ∀ c, c + 4 ≤ 0xA50 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  -- copy β, and reload the spilled registers
  obtain ⟨n1, c1, u1⟩ := s.block dqG1 C.self dqG1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock dqG1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, fr2, k2⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x1D0) (src := S + BitVec.ofNat 32 0x95C)
    (S := S) (N := 48) (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M DP n1 0x5AE (reg n1)) C dp_at_5ae dp_at_5b2 (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact R.sp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqG1, upd, ↓reduceIte]; rw [R.sp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqG1, upd, ↓reduceIte]; rw [R.sp, spo]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqG1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    ⟨C.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr2' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x1D0) 48 x 1 → n2.mem x = M x :=
    fun x a b => by rw [fr2 x a, copyBytes_sep b (Nat.le_refl _)]
  have C2 := C.hi fun x hx => fr2' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D2 : DqData n2.mem := D.of F fun x hx => fr2' x (below hb16 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have k2' := kc k2
  have sp2 : reg n2 sp = S := by rw [k2' sp (by decide), r1, runBlock_reg _ _ _ sp hz (by decide)]; exact R.sp
  have hB2 : accV n2.mem (S + BitVec.ofNat 32 0x1D0) 12 = B := by
    rw [← hB]; exact cp_accV (by decide) (by decide) fun i hi => by
      rw [load_frame fr2 (l16 _ (by omega)), ← add_ofNat_assoc S 0x1D0, cp_word (by omega) (by decide), add_ofNat_assoc]
  have ld2 : ∀ d, d + 4 ≤ 0xA50 → (d + 4 ≤ 0x1D0 ∨ 0x200 ≤ d) →
      memLoad32 n2.mem (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := fun d h1 h2 =>
    ld_keep fun q hq => fr2' _ (l16b _ (by omega))
      (sq _ _ _ (by decide) (by omega) (by rcases h2 with h | h; exact .inr (by omega); exact .inl (by omega)))
  obtain ⟨n3, c3, u3⟩ := u2.block dqG2 C2.self dqG2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqG2]; simp +decide only [upd, ↓reduceIte, and_true]
    rw [sp2]; exact ⟨al 0x18 (by decide) (by decide), al 0x14 (by decide) (by decide), al 0x10 (by decide) (by decide)⟩)
  have r3 : ∀ q, reg n3 q = (runBlock dqG2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have e319 : reg n3 (19 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x18) := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, dqG2, upd, ↓reduceIte]; rw [sp2]
    show memLoad32 n2.mem (S + BitVec.ofNat 32 0x18) = _; exact ld2 0x18 (by decide) (.inl (by decide))
  have e320 : reg n3 (20 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x14) := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, dqG2, upd, ↓reduceIte]; rw [sp2]
    show memLoad32 n2.mem (S + BitVec.ofNat 32 0x14) = _; exact ld2 0x14 (by decide) (.inl (by decide))
  have e321 : reg n3 (21 : Fin 32) = memLoad32 M (S + BitVec.ofNat 32 0x10) := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, dqG2, upd, ↓reduceIte]; rw [sp2]
    show memLoad32 n2.mem (S + BitVec.ofNat 32 0x10) = _; exact ld2 0x10 (by decide) (.inl (by decide))
  have t3 : St n2.mem DP n3 0x5BC (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have sp3 : reg n3 sp = S := by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2
  have K3 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n q := fun q hq => by
    rw [r3, runBlock_reg _ _ _ q u2.zero (by simp only [dqG2]; revert hq; revert q; decide), k2' q (by revert hq; revert q; decide),
      r1, runBlock_reg _ _ _ q hz (by simp only [dqG1]; revert hq; revert q; decide)]
  -- copy the parameters to `S + 0x200`
  obtain ⟨n4, c4, u4⟩ := t3.block dqG3 C2.self dqG3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock dqG3 (n2.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have e49 : reg n4 (9 : Fin 32) = PARAMS := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, dqG3, upd, ↓reduceIte]; (try rw [t3.zero]); try rfl
  obtain ⟨n5, c5, u5, fr5, k5⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x200) (src := PARAMS) (S := S) (N := 0x9C)
    (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n2.mem DP n4 0x5CE (reg n4)) C2 dp_at_5ce dp_at_5d2 (by decide) (by decide)
    (by rw [r4, runBlock_reg _ _ _ sp t3.zero (by decide)]; exact sp3)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqG3, upd, ↓reduceIte]; rw [sp3]
        exact BitVec.zero_add _)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqG3, upd, ↓reduceIte]; (try rw [t3.zero]); (try rw [BitVec.zero_add]); try rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqG3, upd, ↓reduceIte]; (try rw [t3.zero]); try rfl)
    ⟨C2.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr5' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x200) 0x9C x 1 → n5.mem x = n2.mem x :=
    fun x a b => by rw [fr5 x a, copyBytes_sep b (Nat.le_refl _)]
  have C5 := C2.hi fun x hx => fr5' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D5 : DqData n5.mem := D2.of F fun x hx => fr5' x (below hb16 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have hP5 : ∀ k, k + 4 ≤ 0x9C → memLoad32 n5.mem (S + BitVec.ofNat 32 (0x200 + k)) =
      memLoad32 n2.mem (PARAMS + BitVec.ofNat 32 k) := fun k hk => by
    rw [load_frame fr5 (l16 _ (by omega)), ← add_ofNat_assoc S 0x200, cp_word (by omega) (by decide)]
  have hN0 : memLoad32 n5.mem (S + BitVec.ofNat 32 0x200) = 0xFFFFFFFF :=
    (hP5 0 (by decide)).trans ((code_word D2.params 0 0 (by decide)).trans params_n0)
  have hN : accV n5.mem (S + BitVec.ofNat 32 0x200) 12 = p384 := by
    rw [← params_N, ← code_accV D2.params 0 12 (by decide)]
    exact accV_congr2 12 fun i hi => by rw [add_ofNat_assoc, hP5 (4 * i) (by omega), add_ofNat_zero]; try rfl
  have hK : memLoad32 n5.mem (S + BitVec.ofNat 32 0x290) = 0xFFFFFFFF :=
    (hP5 0x90 (by decide)).trans ((code_word D2.params 0x90 0 (by decide)).trans params_k)
  have k5' := kc k5
  have sp5 : reg n5 sp = S := by rw [k5' sp (by decide), r4, runBlock_reg _ _ _ sp t3.zero (by decide)]; exact sp3
  have K5 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n3 q := fun q hq => by
    rw [k5' q (by revert hq; revert q; decide), r4, runBlock_reg _ _ _ q t3.zero (by simp only [dqG3]; revert hq; revert q; decide)]
  have e59 : reg n5 (9 : Fin 32) = PARAMS := by rw [k5' 9 (by decide), e49]
  -- square `β`
  obtain ⟨n6, c6, u6⟩ := u5.block dqG4 C5.self dqG4_end (by
    simp only [BlockOk, BInstr.ok, dqG4]; simp +decide only [↓reduceIte, and_true]
    rw [sp5]; exact al 0x290 (by decide) (by decide))
  have r6 : ∀ q, reg n6 q = (runBlock dqG4 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have hB5 : accV n5.mem (S + BitVec.ofNat 32 0x1D0) 12 = B := by
    rw [← hB2]; exact accV_keep fun q hq => fr5' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  obtain ⟨n7, c7, u7, e7, fr7, sp7, k7⟩ := dq_sqm (out := S + BitVec.ofNat 32 0x62C) (xp := S + BitVec.ofNat 32 0x1D0)
    (np := S + BitVec.ofNat 32 0x200) (co := 0x62C) (cx := 0x1D0) (cn := 0x200)
    (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St n5.mem DP n6 0x5E6 (reg n6)) C5 F dp_at_5e6 dp_at_5ea (by decide) (by decide)
    (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqG4, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqG4, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqG4, upd, ↓reduceIte]; rw [k5' 8 (by decide), r4]
        simp +decide only [runBlock, BInstr.run, dqG3, upd, ↓reduceIte]; rw [sp3]
        exact BitVec.zero_add _)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqG4, upd, ↓reduceIte]; rw [sp5]
        show reg n5 x0 - memLoad32 n5.mem (S + BitVec.ofNat 32 0x290) = 1
        rw [u5.zero, hK]; rfl)
    (by decide) (by decide) (by decide) rfl rfl rfl (by decide) (by decide) (by decide) hN0 hN (by rw [hB5]; exact hBp)
  have K7 : ∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n7 q = reg n5 q := fun q hq => by
    rw [k7 q (by revert hq; revert q; decide), r6, runBlock_reg _ _ _ q u5.zero (by simp only [dqG4]; revert hq; revert q; decide)]
  have hb4 : (S + 0xFFFFFFFC).toNat = S.toNat - 4 := F.below 4 (by decide) (by decide)
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have loK : ∀ {k : Nat} {B' : Word}, B'.toNat = S.toNat - k → k ≤ 0x1A0 → ∀ x : Word, 0x40000000 ≤ x.toNat →
      Sep B' k x 1 := fun {k B'} hB' hk x hx => sep_of_le (by rw [hB']; omega) (by have := x.isLt; omega)
  have lowSub : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0xF0 →
      Sep (S + 0xFFFFFF10) 0xF0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have := hx.sub (c := 0xF0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFF10 + BitVec.ofNat 32 (0xF0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbF, hB']; omega] at this
  have C7 := C5.hi fun x hx => fr7 x (loK hbF (by decide) x hx) (F.hiOut (by decide) hx)
  have D7 : DqData n7.mem := D5.of F fun x hx => fr7 x (below hbF (by decide) (by decide) hx) (inFrame (by decide) hx)
  -- copy the parameters to `S + 0x65C`
  obtain ⟨n8, c8, u8⟩ := u7.block dqG5 C7.self dqG5_end ⟨trivial, trivial, trivial, trivial⟩
  have r8 : ∀ q, reg n8 q = (runBlock dqG5 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  obtain ⟨n9, c9, u9, fr9, k9⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x65C) (src := PARAMS) (S := S) (N := 0x9C)
    (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St n7.mem DP n8 0x5F8 (reg n8)) C7 dp_at_5f8 dp_at_5fc (by decide) (by decide)
    (by rw [r8, runBlock_reg _ _ _ sp u7.zero (by decide)]; exact sp7)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, dqG5, upd, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, dqG5, upd, ↓reduceIte]; rw [K7 9 (by decide), e59]
        exact BitVec.zero_add _)
    (by rw [r8]; simp +decide only [runBlock, BInstr.run, dqG5, upd, ↓reduceIte]; (try rw [u7.zero]); try rfl)
    ⟨C7.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide),
      (F.lowData (c := 16) (by decide) rfl (by decide) (by decide)).symm, F.bufData (by decide) (by decide) (by decide),
      fA, fW, by rw [F.at _ (by decide)]; omega, by decide⟩
  have fr9' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x65C) 0x9C x 1 → n9.mem x = n7.mem x :=
    fun x a b => by rw [fr9 x a, copyBytes_sep b (Nat.le_refl _)]
  have C9 := C7.hi fun x hx => fr9' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D9 : DqData n9.mem := D7.of F fun x hx => fr9' x (below hb16 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have hZ9 : ∀ k, k < 3 → n9.mem (S + BitVec.ofNat 32 (0x68D + k)) = BitVec.ofNat 8 0 := fun k hk => by
    rw [fr9 _ (l16b _ (by omega)), show 0x68D + k = 0x65C + (0x31 + k) by omega, ← add_ofNat_assoc S 0x65C,
      cp_at (by omega) (by decide), D7.params (0x31 + k) (by have : p384ParamsData.length = 156 := rfl; omega)]
    exact params_zero k hk
  have k9' := kc k9
  have sp9 : reg n9 sp = S := by rw [k9' sp (by decide), r8, runBlock_reg _ _ _ sp u7.zero (by decide)]; exact sp7
  -- compare the square with `α`
  obtain ⟨n10, c10, u10⟩ := u9.block dqG6 C9.self dqG6_end ⟨trivial, trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock dqG6 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  obtain ⟨n11, c11, u11, e11, fr11, k11⟩ := dq_eq12 (p := S + BitVec.ofNat 32 0x62C) (q := S + BitVec.ofNat 32 0x104)
    (⟨u10.pc, u10.mem, fun _ => rfl⟩ : St n9.mem DP n10 0x606 (reg n10)) C9 F dp_at_606 dp_at_60a (by decide) (by decide)
    (by rw [r10, runBlock_reg _ _ _ sp u9.zero (by decide)]; exact sp9)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, dqG6, upd, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, dqG6, upd, ↓reduceIte]; rw [sp9]; rfl)
    (al 0x62C (by decide) (by decide)) (al 0x104 (by decide) (by decide))
  have C11 := C9.hi fun x hx => fr11 x (loK hb4 (by decide) x hx)
  have D11 : DqData n11.mem := D9.of F fun x hx => fr11 x (below hb4 (by decide) (by decide) hx)
  obtain ⟨n12, c12, u12⟩ := u11.block dqG6b C11.self dqG6b_end ⟨trivial, trivial⟩
  have r12 : ∀ q, reg n12 q = (runBlock dqG6b (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  have sp12 : reg n12 sp = S := by
    rw [r12, runBlock_reg _ _ _ sp u11.zero (by decide), k11 sp (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), r10, runBlock_reg _ _ _ sp u9.zero (by decide)]; exact sp9
  obtain ⟨n13, c13, u13, e13, fr13, k13⟩ := dq_bb
    (⟨u12.pc, u12.mem, fun _ => rfl⟩ : St n11.mem DP n12 0x612 (reg n12)) C11 F dp_at_612 dp_at_616 (by decide) (by decide) sp12
  have C13 := C11.hi fun x hx => fr13 x (loK hb1 (by decide) x hx)
  have D13 : DqData n13.mem := D11.of F fun x hx => fr13 x (below hb1 (by decide) (by decide) hx)
  -- keep the answer, and copy `β` to `S + 0x62C`
  obtain ⟨n14, c14, u14⟩ := u13.block dqG7 C13.self dqG7_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r14 : ∀ q, reg n14 q = (runBlock dqG7 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
  have sp13 : reg n13 sp = S := by rw [k13 sp (by decide) (by decide)]; exact sp12
  obtain ⟨n15, c15, u15, fr15, k15⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x62C) (src := S + BitVec.ofNat 32 0x1D0)
    (S := S) (N := 48) (⟨u14.pc, u14.mem, fun _ => rfl⟩ : St n13.mem DP n14 0x626 (reg n14)) C13 dp_at_626 dp_at_62a
    (by decide) (by decide) (by rw [r14, runBlock_reg _ _ _ sp u13.zero (by decide)]; exact sp13)
    (by rw [r14]; simp +decide only [runBlock, BInstr.run, dqG7, upd, ↓reduceIte]; rw [sp13]; rfl)
    (by rw [r14]; simp +decide only [runBlock, BInstr.run, dqG7, upd, ↓reduceIte]; rw [sp13]; rfl)
    (by rw [r14]; simp +decide only [runBlock, BInstr.run, dqG7, upd, ↓reduceIte]; (try rw [u13.zero]); try rfl)
    ⟨C13.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr15' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 → n15.mem x = n13.mem x :=
    fun x a b => by rw [fr15 x a, copyBytes_sep b (Nat.le_refl _)]
  have C15 := C13.hi fun x hx => fr15' x (lo16 x hx) (F.hiOut (by decide) hx)
  have D15 : DqData n15.mem := D13.of F fun x hx => fr15' x (below hb16 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have k15' := kc k15
  -- the values
  have back : ∀ d, d + 1 ≤ 0xA50 → (d + 1 ≤ 0x62C ∨ 0x65C ≤ d) → (d + 1 ≤ 0x65C ∨ 0x6F8 ≤ d) →
      n13.mem (S + BitVec.ofNat 32 d) = n7.mem (S + BitVec.ofNat 32 d) := fun d h1 h2 h3 => by
    rw [fr13 _ (F.lowB hb1 (by decide) h1), fr11 _ (F.lowB hb4 (by decide) h1), fr9' _ (l16b _ h1)
      (sq _ _ _ (by decide) h1 (by rcases h3 with h | h; exact .inr h; exact .inl (by omega)))]
  have hB13 : accV n13.mem (S + BitVec.ofNat 32 0x1D0) 12 = B := by
    rw [← hB5]; exact accV_keep fun q hq => by
      rw [back _ (by omega) (.inl (by omega)) (.inl (by omega)), fr7 _ (F.lowB hbF (by decide) (by omega))
        (sq _ _ _ (by decide) (by omega) (.inr (by omega)))]
  have hSq : accV n9.mem (S + BitVec.ofNat 32 0x62C) 12 = p3fm B B := by
    rw [← hB5, ← e7]; exact accV_keep fun q hq => fr9' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  have hA9 : accV n9.mem (S + BitVec.ofNat 32 0x104) 12 = A := by
    rw [← hA]; exact accV_keep fun q hq => by
      rw [fr9' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega))),
        fr7 _ (F.lowB hbF (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega))),
        fr5' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega))),
        fr2' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))]
  have hc : (∀ i : Nat, i < 12 → memLoad32 n9.mem (S + BitVec.ofNat 32 0x62C + BitVec.ofNat 32 (4 * i)) =
      memLoad32 n9.mem (S + BitVec.ofNat 32 0x104 + BitVec.ofNat 32 (4 * i))) ↔ p3fm B B = A := by
    rw [eq12_iff, hSq, hA9]
  have a12 : reg n12 a0 = aluEval .and (reg n11 a0) 0xFF := by
    rw [r12]; simp +decide only [runBlock, BInstr.run, dqG6b, upd, ↓reduceIte]
  have a14 : reg n14 (8 : Fin 32) = reg n13 a0 := by
    rw [r14]; simp +decide only [runBlock, BInstr.run, dqG7, upd, ↓reduceIte]; exact BitVec.zero_add _
  have KK : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 19, 20, 21] → reg n15 q = reg n7 q := fun q hq => by
    rw [k15' q (by revert hq; revert q; decide), r14, runBlock_reg _ _ _ q u13.zero (by simp only [dqG7]; revert hq; revert q; decide),
      k13 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r12,
      runBlock_reg _ _ _ q u11.zero (by simp only [dqG6b]; revert hq; revert q; decide),
      k11 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r10,
      runBlock_reg _ _ _ q u9.zero (by simp only [dqG6]; revert hq; revert q; decide),
      kc k9 q (by revert hq; revert q; decide), r8, runBlock_reg _ _ _ q u7.zero (by simp only [dqG5]; revert hq; revert q; decide)]
  refine ⟨n15, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans (c14.trans c15))))))))))))), u15, C15, D15, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hB13]; exact cp_accV (by decide) (by decide) fun i hi => by
      rw [load_frame fr15 (l16 _ (by omega)), ← add_ofNat_assoc S 0x62C, cp_word (by omega) (by decide), add_ofNat_assoc]
  · rw [k15' 8 (by decide), a14, e13, a12, e11]
    by_cases h : p3fm B B = A
    · rw [ite_eq_left (hc.2 h), ite_eq_left h]; rfl
    · rw [ite_eq_right (fun h' => h (hc.1 h')), ite_eq_right h]; rfl
  · rw [KK 19 (by decide), K7 19 (by decide), K5 19 (by decide), e319]
  · rw [KK 20 (by decide), K7 20 (by decide), K5 20 (by decide), e320]
  · rw [KK 21 (by decide), K7 21 (by decide), K5 21 (by decide), e321]
  · rw [KK sp (by decide)]; exact sp7
  · intro k hk
    rw [fr15' _ (l16b _ (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega))),
      fr13 _ (F.lowB hb1 (by decide) (by omega)), fr11 _ (F.lowB hb4 (by decide) (by omega))]
    exact hZ9 k hk
  · intro x hx h1D0 h62C
    have hA48 : Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 := by
      have := h62C.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
    have hA9C : Sep (S + BitVec.ofNat 32 0x65C) 0x9C x 1 := by
      have := h62C.sub (c := 0x30) (l := 0x9C) (by decide); rwa [add_ofNat_assoc] at this
    have hB48 : Sep (S + BitVec.ofNat 32 0x1D0) 48 x 1 := by
      have := h1D0.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
    have hB9C : Sep (S + BitVec.ofNat 32 0x200) 0x9C x 1 := by
      have := h1D0.sub (c := 0x30) (l := 0x9C) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr15' x (lowSub hb16 (by decide) (by decide) hx) hA48, fr13 x (lowSub hb1 (by decide) (by decide) hx),
      fr11 x (lowSub hb4 (by decide) (by decide) hx), fr9' x (lowSub hb16 (by decide) (by decide) hx) hA9C, fr7 x hx hA48,
      fr5' x (lowSub hb16 (by decide) (by decide) hx) hB9C, fr2' x (lowSub hb16 (by decide) (by decide) hx) hB48]
  · rw [KK 3 (by decide), K7 3 (by decide), K5 3 (by decide), K3 3 (by decide)]
  · rw [KK 4 (by decide), K7 4 (by decide), K5 4 (by decide), K3 4 (by decide)]

/-! ## Choosing the root -/

def dqK0 : List BInstr := [.sb sp (8 : Fin 32) 0x65C, .aluImm .add a0 sp 0x2FC, .aluImm .add a1 sp 0x62C]
def dqK1 : List BInstr := [.aluImm .add a0 sp 0x29C, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0]
def dqK2 : List BInstr :=
  [.lbu (8 : Fin 32) sp 0x32C, .aluImm .add a0 sp 0xD4, .aluImm .add a1 sp 0x29C, .aluImm .add a2 sp 0x2FC,
   .alu .add a3 x0 (8 : Fin 32)]
def dqK3 : List BInstr := [.aluImm .add a0 sp 0x104, .aluImm .add a1 sp 0xD4]
def dqK4 : List BInstr := [.aluImm .add a0 sp 0x62C, .aluImm .add a1 sp 0xD4]
def dqK5 : List BInstr := [.lw a0 sp 0x62C, .aluImm .and a0 a0 0x1]
def dqK6 : List BInstr := [.alu .add a1 x0 (21 : Fin 32)]

theorem dqK0_end : blockEnd p384DecompressCode 0x62E dqK0 = some 0x638 := by decide
theorem dqK1_end : blockEnd p384DecompressCode 0x640 dqK1 = some 0x648 := by decide
theorem dqK2_end : blockEnd p384DecompressCode 0x650 dqK2 = some 0x65C := by decide
theorem dqK3_end : blockEnd p384DecompressCode 0x664 dqK3 = some 0x668 := by decide
theorem dqK4_end : blockEnd p384DecompressCode 0x670 dqK4 = some 0x676 := by decide
theorem dqK5_end : blockEnd p384DecompressCode 0x67E dqK5 = some 0x684 := by decide
theorem dqK6_end : blockEnd p384DecompressCode 0x68C dqK6 = some 0x68E := by decide

theorem dq_st8 {M : Word → BitVec 8} {a x : Word} {v : BitVec 8} (h : Sep a 1 x 1) : memStore8 M a v x = M x :=
  memStore8_ne fun e => h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])

theorem xor_mod2 (x y : Nat) : (x ^^^ y) % 2 = (x % 2 + y % 2) % 2 := by
  have h := Nat.testBit_xor x y 0
  rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at h
  revert h; rcases Nat.mod_two_eq_zero_or_one x with h1 | h1 <;> rcases Nat.mod_two_eq_zero_or_one y with h2 | h2 <;>
    rcases Nat.mod_two_eq_zero_or_one (x ^^^ y) with h3 | h3 <;> simp [h1, h2, h3]

/-- The parity test `decompress` runs: bit 0 of `w` against bit 0 of `b`. -/
theorem par_iff (w b : Word) :
    ((((w &&& 1).extractLsb' 0 8).zeroExtend 32 ^^^ b) &&& 1 = 0) ↔ w.toNat % 2 = b.toNat % 2 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    BitVec.toNat_and, show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.and_one_is_mod, xor_mod2,
    Nat.shiftRight_zero, show (0 : Word).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

theorem accV_low {M : Word → BitVec 8} {b : Word} : ∀ n, accV M b (n + 1) % 2 ^ 32 = (memLoad32 M b).toNat
  | 0 => by
    rw [accV_succ1, show accV M b 0 = 0 from rfl, Nat.mul_zero, add_ofNat_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    exact Nat.mod_eq_of_lt (BitVec.isLt _)
  | n + 1 => by
    rw [accV_succ1, show 32 * (n + 1) = 32 + 32 * n by omega, Nat.pow_add, Nat.mul_left_comm,
      Nat.add_mul_mod_self_left, accV_low n]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Choosing the root**, from 0x62E to 0x696: `y₀ = β` when `c = 1`
(else 0) at `S + 0xD4`, `-y₀` at `S + 0x104`, and in `a0` whether `y₀`'s
value has the parity `s5` asks for. -/
theorem dq_stH {M : Word → BitVec 8} {n : Machine} {S c : Word} {B : Nat} (C : DqCode M) (D : DqData M)
    (F : DqFrame S) (s : St M DP n 0x62E (reg n)) (rsp : reg n sp = S) (r8 : reg n (8 : Fin 32) = c)
    (hc : c = 0 ∨ c = 1) (hB : accV M (S + BitVec.ofNat 32 0x62C) 12 = B) (hBp : B < p384) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x696 (reg n') ∧ DqCode n'.mem ∧ DqData n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0xD4) 12 = (if c = 1 then B else 0) ∧
      accV n'.mem (S + BitVec.ofNat 32 0x104) 12 = dqNeg (if c = 1 then B else 0) ∧
      reg n' a0 = (if p3fm (if c = 1 then B else 0) 1 % 2 = (reg n (21 : Fin 32)).toNat % 2 then 1 else 0) ∧
      reg n' (8 : Fin 32) = c ∧ reg n' sp = S ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21] → reg n' q = reg n q) ∧
      (∀ x, Sep (S + 0xFFFFFF60) 0xA0 x 1 → Sep (S + BitVec.ofNat 32 0xD4) 0x60 x 1 →
        Sep (S + BitVec.ofNat 32 0x29C) 0x91 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 0x31 x 1 → n'.mem x = M x) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbA : (S + 0xFFFFFF60).toNat = S.toNat - 0xA0 := F.below 0xA0 (by decide) (by decide)
  have hb60 : (S + 0xFFFFFFA0).toNat = S.toNat - 0x60 := F.below 0x60 (by decide) (by decide)
  have hb54 : (S + 0xFFFFFFAC).toNat = S.toNat - 0x54 := F.below 0x54 (by decide) (by decide)
  have hb50 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have hb11 : (S + 0xFFFFFFEF).toNat = S.toNat - 0x11 := F.below 0x11 (by decide) (by decide)
  have loK : ∀ {k : Nat} {B' : Word}, B'.toNat = S.toNat - k → k ≤ 0x1A0 → ∀ x : Word, 0x40000000 ≤ x.toNat →
      Sep B' k x 1 := fun {k B'} hB' hk x hx => sep_of_le (by rw [hB']; omega) (by have := x.isLt; omega)
  have below : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have lowSub : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0xA0 →
      Sep (S + 0xFFFFFF60) 0xA0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have := hx.sub (c := 0xA0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFF60 + BitVec.ofNat 32 (0xA0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbA, hB']; omega] at this
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0xBF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have sq : ∀ c l d, c + l ≤ 0xA50 → d + 1 ≤ 0xA50 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have al : ∀ c, c + 4 ≤ 0xA50 → c % 4 = 0 → (S + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [F.at c (by omega)]; omega
  -- store `c` after `β`
  obtain ⟨n1, c1, u1⟩ := s.block dqK0 C.self dqK0_end (by
    simp only [BlockOk, BInstr.ok, dqK0]; simp +decide only [and_true]
    rw [rsp]; exact F.sepHi (by decide) (by decide) (by decide))
  have r1 : ∀ q, reg n1 q = (runBlock dqK0 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore8 M (S + BitVec.ofNat 32 0x65C) (c.extractLsb' 0 8) = M1 := ⟨_, rfl⟩
  have m1 : n1.mem = M1 := by
    rw [u1.mem, ← hM1]; simp +decide only [runBlock, BInstr.run, dqK0, upd, ↓reduceIte]; rw [rsp, r8]; rfl
  have h1 : ∀ x, Sep (S + BitVec.ofNat 32 0x65C) 1 x 1 → M1 x = M x := fun x hx => by rw [← hM1]; exact dq_st8 hx
  have C1 := C.hi fun x hx => h1 x (F.hiOut (by decide) hx)
  have D1 : DqData M1 := D.of F fun x hx => h1 x (inFrame (by decide) hx)
  have t1 : St M1 DP n1 0x638 (reg n1) := ⟨u1.pc, m1, fun _ => rfl⟩
  have sp1 : reg n1 sp = S := by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp
  have e65C : S + BitVec.ofNat 32 0x62C + 0x30 = S + BitVec.ofNat 32 0x65C := by rw [BitVec.add_assoc]; rfl
  have hcb : M1 (S + BitVec.ofNat 32 0x62C + 0x30) = c.extractLsb' 0 8 := by rw [e65C, ← hM1]; exact memStore8_same _ _ _
  have hcb01 : M1 (S + BitVec.ofNat 32 0x62C + 0x30) = 0 ∨ M1 (S + BitVec.ofNat 32 0x62C + 0x30) = 1 := by
    rw [hcb]; rcases hc with h | h <;> rw [h] <;> decide
  -- the root as a `CtOption`
  obtain ⟨n2, c2, u2, w2, b2, fr2, sp2, k2⟩ := dq_cmap (out := S + BitVec.ofNat 32 0x2FC) (x := S + BitVec.ofNat 32 0x62C)
    (co := 0x2FC) (cx := 0x62C) t1 C1 F dp_at_638 dp_at_63c (by decide) (by decide) sp1
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqK0, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqK0, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by decide) (by decide) rfl rfl (by decide) hcb01
  have C2 := C1.hi fun x hx => fr2 x (loK hbA (by decide) x hx) (F.hiOut (by decide) hx)
  have D2 : DqData n2.mem := D1.of F fun x hx => fr2 x (below hbA (by decide) (by decide) hx) (inFrame (by decide) hx)
  -- zero
  obtain ⟨n3, c3, u3⟩ := u2.block dqK1 C2.self dqK1_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock dqK1 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, m4, k4⟩ := dq_memset (dst := S + BitVec.ofNat 32 0x29C) (b := 0) (N := 48)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem DP n3 0x648 (reg n3)) C2 dp_at_648 dp_at_64c (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqK1, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqK1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqK1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    (by rw [F.at _ (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have fr4 : ∀ x, Sep (S + BitVec.ofNat 32 0x29C) 48 x 1 → n4.mem x = n2.mem x := fun x hx => by
    rw [m4]; exact fillBytes_sep hx (Nat.le_refl _)
  have C4 := C2.hi fun x hx => fr4 x (F.hiOut (by decide) hx)
  have D4 : DqData n4.mem := D2.of F fun x hx => fr4 x (inFrame (by decide) hx)
  have k4' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n2 q := fun q hq => by
    rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.zero (by simp only [dqK1]; revert hq; revert q; decide)]
  have sp4 : reg n4 sp = S := by rw [k4' sp (by decide)]; exact sp2
  -- select `y₀`
  obtain ⟨n5, c5, u5⟩ := u4.block dqK2 C4.self dqK2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock dqK2 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e58 : reg n5 (8 : Fin 32) = c := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, dqK2, upd, ↓reduceIte]; rw [sp4]
    show (n4.mem (S + BitVec.ofNat 32 0x32C)).zeroExtend 32 = c
    rw [fr4 _ (sq _ _ _ (by decide) (by decide) (.inl (by decide))),
      show S + BitVec.ofNat 32 0x32C = S + BitVec.ofNat 32 0x2FC + 0x30 by rw [BitVec.add_assoc]; rfl, b2, hcb]
    rcases hc with h | h <;> rw [h] <;> decide
  obtain ⟨n6, c6, u6, w6, fr6, sp6, k6⟩ := dq_csel (out := S + BitVec.ofNat 32 0xD4) (a := S + BitVec.ofNat 32 0x29C)
    (b := S + BitVec.ofNat 32 0x2FC) (c := c) (co := 0xD4) (ca := 0x29C) (cb := 0x2FC)
    (⟨u5.pc, u5.mem, fun _ => rfl⟩ : St n4.mem DP n5 0x65C (reg n5)) C4 F dp_at_65c dp_at_660 (by decide) (by decide)
    (by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqK2, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqK2, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqK2, upd, ↓reduceIte]; rw [sp4]; rfl)
    (by rw [r5]; simp +decide only [runBlock, BInstr.run, dqK2, upd, ↓reduceIte]; rw [← e58, r5]
        simp +decide only [runBlock, BInstr.run, dqK2, upd, ↓reduceIte]; exact BitVec.zero_add _)
    hc (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have C6 := C4.hi fun x hx => fr6 x (loK hb60 (by decide) x hx) (F.hiOut (by decide) hx)
  have D6 : DqData n6.mem := D4.of F fun x hx => fr6 x (below hb60 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have hY : accV n6.mem (S + BitVec.ofNat 32 0xD4) 12 = (if c = 1 then B else 0) := by
    rcases hc with h0 | h0
    · rw [ite_eq_right (by rw [h0]; decide)]
      exact accV_zero 12 fun i hi => by
        rw [w6 i hi, ite_eq_right (by rw [h0]; decide), m4, fill_word0 (by omega) (by decide)]
    · rw [ite_eq_left h0, ← hB]
      have hcb1 : M1 (S + BitVec.ofNat 32 0x62C + 0x30) = 1 := by rw [hcb, h0]; decide
      refine accV_congr2 12 fun i hi => ?_
      rw [w6 i hi, ite_eq_left h0, add_ofNat_assoc, m4,
        fill_word_out (sepS S (.inl (by omega)) (by decide) (by omega)), ← add_ofNat_assoc, w2 i hi, ite_eq_left hcb1,
        add_ofNat_assoc]
      exact load_frame h1 (sepS S (.inr (by omega)) (by decide) (by omega))
  have hYp : (if c = 1 then B else 0) < p384 := by
    rcases hc with h0 | h0
    · rw [ite_eq_right (by rw [h0]; decide)]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hBp
    · rw [ite_eq_left h0]; exact hBp
  have K6 : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21] → reg n6 q = reg n q := fun q hq => by
    rw [k6 q (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [dqK2]; revert hq; revert q; decide),
      k4' q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [dqK0]; revert hq; revert q; decide)]
  have e68 : reg n6 (8 : Fin 32) = c := by rw [k6 8 (by decide), e58]
  -- negate
  obtain ⟨n7, c7, u7⟩ := u6.block dqK3 C6.self dqK3_end ⟨trivial, trivial, trivial⟩
  have r7 : ∀ q, reg n7 q = (runBlock dqK3 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  obtain ⟨n8, c8, u8, e8, fr8, sp8, k8⟩ := dq_neg (out := S + BitVec.ofNat 32 0x104) (xp := S + BitVec.ofNat 32 0xD4)
    (co := 0x104) (cx := 0xD4) (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem DP n7 0x668 (reg n7)) C6 D6 F dp_at_668 dp_at_66c
    (by decide) (by decide) (by rw [r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, dqK3, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, dqK3, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by decide) (by decide) rfl rfl (by decide) (by decide)
  have C8 := C6.hi fun x hx => fr8 x (loK hb54 (by decide) x hx) (F.hiOut (by decide) hx)
  have D8 : DqData n8.mem := D6.of F fun x hx => fr8 x (below hb54 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have hN8 : accV n8.mem (S + BitVec.ofNat 32 0x104) 12 = dqNeg (if c = 1 then B else 0) := by rw [e8, hY]; rfl
  have hY8 : accV n8.mem (S + BitVec.ofNat 32 0xD4) 12 = (if c = 1 then B else 0) := by
    rw [← hY]; exact accV_keep fun q hq =>
      fr8 _ (F.lowB hb54 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  -- out of Montgomery form
  obtain ⟨n9, c9, u9⟩ := u8.block dqK4 C8.self dqK4_end ⟨trivial, trivial, trivial⟩
  have r9 : ∀ q, reg n9 q = (runBlock dqK4 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  obtain ⟨n10, c10, u10, e10, fr10, sp10, k10⟩ := dq_rt (out := S + BitVec.ofNat 32 0x62C) (xp := S + BitVec.ofNat 32 0xD4)
    (co := 0x62C) (cx := 0xD4) (⟨u9.pc, u9.mem, fun _ => rfl⟩ : St n8.mem DP n9 0x676 (reg n9)) C8 D8 F dp_at_676 dp_at_67a
    (by decide) (by decide) (by rw [r9, runBlock_reg _ _ _ sp u8.zero (by decide)]; exact sp8)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, dqK4, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, dqK4, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by decide) (by decide) rfl rfl (by decide) (by decide) (by rw [hY8]; exact hYp)
  have C10 := C8.hi fun x hx => fr10 x (loK hb50 (by decide) x hx) (F.hiOut (by decide) hx)
  have D10 : DqData n10.mem := D8.of F fun x hx => fr10 x (below hb50 (by decide) (by decide) hx) (inFrame (by decide) hx)
  -- the parity
  obtain ⟨n11, c11, u11⟩ := u10.block dqK5 C10.self dqK5_end (by
    simp only [BlockOk, BInstr.ok, dqK5]; simp +decide only [and_true]
    rw [sp10]; exact al 0x62C (by decide) (by decide))
  have r11 : ∀ q, reg n11 q = (runBlock dqK5 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have a11 : reg n11 a0 = memLoad32 n10.mem (S + BitVec.ofNat 32 0x62C) &&& 1 := by
    rw [r11]; simp +decide only [runBlock, BInstr.run, dqK5, upd, ↓reduceIte]; rw [sp10]; rfl
  have sp11 : reg n11 sp = S := by rw [r11, runBlock_reg _ _ _ sp u10.zero (by decide)]; exact sp10
  obtain ⟨n12, c12, u12, e12, fr12, k12⟩ := dq_bb
    (⟨u11.pc, u11.mem, fun _ => rfl⟩ : St n10.mem DP n11 0x684 (reg n11)) C10 F dp_at_684 dp_at_688 (by decide) (by decide) sp11
  have C12 := C10.hi fun x hx => fr12 x (loK hb1 (by decide) x hx)
  have D12 : DqData n12.mem := D10.of F fun x hx => fr12 x (below hb1 (by decide) (by decide) hx)
  obtain ⟨n13, c13, u13⟩ := u12.block dqK6 C12.self dqK6_end ⟨trivial, trivial⟩
  have r13 : ∀ q, reg n13 q = (runBlock dqK6 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have KB : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 19, 20, 21] → reg n12 q = reg n6 q := fun q hq => by
    rw [k12 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r11, runBlock_reg _ _ _ q u10.zero (by simp only [dqK5]; revert hq; revert q; decide),
      k10 q (by revert hq; revert q; decide), r9, runBlock_reg _ _ _ q u8.zero (by simp only [dqK4]; revert hq; revert q; decide),
      k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r7, runBlock_reg _ _ _ q u6.zero (by simp only [dqK3]; revert hq; revert q; decide)]
  have sp12 : reg n12 sp = S := by rw [k12 sp (by decide) (by decide)]; exact sp11
  obtain ⟨n14, c14, u14, e14, fr14, k14⟩ := dq_cte
    (a := ((memLoad32 n10.mem (S + BitVec.ofNat 32 0x62C) &&& 1).extractLsb' 0 8).zeroExtend 32) (b := reg n (21 : Fin 32))
    (⟨u13.pc, u13.mem, fun _ => rfl⟩ : St n12.mem DP n13 0x68E (reg n13)) C12 F dp_at_68e dp_at_692 (by decide) (by decide)
    (by rw [r13, runBlock_reg _ _ _ sp u12.zero (by decide)]; exact sp12)
    (by rw [r13, runBlock_reg _ _ _ a0 u12.zero (by decide), e12, a11])
    (by rw [r13]; simp +decide only [runBlock, BInstr.run, dqK6, upd, ↓reduceIte]
        rw [KB 21 (by decide), K6 21 (by decide)]; exact BitVec.zero_add _)
  have C14 := C12.hi fun x hx => fr14 x (loK hb11 (by decide) x hx)
  have D14 : DqData n14.mem := D12.of F fun x hx => fr14 x (below hb11 (by decide) (by decide) hx)
  have back : ∀ d, d + 1 ≤ 0xA50 → (d + 1 ≤ 0x62C ∨ 0x65C ≤ d) → n14.mem (S + BitVec.ofNat 32 d) = n8.mem (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 => by
      rw [fr14 _ (F.lowB hb11 (by decide) h1), fr12 _ (F.lowB hb1 (by decide) h1),
        fr10 _ (F.lowB hb50 (by decide) h1) (sq _ _ _ (by decide) h1 (by rcases h2 with h | h; exact .inr h; exact .inl h))]
  have hpar : (memLoad32 n10.mem (S + BitVec.ofNat 32 0x62C)).toNat % 2 = p3fm (if c = 1 then B else 0) 1 % 2 := by
    have := accV_low (M := n10.mem) (b := S + BitVec.ofNat 32 0x62C) 11
    rw [show 11 + 1 = 12 from rfl, e10, hY8] at this
    rw [← this, Nat.mod_mod_of_dvd _ (by decide)]
  refine ⟨n14, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans c14)))))))))))), u14, C14, D14, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hY8]; exact accV_keep fun q hq => back _ (by omega) (.inl (by omega))
  · rw [← hN8]; exact accV_keep fun q hq => back _ (by omega) (.inl (by omega))
  · rw [e14]
    by_cases h : p3fm (if c = 1 then B else 0) 1 % 2 = (reg n (21 : Fin 32)).toNat % 2
    · rw [ite_eq_left ((par_iff _ _).2 (by rw [hpar]; exact h)), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (by rw [← hpar]; exact (par_iff _ _).1 h')), ite_eq_right h]
  · rw [k14 8 (by decide) (by decide) (by decide), r13, runBlock_reg _ _ _ 8 u12.zero (by decide), KB 8 (by decide), e68]
  · rw [k14 sp (by decide) (by decide) (by decide), r13, runBlock_reg _ _ _ sp u12.zero (by decide)]; exact sp12
  · intro q hq
    rw [k14 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), r13, runBlock_reg _ _ _ q u12.zero (by simp only [dqK6]; revert hq; revert q; decide),
      KB q (by revert hq; revert q; decide), K6 q hq]
  · intro x hx hD4 h29C h62C
    have sub0 : ∀ {b : Word} {l l' : Nat}, l' ≤ l → Sep b l x 1 → Sep b l' x 1 := fun {b l l'} hl h => by
      have := h.sub (c := 0) (l := l') (by omega); rwa [add_ofNat_zero] at this
    have hD104 : Sep (S + BitVec.ofNat 32 0x104) 48 x 1 := by
      have := hD4.sub (c := 0x30) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    have h2FC : Sep (S + BitVec.ofNat 32 0x2FC) 0x31 x 1 := by
      have := h29C.sub (c := 0x60) (l := 0x31) (by decide); rwa [add_ofNat_assoc] at this
    have h65C : Sep (S + BitVec.ofNat 32 0x65C) 1 x 1 := by
      have := h62C.sub (c := 0x30) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
    rw [fr14 x (lowSub hb11 (by decide) (by decide) hx), fr12 x (lowSub hb1 (by decide) (by decide) hx),
      fr10 x (lowSub hb50 (by decide) (by decide) hx) (sub0 (by decide) h62C),
      fr8 x (lowSub hb54 (by decide) (by decide) hx) hD104, fr6 x (lowSub hb60 (by decide) (by decide) hx) (sub0 (by decide) hD4),
      fr4 x (sub0 (by decide) h29C), fr2 x hx h2FC]
    exact h1 x h65C

/-! ## Writing the point -/

def dqI0 : List BInstr :=
  [.aluImm .add a4 sp 0x65C, .aluImm .and a3 a0 0xFF, .aluImm .add a1 sp 0x104, .aluImm .add a2 sp 0xD4, .alu .add a0 x0 a4]
def dqI1 : List BInstr := [.aluImm .add a0 sp 0x62C, .aluImm .add a1 sp 0xA4, .aluImm .add a2 x0 0x30]
def dqI2 : List BInstr := [.sb sp x0 0x68C, .alu .and a0 (8 : Fin 32) (20 : Fin 32)]
def dqI3 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a1 sp 0x62C, .aluImm .add a2 x0 0x64, .alu .add a0 x0 (19 : Fin 32)]
def dqI4a : List BInstr := [.sb (19 : Fin 32) (8 : Fin 32) 0x64]
def dqI4b : List BInstr :=
  [.aluImm .add sp sp 0x260, .aluImm .add a0 sp 0x780, .lw ra a0 0x6C, .lw (8 : Fin 32) a0 0x68, .lw (9 : Fin 32) a0 0x64, .lw (18 : Fin 32) a0 0x60, .lw (19 : Fin 32) a0 0x5C, .lw (20 : Fin 32) a0 0x58, .lw (21 : Fin 32) a0 0x54, .lw (22 : Fin 32) a0 0x50, .lw (23 : Fin 32) a0 0x4C, .lw (24 : Fin 32) a0 0x48, .lw (25 : Fin 32) a0 0x44, .lw (26 : Fin 32) a0 0x40, .lw (27 : Fin 32) a0 0x3C, .aluImm .add sp sp 0x7F0]

theorem dqI0_end : blockEnd p384DecompressCode 0x696 dqI0 = some 0x6A4 := by decide
theorem dqI1_end : blockEnd p384DecompressCode 0x6AC dqI1 = some 0x6B6 := by decide
theorem dqI2_end : blockEnd p384DecompressCode 0x6BE dqI2 = some 0x6C6 := by decide
theorem dqI3_end : blockEnd p384DecompressCode 0x6CE dqI3 = some 0x6DA := by decide
theorem dqI4a_end : blockEnd p384DecompressCode 0x6E2 dqI4a = some 0x6E6 := by decide
theorem dqI4b_end : blockEnd p384DecompressCode 0x6E6 dqI4b = some 0x722 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **Writing the point**, from 0x696 to the return: `y` is `y₀` or `-y₀`
by the parity test, and `decompress` writes `x`, `y`, the identity flag 0,
and `c ∧ ok` as the choice to `out`, then restores the saved registers. -/
theorem dq_stI {M : Word → BitVec 8} {n : Machine} {S out par c ok : Word} {X Y0 N0 : Nat} {v : Nat → Word}
    (C : DqCode M) (D : DqData M) (F : DqFrame S) (s : St M DP n 0x696 (reg n)) (rsp : reg n sp = S)
    (ra0 : reg n a0 = par) (hpar : par = 0 ∨ par = 1) (r8 : reg n (8 : Fin 32) = c) (hc : c = 0 ∨ c = 1)
    (r19 : reg n (19 : Fin 32) = out) (r20 : reg n (20 : Fin 32) = ok) (hok : ok = 0 ∨ ok = 1)
    (sO : Sep out 0x65 (S + 0xFFFFFE60) 0xBF0) (hO : out.toNat + 0x65 ≤ 0x40000000)
    (hX : accV M (S + BitVec.ofNat 32 0xA4) 12 = X) (hY : accV M (S + BitVec.ofNat 32 0xD4) 12 = Y0)
    (hN : accV M (S + BitVec.ofNat 32 0x104) 12 = N0)
    (hZ : ∀ k, k < 3 → M (S + BitVec.ofNat 32 (0x68D + k)) = BitVec.ofNat 8 0)
    (hS : ∀ k, k < 13 → memLoad32 M (S + BitVec.ofNat 32 (0xA4C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0) :
    ∃ n', Steps n n' ∧ n'.pc = v 0 ∧ reg n' sp = S + 0xA50 ∧ (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
      accV n'.mem out 12 = X ∧ accV n'.mem (out + BitVec.ofNat 32 0x30) 12 = (if par = 1 then Y0 else N0) ∧
      (∀ k, k < 4 → n'.mem (out + BitVec.ofNat 32 (0x60 + k)) = BitVec.ofNat 8 0) ∧
      n'.mem (out + BitVec.ofNat 32 0x64) = (if c = 1 ∧ ok = 1 then 1 else 0) ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) ∧
      ∀ x, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep out 0x65 x 1 → n'.mem x = M x := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨fA, fW, hFC, b16⟩ := F.mc
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb60 : (S + 0xFFFFFFA0).toNat = S.toNat - 0x60 := F.below 0x60 (by decide) (by decide)
  have hb1 : (S + 0xFFFFFFFF).toNat = S.toNat - 1 := F.below 1 (by decide) (by decide)
  have loK : ∀ {k : Nat} {B' : Word}, B'.toNat = S.toNat - k → k ≤ 0x1A0 → ∀ x : Word, 0x40000000 ≤ x.toNat →
      Sep B' k x 1 := fun {k B'} hB' hk x hx => sep_of_le (by rw [hB']; omega) (by have := x.isLt; omega)
  have below : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0xBF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have l16b : ∀ d, d + 1 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 1 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have l16 : ∀ d, d + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have sq : ∀ c l d, c + l ≤ 0xA50 → d + 1 ≤ 0xA50 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have oF : ∀ j, j < 0x65 → Sep (S + 0xFFFFFE60) 0xBF0 (out + BitVec.ofNat 32 j) 1 := fun j hj =>
    (sO.sub (c := j) (l := 1) (by omega)).symm
  have oAt : ∀ j, j ≤ 0x65 → (out + BitVec.ofNat 32 j).toNat = out.toNat + j := fun j hj => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have oLow : ∀ {k : Nat} {B' : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 → Sep out 0x65 B' k :=
    fun {k B'} hB' hk hk' => by
      have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
      have := sO.subR (c := 0x1A0 - k) (l := k) (by omega)
      rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have oBuf : ∀ {c l : Nat}, c + l ≤ 0xA50 → Sep out 0x65 (S + BitVec.ofNat 32 c) l := fun {c l} h => by
    have := sO.subR (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have shr : ∀ {a b : Word} {l l' k : Nat}, l' ≤ l → Sep a l b k → Sep a l' b k := fun {a b l l' k} hl h => by
    have := h.sub (c := 0) (l := l') (by omega); rwa [add_ofNat_zero] at this
  have oHi : ∀ {x : Word}, 0x40000000 ≤ x.toNat → Sep out 0x65 x 1 := fun {x} hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  -- select `y`
  obtain ⟨n1, c1, u1⟩ := s.block dqI0 C.self dqI0_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock dqI0 (M, reg n)).2 q := fun q => by rw [u1.regs]
  have hpar' : aluEval .and par 0xFF = par := by rcases hpar with h | h <;> rw [h] <;> decide
  obtain ⟨n2, c2, u2, w2, fr2, sp2, k2⟩ := dq_csel (out := S + BitVec.ofNat 32 0x65C) (a := S + BitVec.ofNat 32 0x104)
    (b := S + BitVec.ofNat 32 0xD4) (c := par) (co := 0x65C) (ca := 0x104) (cb := 0xD4)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M DP n1 0x6A4 (reg n1)) C F dp_at_6a4 dp_at_6a8 (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqI0, upd, ↓reduceIte]; rw [rsp]; exact BitVec.zero_add _)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqI0, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqI0, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqI0, upd, ↓reduceIte]; rw [ra0]; exact hpar')
    hpar (by decide) (by decide) (by decide) rfl rfl rfl (by decide)
  have C2 := C.hi fun x hx => fr2 x (loK hb60 (by decide) x hx) (F.hiOut (by decide) hx)
  have D2 : DqData n2.mem := D.of F fun x hx => fr2 x (below hb60 (by decide) (by decide) hx) (inFrame (by decide) hx)
  have K2 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 19, 20] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [dqI0]; revert hq; revert q; decide)]
  -- copy `x`
  obtain ⟨n3, c3, u3⟩ := u2.block dqI1 C2.self dqI1_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock dqI1 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, fr4, k4⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x62C) (src := S + BitVec.ofNat 32 0xA4)
    (S := S) (N := 48) (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem DP n3 0x6B6 (reg n3)) C2 dp_at_6b6 dp_at_6ba
    (by decide) (by decide) (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqI1, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqI1, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, dqI1, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    ⟨C2.body, F.sepHi (by decide) (by decide) (by decide), hFC, F.mcN (by decide), F.mcN (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [F.at _ (by decide)]; omega,
      by rw [F.at _ (by decide)]; omega⟩
  have fr4' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 → n4.mem x = n2.mem x :=
    fun x a b => by rw [fr4 x a, copyBytes_sep b (Nat.le_refl _)]
  have C4 := C2.hi fun x hx => fr4' x (loK hb16 (by decide) x hx) (F.hiOut (by decide) hx)
  have k4' := kc k4
  have sp4 : reg n4 sp = S := by rw [k4' sp (by decide), r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2
  -- the identity flag, and the choice
  obtain ⟨n5, c5, u5⟩ := u4.block dqI2 C4.self dqI2_end (by
    simp only [BlockOk, BInstr.ok, dqI2]; simp +decide only [and_true]
    rw [sp4]; exact F.sepHi (by decide) (by decide) (by decide))
  have r5 : ∀ q, reg n5 q = (runBlock dqI2 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore8 n4.mem (S + BitVec.ofNat 32 0x68C) ((0 : Word).extractLsb' 0 8) = M5 := ⟨_, rfl⟩
  have m5 : n5.mem = M5 := by
    rw [u5.mem, ← hM5]; simp +decide only [runBlock, BInstr.run, dqI2, upd, ↓reduceIte]; rw [sp4, u4.zero]; rfl
  have h5 : ∀ x, Sep (S + BitVec.ofNat 32 0x68C) 1 x 1 → M5 x = n4.mem x := fun x hx => by rw [← hM5]; exact dq_st8 hx
  have C5 := C4.hi fun x hx => h5 x (F.hiOut (by decide) hx)
  have sp5 : reg n5 sp = S := by rw [r5, runBlock_reg _ _ _ sp u4.zero (by decide)]; exact sp4
  obtain ⟨n6, c6, u6, e6, fr6, k6⟩ := dq_bb (⟨u5.pc, m5, fun _ => rfl⟩ : St M5 DP n5 0x6C6 (reg n5)) C5 F dp_at_6c6 dp_at_6ca
    (by decide) (by decide) sp5
  have C6 := C5.hi fun x hx => fr6 x (loK hb1 (by decide) x hx)
  -- copy the point to `out`
  obtain ⟨n7, c7, u7⟩ := u6.block dqI3 C6.self dqI3_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r7 : ∀ q, reg n7 q = (runBlock dqI3 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have sp6 : reg n6 sp = S := by rw [k6 sp (by decide) (by decide)]; exact sp5
  have K6 : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20] → reg n6 q = reg n q := fun q hq => by
    rw [k6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), r5, runBlock_reg _ _ _ q u4.zero (by simp only [dqI2]; revert hq; revert q; decide),
      k4' q (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.zero (by simp only [dqI1]; revert hq; revert q; decide), K2 q (by revert hq; revert q; decide)]
  have e78 : reg n7 (8 : Fin 32) = ((c &&& ok).extractLsb' 0 8).zeroExtend 32 := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, dqI3, upd, ↓reduceIte]
    rw [e6, r5]; simp +decide only [runBlock, BInstr.run, dqI2, upd, ↓reduceIte]
    rw [k4' 8 (by decide), r3, runBlock_reg _ _ _ 8 u2.zero (by decide), K2 8 (by decide), r8,
      k4' 20 (by decide), r3, runBlock_reg _ _ _ 20 u2.zero (by decide), K2 20 (by decide), r20]
    exact BitVec.zero_add _
  have hMC : Sep out 0x64 (MCS + 8) memcpyBodyCode.length := by
    have : 0x40000000 ≤ (MCS + 8 : Word).toNat := by decide
    exact sep_of_le (by omega) (by decide)
  obtain ⟨n8, c8, u8, fr8, k8⟩ := dq_memcpy (dst := out) (src := S + BitVec.ofNat 32 0x62C) (S := S) (N := 0x64)
    (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n6.mem DP n7 0x6DA (reg n7)) C6 dp_at_6da dp_at_6de (by decide) (by decide)
    (by rw [r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, dqI3, upd, ↓reduceIte]; rw [K6 19 (by decide), r19]
        exact BitVec.zero_add _)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, dqI3, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, dqI3, upd, ↓reduceIte]; (try rw [u6.zero]); try rfl)
    ⟨C6.body, hMC, hFC, shr (by decide) (oLow hb16 (by decide) (by decide)),
      F.mcN (by decide), shr (by decide) (oBuf (by decide)), fA, fW, by omega, by rw [F.at _ (by decide)]; omega⟩
  have fr8' : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep out 0x64 x 1 → n8.mem x = n6.mem x :=
    fun x a b => by rw [fr8 x a, copyBytes_sep b (Nat.le_refl _)]
  have C8 := C6.hi fun x hx => fr8' x (loK hb16 (by decide) x hx) (shr (by decide) (oHi hx))
  have k8' := kc k8
  have sp8 : reg n8 sp = S := by rw [k8' sp (by decide), r7, runBlock_reg _ _ _ sp u6.zero (by decide)]; exact sp6
  have K8 : ∀ q : Fin 32, q.val ∈ [3, 4, 19] → reg n8 q = reg n q := fun q hq => by
    rw [k8' q (by revert hq; revert q; decide), r7, runBlock_reg _ _ _ q u6.zero (by simp only [dqI3]; revert hq; revert q; decide), K6 q (by revert hq; revert q; decide)]
  -- store the choice
  have hO64 : Sep (out + 0x64) 1 DP p384DecompressCode.length := by
    have : 0x40000000 ≤ DP.toNat := by decide
    exact sep_of_le (by rw [show (out + 0x64 : Word) = out + BitVec.ofNat 32 0x64 from rfl, oAt 0x64 (by decide)]; omega)
      (by decide)
  obtain ⟨n9, c9, u9⟩ := u8.block dqI4a C8.self dqI4a_end (by
    simp only [BlockOk, BInstr.ok, dqI4a]; simp +decide only [and_true]
    rw [K8 19 (by decide), r19]; exact hO64)
  obtain ⟨M9, hM9⟩ : ∃ M9, memStore8 n8.mem (out + BitVec.ofNat 32 0x64)
      ((((c &&& ok).extractLsb' 0 8).zeroExtend 32 : Word).extractLsb' 0 8) = M9 := ⟨_, rfl⟩
  have m9 : n9.mem = M9 := by
    rw [u9.mem, ← hM9]; simp +decide only [runBlock, BInstr.run, dqI4a, upd, ↓reduceIte]
    rw [K8 19 (by decide), r19, k8' 8 (by decide), e78]; rfl
  have h9 : ∀ x, Sep (out + BitVec.ofNat 32 0x64) 1 x 1 → M9 x = n8.mem x := fun x hx => by rw [← hM9]; exact dq_st8 hx
  have C9 := C8.hi fun x hx => h9 x ((oHi hx).sub (c := 0x64) (l := 1) (by decide))
  have r9 : ∀ q, reg n9 q = reg n8 q := fun q => by rw [u9.regs]; rfl
  have sp9 : reg n9 sp = S := by rw [r9]; exact sp8
  -- what memory holds now
  have sub60 : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x60 →
      Sep (S + 0xFFFFFFA0) 0x60 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have := hx.sub (c := 0x60 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFFA0 + BitVec.ofNat 32 (0x60 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb60, hB']; omega] at this
  have fin : ∀ x, Sep (S + 0xFFFFFFA0) 0x60 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 0x61 x 1 → Sep out 0x65 x 1 →
      M9 x = M x := fun x hl hb ho => by
    have hb48 : Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 := shr (by decide) hb
    have h65C : Sep (S + BitVec.ofNat 32 0x65C) 48 x 1 := by
      have := hb.sub (c := 0x30) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    have h68C : Sep (S + BitVec.ofNat 32 0x68C) 1 x 1 := by
      have := hb.sub (c := 0x60) (l := 1) (by decide); rwa [add_ofNat_assoc] at this
    rw [h9 x (ho.sub (c := 0x64) (l := 1) (by decide)), fr8' x (sub60 hb16 (by decide) (by decide) hl) (shr (by decide) ho),
      fr6 x (sub60 hb1 (by decide) (by decide) hl), h5 x h68C, fr4' x (sub60 hb16 (by decide) (by decide) hl) hb48,
      fr2 x hl h65C]
  have lowOut : ∀ j, j < 0x65 → Sep (S + 0xFFFFFFF0) 16 (out + BitVec.ofNat 32 j) 1 := fun j hj =>
    below hb16 (by decide) (by decide) (oF j hj)
  have sepO : ∀ j, j + 1 ≤ 0x64 → Sep (out + BitVec.ofNat 32 0x64) 1 (out + BitVec.ofNat 32 j) 1 := fun j hj =>
    sep_offsets out (.inr (by omega)) (by omega) (by omega)
  have byB : ∀ k, k < 0x64 → M9 (out + BitVec.ofNat 32 k) = n6.mem (S + BitVec.ofNat 32 (0x62C + k)) := fun k hk => by
    rw [h9 _ (sepO k (by omega)), fr8 _ (lowOut k (by omega)), cp_at hk (by decide), add_ofNat_assoc]
  have ldB : ∀ k, k + 4 ≤ 0x64 → memLoad32 M9 (out + BitVec.ofNat 32 k) = memLoad32 n6.mem (S + BitVec.ofNat 32 (0x62C + k)) :=
    fun k hk => by
      rw [memLoad32_congr (M := copyBytes n6.mem out (S + BitVec.ofNat 32 0x62C) 0x64) fun j hj => by
        rw [add_ofNat_assoc, h9 _ (sepO _ (by omega)), fr8 _ (lowOut _ (by omega))], cp_word (by omega) (by decide),
        add_ofNat_assoc]
  have back6 : ∀ d, d + 1 ≤ 0xA50 → (d + 1 ≤ 0x68C ∨ 0x68D ≤ d) → (d + 1 ≤ 0x62C ∨ 0x65C ≤ d) →
      n6.mem (S + BitVec.ofNat 32 d) = n2.mem (S + BitVec.ofNat 32 d) := fun d h1 h2 h3 => by
    rw [fr6 _ (F.lowB hb1 (by decide) h1), h5 _ (sq _ _ _ (by decide) h1 (by rcases h2 with h | h; exact .inr h; exact .inl h)),
      fr4' _ (l16b _ h1) (sq _ _ _ (by decide) h1 (by rcases h3 with h | h; exact .inr h; exact .inl h))]
  have hS9 : ∀ k, k < 13 → memLoad32 M9 (S + BitVec.ofNat 32 (0xA4C - 4 * k)) = v k := fun k hk => by
    rw [← hS k hk]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact fin _ (F.lowB hb60 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))
        (oBuf (by omega))
  -- restore the saved registers and return
  have hA3 : aluEval .add (aluEval .add S 0x260) 0x780 = S + BitVec.ofNat 32 0x9E0 := by
    show S + 0x260 + 0x780 = S + BitVec.ofNat 32 0x9E0
    rw [BitVec.add_assoc]; rfl
  have alB : ∀ k : Word, 0x9E0 + k.toNat + 4 ≤ 0xA50 → k.toNat % 4 = 0 →
      (S + BitVec.ofNat 32 0x9E0 + k).toNat % 4 = 0 := fun k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  obtain ⟨n10, c10, u10⟩ := (⟨u9.pc, m9, fun _ => rfl⟩ : St M9 DP n9 0x6E6 (reg n9)).block dqI4b C9.self dqI4b_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqI4b]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp9, hA3]
    exact ⟨alB 0x6C (by decide) (by decide), alB 0x68 (by decide) (by decide), alB 0x64 (by decide) (by decide), alB 0x60 (by decide) (by decide), alB 0x5C (by decide) (by decide), alB 0x58 (by decide) (by decide), alB 0x54 (by decide) (by decide), alB 0x50 (by decide) (by decide), alB 0x4C (by decide) (by decide), alB 0x48 (by decide) (by decide), alB 0x44 (by decide) (by decide), alB 0x40 (by decide) (by decide), alB 0x3C (by decide) (by decide)⟩)
  have m10 : (runBlock dqI4b (M9, reg n9)).1 = M9 := rfl
  have C10 : DqCode (runBlock dqI4b (M9, reg n9)).1 := by rw [m10]; exact C9
  obtain ⟨n11, st11, pc11, mem11, regs11⟩ := u10.jalr C10.self dp_at_722
  have ra10 : (runBlock dqI4b (M9, reg n9)).2 ra = v 0 := by
    simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte]
    rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 0 (by decide)
  have mem11' : n11.mem = M9 := mem11.trans m10
  refine ⟨n11, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (.single st11)))))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc11, ra10]; exact (congrArg (· &&& ~~~1) (BitVec.add_zero _)).trans hret
  · rw [regs11]; simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte]; rw [sp9]
    show S + 0x260 + 0x7F0 = S + 0xA50
    rw [BitVec.add_assoc]; rfl
  · intro k hk
    rw [regs11]
    match k, hk with
    | 0, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 0 (by decide)
    | 1, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 1 (by decide)
    | 2, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 2 (by decide)
    | 3, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 3 (by decide)
    | 4, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 4 (by decide)
    | 5, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 5 (by decide)
    | 6, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 6 (by decide)
    | 7, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 7 (by decide)
    | 8, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 8 (by decide)
    | 9, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 9 (by decide)
    | 10, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 10 (by decide)
    | 11, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 11 (by decide)
    | 12, _ =>
      simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte, savedReg]
      rw [sp9, hA3, frame_lit _ (by decide)]; exact hS9 12 (by decide)
    | _ + 13, h => exact absurd h (by omega)
  · rw [mem11', ← hX]
    exact accV_congr2 12 fun i hi => by
      rw [ldB _ (by omega), ← add_ofNat_assoc S 0x62C,
        show memLoad32 n6.mem (S + BitVec.ofNat 32 0x62C + BitVec.ofNat 32 (4 * i)) =
          memLoad32 n4.mem (S + BitVec.ofNat 32 0x62C + BitVec.ofNat 32 (4 * i)) from memLoad32_congr fun j hj => by
            rw [add_ofNat_assoc, add_ofNat_assoc, fr6 _ (F.lowB hb1 (by decide) (by omega)),
              h5 _ (sq _ _ _ (by decide) (by omega) (.inr (by omega)))],
        load_frame fr4 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
      exact memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc, add_ofNat_assoc]
        exact fr2 _ (F.lowB hb60 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inr (by omega)))
  · rw [mem11']
    have hw : ∀ i, i < 12 → memLoad32 M9 (out + BitVec.ofNat 32 0x30 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 n2.mem (S + BitVec.ofNat 32 0x65C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
      rw [add_ofNat_assoc, ldB _ (by omega), add_ofNat_assoc, show 0x62C + (0x30 + 4 * i) = 0x65C + 4 * i by omega]
      exact memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact back6 _ (by omega) (.inl (by omega)) (.inr (by omega))
    rcases hpar with h | h
    · rw [ite_eq_right (by rw [h]; decide), ← hN]
      exact accV_congr2 12 fun i hi => by rw [hw i hi, w2 i hi, ite_eq_right (by rw [h]; decide)]
    · rw [ite_eq_left h, ← hY]
      exact accV_congr2 12 fun i hi => by rw [hw i hi, w2 i hi, ite_eq_left h]
  · intro k hk
    rw [mem11', byB _ (by omega)]
    rcases Nat.lt_or_ge k 1 with h | h
    · obtain rfl : k = 0 := by omega
      rw [fr6 _ (F.lowB hb1 (by decide) (by decide)), ← m5, u5.mem]
      simp +decide only [runBlock, BInstr.run, dqI2, upd, ↓reduceIte]
      rw [sp4, u4.zero]; exact memStore8_same _ _ _
    · rw [show 0x62C + (0x60 + k) = 0x68D + (k - 1) by omega, back6 _ (by omega) (.inr (by omega)) (.inr (by omega)),
        fr2 _ (F.lowB hb60 (by decide) (by omega)) (sq _ _ _ (by decide) (by omega) (.inl (by omega)))]
      exact hZ _ (by omega)
  · rw [mem11', ← hM9, memStore8_same]
    rcases hc with h | h <;> rcases hok with h' | h' <;> (rw [h, h']; decide)
  · rw [regs11]; simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte]; rw [r9, K8 3 (by decide)]
  · rw [regs11]; simp +decide only [runBlock, BInstr.run, dqI4b, upd, ↓reduceIte]; rw [r9, K8 4 (by decide)]
  · intro x hx ho
    rw [mem11']
    exact fin x (below hb60 (by decide) (by decide) hx) (inFrame (by decide) hx) ho

/-! ## The whole function -/

theorem ite01 (P : Prop) [Decidable P] : (if P then (1 : Word) else 0) = 0 ∨ (if P then (1 : Word) else 0) = 1 := by
  by_cases h : P
  · exact .inr (ite_eq_left h)
  · exact .inl (ite_eq_right h)

theorem ite01_iff (P : Prop) [Decidable P] : (if P then (1 : Word) else 0) = 1 ↔ P := by
  by_cases h : P
  · rw [ite_eq_left h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]; exact ⟨fun e => absurd e (by decide), fun e => absurd e h⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `<AffinePoint<NistP384> as DecompressPoint>::decompress`.**
With the 48 big-endian bytes of `x` at `inp` and the requested parity of `y`
in `a2`, it writes to `out` the `CtOption<AffinePoint>` that the RustCrypto
code returns: `x` in Montgomery form (0 when `x ≥ p`), the square root of
`α = x³ + ax + b` with the requested parity (or its negation, from 0 when `α`
has no root), the identity flag 0, and as the choice 1 exactly when `x < p` and
the root squares to `α`. It returns with the saved registers restored and
changes no memory outside its frame and `out`. -/
theorem p384Decompress_correct (m : Machine) {S inp out retAddr : Word} (C : DqCode m.mem) (D : DqData m.mem)
    (F : DqFrame S) (hpc : m.pc = DP) (hsp : reg m sp = S + 0xA50) (ha0 : reg m a0 = out) (ha1 : reg m a1 = inp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (sI : Sep inp 48 (S + 0xFFFFFE60) 0xBF0) (sO : Sep out 0x65 (S + 0xFFFFFE60) 0xBF0)
    (hO : out.toNat + 0x65 ≤ 0x40000000) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = S + 0xA50 ∧
      (∀ k, k < 13 → reg m' (savedReg k) = reg m (savedReg k)) ∧
      reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      (∃ ok X, XOk (beNat (memBytes m.mem inp 48)) ok X ∧ accV m'.mem out 12 = X ∧
        accV m'.mem (out + BitVec.ofNat 32 0x30) 12 = dqY (dqAlpha X) (reg m a2) ∧
        (∀ k, k < 4 → m'.mem (out + BitVec.ofNat 32 (0x60 + k)) = BitVec.ofNat 8 0) ∧
        m'.mem (out + BitVec.ofNat 32 0x64) =
          (if p3fm (dqSqrt (dqAlpha X)) (dqSqrt (dqAlpha X)) = dqAlpha X ∧ ok = 1 then 1 else 0)) ∧
      ∀ x, Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep out 0x65 x 1 → m'.mem x = m.mem x := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hbF : (S + 0xFFFFFF10).toNat = S.toNat - 0xF0 := F.below 0xF0 (by decide) (by decide)
  have hbA : (S + 0xFFFFFF60).toNat = S.toNat - 0xA0 := F.below 0xA0 (by decide) (by decide)
  have sq : ∀ c l d, c + l ≤ 0xA50 → d + 1 ≤ 0xA50 → (c + l ≤ d ∨ d + 1 ≤ c) →
      Sep (S + BitVec.ofNat 32 c) l (S + BitVec.ofNat 32 d) 1 := fun c l d h1 h2 h3 => sepS S h3 (by omega) (by omega)
  have below : ∀ {k : Nat} {B' : Word} {x : Word}, B'.toNat = S.toNat - k → 0 < k → k ≤ 0x1A0 →
      Sep (S + 0xFFFFFE60) 0xBF0 x 1 → Sep B' k x 1 := fun {k B' x} hB' hk hk' hx => by
    have hb1A : (S + 0xFFFFFE60).toNat = S.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := hx.sub (c := 0x1A0 - k) (l := k) (by omega)
    rwa [show S + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 - k) = B' by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hb1A, hB']; omega] at this
  have inFrame : ∀ {c l : Nat} {x : Word}, c + l ≤ 0xA50 → Sep (S + 0xFFFFFE60) 0xBF0 x 1 →
      Sep (S + BitVec.ofNat 32 c) l x 1 := fun {c l x} h hx => by
    have := hx.sub (c := 0x1A0 + c) (l := l) (by omega)
    rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + c) = BitVec.ofNat 32 c by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl]
      omega] at this
  have s0 : St m.mem DP m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨n1, c1, u1, C1, D1, hXo, hA1, hB1, h10, h18, hS1, R1, e13, e14, fr1⟩ := dq_toLoop C D F s0 hsp ha1 sI
  obtain ⟨ok, hok⟩ : ∃ ok, memLoad32 n1.mem (S + BitVec.ofNat 32 0x14) = ok := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, accV n1.mem (S + BitVec.ofNat 32 0xA4) 12 = X := ⟨_, rfl⟩
  rw [hok, hX] at hXo; rw [hX] at hA1 hB1
  have hok01 : ok = 0 ∨ ok = 1 := by
    rcases Nat.lt_or_ge (beNat (memBytes m.mem inp 48)) p384 with h | h
    · exact .inr (hXo.1 h).1
    · exact .inl (hXo.2 h).1
  obtain ⟨n2, c2, u2, C2, D2, hb2, e28, e219, e220, e221, sp2, hZ2, fr2, e23, e24⟩ :=
    dq_stG C1 D1 F u1 R1 hB1 (mpow_lt _ _) hA1
  obtain ⟨n3, c3, u3, C3, D3, hY3, hN3, ea3, e38, sp3, K3, fr3⟩ :=
    dq_stH C2 D2 F u2 sp2 e28 (ite01 _) hb2 (mpow_lt _ _)
  have keepH : ∀ d, d + 1 ≤ 0xA50 → (d + 1 ≤ 0xD4 ∨ 0x134 ≤ d) → (d + 1 ≤ 0x29C ∨ 0x32D ≤ d) →
      (d + 1 ≤ 0x62C ∨ 0x65D ≤ d) → n3.mem (S + BitVec.ofNat 32 d) = n2.mem (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 h3 h4 => fr3 _ (F.lowB hbA (by decide) h1) (sq _ _ _ (by decide) h1 h2.symm) (sq _ _ _ (by decide) h1 h3.symm)
      (sq _ _ _ (by decide) h1 h4.symm)
  have keepG : ∀ d, d + 1 ≤ 0xA50 → (d + 1 ≤ 0x1D0 ∨ 0x29C ≤ d) → (d + 1 ≤ 0x62C ∨ 0x6F8 ≤ d) →
      n2.mem (S + BitVec.ofNat 32 d) = n1.mem (S + BitVec.ofNat 32 d) :=
    fun d h1 h2 h3 => fr2 _ (F.lowB hbF (by decide) h1) (sq _ _ _ (by decide) h1 h2.symm) (sq _ _ _ (by decide) h1 h3.symm)
  have hX3 : accV n3.mem (S + BitVec.ofNat 32 0xA4) 12 = X := by
    rw [← hX]; exact accV_keep fun q hq => by
      rw [keepH _ (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)),
        keepG _ (by omega) (.inl (by omega)) (.inl (by omega))]
  have hS3 : ∀ k, k < 13 → memLoad32 n3.mem (S + BitVec.ofNat 32 (0xA4C - 4 * k)) = reg m (savedReg k) := fun k hk => by
    rw [← hS1 k hk]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, keepH _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)),
        keepG _ (by omega) (.inr (by omega)) (.inr (by omega))]
  have hZ3 : ∀ k, k < 3 → n3.mem (S + BitVec.ofNat 32 (0x68D + k)) = BitVec.ofNat 8 0 := fun k hk => by
    rw [keepH _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega))]; exact hZ2 k hk
  obtain ⟨n4, c4, pc4, sp4, sv4, hx4, hy4, hz4, hc4, e43, e44, fr4⟩ :=
    dq_stI (v := fun k => reg m (savedReg k)) C3 D3 F u3 sp3 ea3 (ite01 _) e38 (ite01 _)
      (by rw [K3 19 (by decide), e219, h18, ha0]) (by rw [K3 20 (by decide), e220, hok]) hok01 sO hO hX3 hY3 hN3 hZ3 hS3
      (by show reg m ra &&& ~~~1 = reg m ra; rw [hra]; exact hret)
  have hY0 : (if (if p3fm (mpow (dqAlpha X) sqrtExp) (mpow (dqAlpha X) sqrtExp) = dqAlpha X then (1 : Word) else 0) = 1
      then mpow (dqAlpha X) sqrtExp else 0) = dqY0 (dqAlpha X) := by
    unfold dqY0 dqSqrt
    by_cases h : p3fm (mpow (dqAlpha X) sqrtExp) (mpow (dqAlpha X) sqrtExp) = dqAlpha X
    · rw [ite_eq_left ((ite01_iff _).2 h), ite_eq_left h]
    · rw [ite_eq_right (fun e => h ((ite01_iff _).1 e)), ite_eq_right h]
  have y21 : reg n2 (21 : Fin 32) = reg m a2 := by rw [e221, h10]
  refine ⟨n4, c1.trans (c2.trans (c3.trans c4)), by rw [pc4]; exact hra, sp4, sv4, by rw [e43, K3 3 (by decide), e23, e13],
    by rw [e44, K3 4 (by decide), e24, e14], ⟨ok, X, hXo, hx4, ?_, hz4, ?_⟩, fun x hx ho => ?_⟩
  · rw [hy4, hY0, y21]
    unfold dqY
    by_cases h : p3fm (dqY0 (dqAlpha X)) 1 % 2 = (reg m a2).toNat % 2
    · rw [ite_eq_left ((ite01_iff _).2 h), ite_eq_left h]
    · rw [ite_eq_right (fun e => h ((ite01_iff _).1 e)), ite_eq_right h]
  · rw [hc4]
    unfold dqSqrt
    by_cases h : p3fm (mpow (dqAlpha X) sqrtExp) (mpow (dqAlpha X) sqrtExp) = dqAlpha X ∧ ok = 1
    · rw [ite_eq_left ⟨(ite01_iff _).2 h.1, h.2⟩, ite_eq_left h]
    · rw [ite_eq_right (fun e => h ⟨(ite01_iff _).1 e.1, e.2⟩), ite_eq_right h]
  · rw [fr4 x hx ho, fr3 x (below hbA (by decide) (by decide) hx) (inFrame (by decide) hx) (inFrame (by decide) hx)
      (inFrame (by decide) hx), fr2 x (below hbF (by decide) (by decide) hx) (inFrame (by decide) hx)
      (inFrame (by decide) hx), fr1 x hx]

end C3.RV32.Dq
