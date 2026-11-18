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

end C3.RV32.Dq
