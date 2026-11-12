import C3BootProofs.Proofs.Sha256LoopDecode

/-!
# `compress256`, compact backend: the straight-line blocks

One round (`kcRound`) and one schedule step (`kcSched`) of the 64-round
loop, as blocks, with what they compute in FIPS 180-4's terms.
-/

namespace C3.RV32

open C3.Image

theorem upd_app (f : Fin 32 → Word) (rd : Fin 32) (v : Word) (r : Fin 32) :
    upd f rd v r = if r.val = 0 then 0 else if r = rd then v else f r := rfl

theorem ev_add (a b : Word) : aluEval .add a b = a + b := rfl
theorem ev_xor (a b : Word) : aluEval .xor a b = a ^^^ b := rfl
theorem ev_and (a b : Word) : aluEval .and a b = a &&& b := rfl

theorem ev_rotr_lr {x : Word} {r l : Nat} (i j : Word) (hi : (i.toNat % 32 == r) = true)
    (hj : (j.toNat % 32 == l) = true) (hrl : (r + l == 32 && decide (0 < r) && decide (r < 32)) = true) :
    aluEval .or (aluEval .srl x i) (aluEval .sll x j) = rotrW x r := by
  show x >>> (i.toNat % 32) ||| x <<< (j.toNat % 32) = _
  rw [beq_iff_eq.mp hi, beq_iff_eq.mp hj]; exact rotr_or_lr x r l hrl

theorem ev_rotr_rl {x : Word} {r l : Nat} (i j : Word) (hi : (i.toNat % 32 == r) = true)
    (hj : (j.toNat % 32 == l) = true) (hrl : (r + l == 32 && decide (0 < r) && decide (r < 32)) = true) :
    aluEval .or (aluEval .sll x j) (aluEval .srl x i) = rotrW x r := by
  show x <<< (j.toNat % 32) ||| x >>> (i.toNat % 32) = _
  rw [beq_iff_eq.mp hi, beq_iff_eq.mp hj]; exact rotr_or_rl x r l hrl

theorem rnd_a (w : Nat → Word) (t : Nat) (v : Sha256.V8) :
    (Sha256.rnd w t v).a = (v.h + Sha256.bigSigma1 v.e + Sha256.ch v.e v.f v.g + Sha256.k[t]! + w t) +
      (Sha256.bigSigma0 v.a + Sha256.maj v.a v.b v.c) := rfl

theorem rnd_e (w : Nat → Word) (t : Nat) (v : Sha256.V8) :
    (Sha256.rnd w t v).e = v.d + (v.h + Sha256.bigSigma1 v.e + Sha256.ch v.e v.f v.g + Sha256.k[t]! + w t) := rfl

/-- One round, from 0x160 to 0x1E8: `T1` and `T2`, the new `a` in `a2` and
the new `e` in `a0`, and the working variables shifted down. -/
def kcRound : List BInstr :=
  [.aluImm .srl a2 (6 : Fin 32) 0x6, .aluImm .sll a3 (6 : Fin 32) 0x1A, .aluImm .srl a5 (6 : Fin 32) 0xB,
   .aluImm .sll a1 (6 : Fin 32) 0x15, .alu .or a2 a2 a3, .alu .or a1 a1 a5, .alu .xor a1 a1 a2,
   .aluImm .srl a2 (6 : Fin 32) 0x19, .aluImm .sll a3 (6 : Fin 32) 0x7,
   .aluImm .xor a5 (6 : Fin 32) 0xFFFFFFFF, .lw (9 : Fin 32) (7 : Fin 32) 0x0, .alu .or a2 a2 a3,
   .alu .and a3 (17 : Fin 32) a5, .alu .add a3 a3 (26 : Fin 32), .alu .and a5 (5 : Fin 32) (6 : Fin 32),
   .alu .xor a1 a1 a2, .alu .add a3 a3 a5, .alu .add a1 a1 a3, .alu .add a0 a0 (9 : Fin 32),
   .aluImm .srl a2 (30 : Fin 32) 0x2, .aluImm .sll a3 (30 : Fin 32) 0x1E, .aluImm .srl a5 (30 : Fin 32) 0xD,
   .aluImm .sll a4 (30 : Fin 32) 0x13, .alu .or a2 a2 a3, .alu .or a4 a4 a5, .alu .add a1 a1 a0,
   .alu .xor a2 a2 a4, .aluImm .srl a0 (30 : Fin 32) 0x16, .aluImm .sll a3 (30 : Fin 32) 0xA,
   .alu .or a0 a0 a3, .alu .xor a3 (29 : Fin 32) a6, .alu .and a3 a3 (30 : Fin 32),
   .alu .and a4 (29 : Fin 32) a6, .alu .xor a0 a0 a2, .alu .xor a3 a3 a4, .alu .add a2 a3 a0,
   .alu .add a0 a1 (25 : Fin 32), .alu .add a2 a2 a1, .aluImm .add (22 : Fin 32) (22 : Fin 32) 0x4,
   .aluImm .add (7 : Fin 32) (7 : Fin 32) 0x4, .alu .add (8 : Fin 32) x0 (28 : Fin 32),
   .alu .add (26 : Fin 32) x0 (17 : Fin 32), .alu .add (17 : Fin 32) x0 (5 : Fin 32),
   .alu .add (5 : Fin 32) x0 (6 : Fin 32), .alu .add (25 : Fin 32) x0 a6, .alu .add a6 x0 (29 : Fin 32),
   .alu .add (29 : Fin 32) x0 (30 : Fin 32)]

/-- The registers a round leaves alone. -/
def kcRoundKeep (q : Fin 32) : Bool := q.val ∉ [5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 22, 25, 26, 29]

section
set_option maxRecDepth 20000
theorem kcRound_end : blockEnd sha256CompressCode 0x160 kcRound = some 0x1E8 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem kcRound_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) {v : Sha256.V8}
    {w : Nat → Word} {t : Nat} (he : f 6 = v.e) (hf : f 5 = v.f) (hg : f 17 = v.g) (hh : f 26 = v.h)
    (ha : f 30 = v.a) (hb : f 29 = v.b) (hc : f a6 = v.c) (hd : f 25 = v.d) (hw : f a0 = w t)
    (hk : memLoad32 M (f 7 + 0) = Sha256.k[t]!) :
    (runBlock kcRound (M, f)).1 = M ∧
    (runBlock kcRound (M, f)).2 a2 = (Sha256.rnd w t v).a ∧
    (runBlock kcRound (M, f)).2 a0 = (Sha256.rnd w t v).e ∧
    (runBlock kcRound (M, f)).2 (29 : Fin 32) = v.a ∧ (runBlock kcRound (M, f)).2 a6 = v.b ∧
    (runBlock kcRound (M, f)).2 (25 : Fin 32) = v.c ∧ (runBlock kcRound (M, f)).2 (5 : Fin 32) = v.e ∧
    (runBlock kcRound (M, f)).2 (17 : Fin 32) = v.f ∧ (runBlock kcRound (M, f)).2 (26 : Fin 32) = v.g ∧
    (runBlock kcRound (M, f)).2 (8 : Fin 32) = f 28 ∧
    (runBlock kcRound (M, f)).2 (22 : Fin 32) = f 22 + 4 ∧
    (runBlock kcRound (M, f)).2 (7 : Fin 32) = f 7 + 4 ∧
    ∀ q, kcRoundKeep q = true → (runBlock kcRound (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, kcRound, upd_app, ↓reduceIte]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [ev_rotr_rl (x := f 6) (r := 11) (l := 21) 0xB 0x15 rfl rfl rfl, ev_rotr_lr (x := f 6) (r := 6) (l := 26) 0x6 0x1A rfl rfl rfl,
      ev_rotr_lr (x := f 6) (r := 25) (l := 7) 0x19 0x7 rfl rfl rfl, ev_rotr_lr (x := f 30) (r := 22) (l := 10) 0x16 0xA rfl rfl rfl,
      ev_rotr_lr (x := f 30) (r := 2) (l := 30) 0x2 0x1E rfl rfl rfl, ev_rotr_rl (x := f 30) (r := 13) (l := 19) 0xD 0x13 rfl rfl rfl]
    rw [xor_notMask]; simp only [ev_add, ev_xor, ev_and]
    rw [he, hf, hg, hh, ha, hb, hc, hw, hk, rnd_a, ← ktAt_def, bigSigma1_w, bigSigma0_w, ch_mask, Sha256.maj_alt]
    ac_rfl
  · rw [ev_rotr_rl (x := f 6) (r := 11) (l := 21) 0xB 0x15 rfl rfl rfl, ev_rotr_lr (x := f 6) (r := 6) (l := 26) 0x6 0x1A rfl rfl rfl,
      ev_rotr_lr (x := f 6) (r := 25) (l := 7) 0x19 0x7 rfl rfl rfl]
    rw [xor_notMask]; simp only [ev_add, ev_xor, ev_and]
    rw [he, hf, hg, hh, hd, hw, hk, rnd_e, ← ktAt_def, bigSigma1_w, ch_mask]
    ac_rfl
  · rw [← ha]; exact BitVec.zero_add _
  · rw [← hb]; exact BitVec.zero_add _
  · rw [← hc]; exact BitVec.zero_add _
  · rw [← he]; exact BitVec.zero_add _
  · rw [← hf]; exact BitVec.zero_add _
  · rw [← hg]; exact BitVec.zero_add _
  · exact BitVec.zero_add _
  · rfl
  · rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp only [h0, ite_false, pkeep_ne (r := 5) hq rfl, pkeep_ne (r := 7) hq rfl, pkeep_ne (r := 8) hq rfl,
        pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl,
        pkeep_ne (r := a3) hq rfl, pkeep_ne (r := a4) hq rfl, pkeep_ne (r := a5) hq rfl, pkeep_ne (r := a6) hq rfl,
        pkeep_ne (r := 17) hq rfl, pkeep_ne (r := 22) hq rfl, pkeep_ne (r := 25) hq rfl, pkeep_ne (r := 26) hq rfl,
        pkeep_ne (r := 29) hq rfl]

theorem kcRound_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h7 : (f 7 + 0).toNat % 4 = 0) : BlockOk base len kcRound (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, kcRound, upd, ↓reduceIte, and_true, true_and]
  exact h7

/-- The word slot for schedule index `n` in the 16-word window at `F + 0x2C`. -/
def kslot (F : Word) (n : Nat) : Word := F + BitVec.ofNat 32 (0x2C + 4 * (n % 16))

theorem and15_small : ∀ r, r < 16 → r &&& 15 = r := by decide

theorem and15 (x : Nat) : x &&& 15 = x % 16 := by
  have h1 : x &&& 15 ≤ 15 := Nat.and_le_right
  have e := Nat.and_mod_two_pow (a := x) (b := 15) (n := 4)
  rw [show (2 : Nat) ^ 4 = 16 from rfl, Nat.mod_eq_of_lt (show x &&& 15 < 16 by omega), show 15 % 16 = 15 from rfl,
    and15_small _ (Nat.mod_lt _ (by decide))] at e
  exact e

theorem and15_sll2 (n : Nat) : (BitVec.ofNat 32 n &&& 15) <<< 2 = BitVec.ofNat 32 (4 * (n % 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (15 : Word).toNat = 15 from rfl, and15, Nat.shiftLeft_eq]
  have : n % 2 ^ 32 % 16 = n % 16 := Nat.mod_mod_of_dvd n (by decide)
  rw [this]
  have h : n % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize n % 16 = r at h ⊢
  simp only [Nat.reducePow]
  omega

theorem slot_addr (F : Word) (n : Nat) :
    aluEval .add (aluEval .sll (aluEval .and (BitVec.ofNat 32 n) 15) 2) (F + BitVec.ofNat 32 0x2C) + 0 =
      kslot F n := by
  show ((BitVec.ofNat 32 n &&& 15) <<< ((2 : Word).toNat % 32)) + (F + BitVec.ofNat 32 0x2C) + 0 = _
  rw [show (2 : Word).toNat % 32 = 2 from rfl, and15_sll2, add_lit_zero, BitVec.add_comm, BitVec.add_assoc,
    ofNat_add_ofNat]
  rfl

theorem ev_add9 (t : Nat) : aluEval .add (BitVec.ofNat 32 t) 9 = BitVec.ofNat 32 (t + 9) := ofNat_add_ofNat t 9
theorem ev_add14 (t : Nat) : aluEval .add (BitVec.ofNat 32 t) 14 = BitVec.ofNat 32 (t + 14) := ofNat_add_ofNat t 14

/-- One schedule step, from 0xEE to 0x160, for round `t ≥ 16`: `W[t]` from
the window, into `a0` and over `W[t - 16]`'s slot. -/
def kcSched : List BInstr :=
  [.aluImm .and a0 (28 : Fin 32) 0xF, .aluImm .add a2 (8 : Fin 32) 0xE, .aluImm .sll a0 a0 0x2,
   .aluImm .and a2 a2 0xF, .alu .add a0 a0 (20 : Fin 32), .aluImm .sll a2 a2 0x2, .lw a0 a0 0x0,
   .alu .add a2 a2 (20 : Fin 32), .aluImm .and (9 : Fin 32) (8 : Fin 32) 0xF,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x9, .aluImm .sll (9 : Fin 32) (9 : Fin 32) 0x2,
   .aluImm .and (8 : Fin 32) (8 : Fin 32) 0xF, .alu .add (9 : Fin 32) (9 : Fin 32) (20 : Fin 32),
   .aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x2, .alu .add (8 : Fin 32) (8 : Fin 32) (20 : Fin 32),
   .lw a5 a2 0x0, .lw (31 : Fin 32) (9 : Fin 32) 0x0, .lw ra (8 : Fin 32) 0x0, .aluImm .srl a3 a0 0x7,
   .aluImm .sll a2 a0 0x19, .aluImm .srl (8 : Fin 32) a0 0x12, .aluImm .sll (23 : Fin 32) a0 0xE,
   .alu .or a3 a3 a2, .alu .or (23 : Fin 32) (23 : Fin 32) (8 : Fin 32), .aluImm .srl (8 : Fin 32) a5 0x11,
   .aluImm .sll a2 a5 0xF, .alu .xor a3 a3 (23 : Fin 32), .alu .or (23 : Fin 32) a2 (8 : Fin 32),
   .aluImm .srl (8 : Fin 32) a5 0x13, .aluImm .sll a2 a5 0xD, .alu .or a2 a2 (8 : Fin 32),
   .aluImm .srl a0 a0 0x3, .alu .xor a0 a0 a3, .alu .xor a2 (23 : Fin 32) a2, .aluImm .srl a5 a5 0xA,
   .alu .add (31 : Fin 32) (31 : Fin 32) ra, .alu .xor a2 a2 a5, .alu .add a0 a0 (31 : Fin 32),
   .alu .add a0 a0 a2, .sw (9 : Fin 32) a0 0x0]

/-- The registers a schedule step leaves alone. -/
def kcSchedKeep (q : Fin 32) : Bool := q.val ∉ [1, 8, 9, 10, 12, 13, 15, 23, 31]

section
set_option maxRecDepth 20000
theorem kcSched_end : blockEnd sha256CompressCode 0xEE kcSched = some 0x160 := by decide
end

set_option maxRecDepth 20000 in
theorem kcSched_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) {F : Word} {t : Nat}
    {w : Nat → Word} (h8 : f 8 = BitVec.ofNat 32 t) (h28 : f 28 = BitVec.ofNat 32 (t + 1))
    (h20 : f 20 = F + BitVec.ofNat 32 0x2C)
    (h15 : memLoad32 M (kslot F (t + 1)) = w (t - 15)) (h2 : memLoad32 M (kslot F (t + 14)) = w (t - 2))
    (h16 : memLoad32 M (kslot F t) = w (t - 16)) (h7 : memLoad32 M (kslot F (t + 9)) = w (t - 7))
    (hrec : w t = Sha256.smallSigma1 (w (t - 2)) + w (t - 7) + Sha256.smallSigma0 (w (t - 15)) + w (t - 16)) :
    (runBlock kcSched (M, f)).1 = memStore32 M (kslot F t) (w t) ∧
    (runBlock kcSched (M, f)).2 a0 = w t ∧
    ∀ q, kcSchedKeep q = true → (runBlock kcSched (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, kcSched, upd_app, ↓reduceIte]
  simp only [h8, h28, h20, ev_add9, ev_add14, slot_addr, h15, h2, h16, h7]
  refine ⟨?_, ?_, fun q hq => ?_⟩
  rotate_left 2
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp only [h0, ite_false, pkeep_ne (r := 1) hq rfl, pkeep_ne (r := 8) hq rfl, pkeep_ne (r := 9) hq rfl,
        pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl,
        pkeep_ne (r := a5) hq rfl, pkeep_ne (r := 23) hq rfl, pkeep_ne (r := 31) hq rfl]
  all_goals try congr 1
  all_goals
    rw [ev_rotr_lr (x := w (t - 15)) (r := 7) (l := 25) 0x7 0x19 rfl rfl rfl,
      ev_rotr_rl (x := w (t - 15)) (r := 18) (l := 14) 0x12 0xE rfl rfl rfl,
      ev_rotr_rl (x := w (t - 2)) (r := 17) (l := 15) 0x11 0xF rfl rfl rfl,
      ev_rotr_rl (x := w (t - 2)) (r := 19) (l := 13) 0x13 0xD rfl rfl rfl, shr3_eval, shr10_eval]
    simp only [ev_add, ev_xor]
    rw [hrec, s0_fold, s1_fold]
    ac_rfl

set_option maxRecDepth 20000 in
theorem kcSched_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F base : Word} {len t : Nat}
    (h8 : f 8 = BitVec.ofNat 32 t) (h28 : f 28 = BitVec.ofNat 32 (t + 1)) (h20 : f 20 = F + BitVec.ofNat 32 0x2C)
    (hal : ∀ n, (kslot F n).toNat % 4 = 0) (hsep : Sep (kslot F t) 4 base len) :
    BlockOk base len kcSched (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, kcSched, upd_app, ↓reduceIte, and_true, true_and]
  simp only [h8, h28, h20, ev_add9, ev_add14, slot_addr]
  exact ⟨hal _, hal _, hal _, hal _, hal _, hsep⟩

end C3.RV32
