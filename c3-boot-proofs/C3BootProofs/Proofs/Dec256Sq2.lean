import C3BootProofs.Proofs.Dec256Sq

/-!
# P-256 point decompression: one inlined Montgomery squaring

`gd_sq` runs one pass of `square_repeat_montgomery_form`'s loop in
`decompress`, from 0x322 to the loop's head at 0x31C: it squares the
working value at `S + 0x67C` in Montgomery form, through the copy at
`S + 0x69C`, the loop of `Dec256Sq.lean`, and the final subtraction.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2

set_option maxRecDepth 20000

def gdPre1 : List BInstr := [.aluImm .add a0 sp 0x69C, .aluImm .add a1 sp 0x67C, .aluImm .add a2 x0 0x20]
def gdPre2 : List BInstr := [.aluImm .add a0 sp 0x67C, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0]
def gdPre3 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x0, .aluImm .add (17 : Fin 32) x0 0x0, .lw a6 sp 0x69C,
   .aluImm .add (5 : Fin 32) x0 0x0]

theorem gdPre1_end : blockEnd p256DecompressCode 0x324 gdPre1 = some 0x330 := by decide
theorem gdPre2_end : blockEnd p256DecompressCode 0x338 gdPre2 = some 0x342 := by decide
theorem gdPre3_end : blockEnd p256DecompressCode 0x34A gdPre3 = some 0x354 := by decide

/-- The registers the start of a squaring leaves alone. -/
def gdPreKeep (q : Fin 32) : Bool := q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 20, 28, 29, 30]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The start of a squaring**, from 0x322 to the loop at 0x358: save the
count, copy the working value to the operand at `S + 0x69C`, and clear the
accumulator at `S + 0x67C`. -/
theorem gd_sq_pre {M : Word → BitVec 8} {S : Word} {n : Machine} {j : Nat} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0x322 (reg n)) (rsp : reg n sp = S) (ra1 : reg n a1 = BitVec.ofNat 32 j)
    (r27 : reg n (27 : Fin 32) = 8) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x358 (reg n') ∧ GdCode n'.mem ∧
      (∀ i, i < 8 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0x69C + 4 * i)) =
        memLoad32 M (S + BitVec.ofNat 32 (0x67C + 4 * i))) ∧
      (∀ i, i < 8 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0x67C + 4 * i)) = 0) ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x3C) = BitVec.ofNat 32 j ∧
      (∀ x, Sep (S + BitVec.ofNat 32 (2 ^ 32 - 16)) 16 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
        Sep (S + BitVec.ofNat 32 0x67C) 0x40 x 1 → n'.mem x = M x) ∧
      reg n' (20 : Fin 32) = 0 ∧ reg n' (17 : Fin 32) = 0 ∧ reg n' a6 = memLoad32 M (S + BitVec.ofNat 32 0x67C) ∧
      reg n' (5 : Fin 32) = 0 ∧ ∀ q, gdPreKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  -- save the count
  obtain ⟨n1, d1, u1⟩ := s.sw C.self gd_at_322 (off' := 0x324) (by decide)
    (by rw [rsp]; show (S + BitVec.ofNat 32 0x3C).toNat % 4 = 0; rw [F.at 0x3C (by decide)]; omega)
  rw [rsp, ra1] at u1
  have u1' : St (memStore32 M (S + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 j)) GD n1 0x324 (reg n1) := u1.self
  have h1hi : ∀ x : Word, 0x40000000 ≤ x.toNat → memStore32 M (S + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 j) x = M x :=
    fun x hx => memStore32_get_sep (F.hiOut (c := 0x3C) (n := 4) (by decide) hx)
  have C1 := C.hi h1hi
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 M (S + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 j) = M1 := ⟨_, rfl⟩
  rw [hM1] at u1' h1hi C1
  -- copy the working value
  obtain ⟨n2, c2, u2⟩ := u1'.block gdPre1 C1.self gdPre1_end ⟨trivial, trivial, trivial, trivial⟩
  have r2 : ∀ q, reg n2 q = (runBlock gdPre1 (M1, reg n1)).2 q := fun q => by rw [u2.regs]
  have sp1 : reg n1 sp = S := by rw [u1.regs, rsp]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n2 q = reg n q := fun q h0 h1 h2 => by
    rw [r2, runBlock_reg _ _ _ q u1'.zero (by simp only [gdPre1]; revert h0 h1 h2; revert q; decide), u1.regs]
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have dW : (S + BitVec.ofNat 32 0x69C).toNat + 32 < 2 ^ 32 := by rw [F.at 0x69C (by decide)]; omega
  have sW : (S + BitVec.ofNat 32 0x67C).toNat + 32 < 2 ^ 32 := by rw [F.at 0x67C (by decide)]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide)
  have hdF : Sep (S + BitVec.ofNat 32 0x69C) 32 (S + 0xFFFFFFF0) 16 :=
    (sep_of_le (by rw [hb16, F.at 0x69C (by decide)]; omega) (by omega)).symm
  have hsF : Sep (S + BitVec.ofNat 32 0x67C) 32 (S + 0xFFFFFFF0) 16 :=
    (sep_of_le (by rw [hb16, F.at 0x67C (by decide)]; omega) (by omega)).symm
  have below16 : ∀ c, c + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  obtain ⟨n3, c3, u3, fr3, k3⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x69C) (src := S + BitVec.ofNat 32 0x67C)
    (S := S) (N := 32) (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St M1 GD n2 0x330 (reg n2)) C1.self C1.K.K gd_at_330 gd_at_334
    (by decide) (by decide)
    (by rw [k2 sp (by decide) (by decide) (by decide)]; exact rsp)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdPre1, upd, ↓reduceIte]; rw [sp1]; try rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdPre1, upd, ↓reduceIte]; rw [sp1]; try rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, gdPre1, upd, ↓reduceIte]; (try rw [u1'.zero]); try rfl)
    ⟨C1.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, hdF, hsF,
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, dW, sW⟩
  have h3hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n3.mem x = M x := fun x hx => by
    rw [fr3 x (sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)),
      copyBytes_sep (F.hiOut (c := 0x69C) (n := 32) (by decide) hx) (Nat.le_refl _), h1hi x hx]
  have C3 := C.hi h3hi
  have k3' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n3 q = reg n q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      rw [k3 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, k2 q h0 h1 h2]
  -- clear the accumulator
  obtain ⟨n4, c4, u4⟩ := u3.block gdPre2 C3.self gdPre2_end ⟨trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock gdPre2 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have sp3 : reg n3 sp = S := by
    rw [k3' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rsp
  obtain ⟨n5, c5, u5, mem5, k5⟩ := c_memset (dst := S + BitVec.ofNat 32 0x67C) (b := 0) (N := 32)
    (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem GD n4 0x342 (reg n4)) C3.self C3.K.K gd_at_342 gd_at_346 (by decide) (by decide)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdPre2, upd, ↓reduceIte]; rw [sp3]; try rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdPre2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, gdPre2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    (by rw [F.at 0x67C (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h5hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n5.mem x = M x := fun x hx => by
    rw [mem5, fillBytes_sep (F.hiOut (c := 0x67C) (n := 32) (by decide) hx) (Nat.le_refl _), h3hi x hx]
  have C5 := C.hi h5hi
  have k5' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n5 q = reg n q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ gdPre2.filterMap BInstr.dst := by simp only [gdPre2]; revert h0 h1 h2; revert q; decide
      rw [k5 q h0 h2 h3 h4 h5 h6 hr, r4, runBlock_reg _ _ _ q u3.zero hb, k3' q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr]
  -- the operand copy and the cleared accumulator, read word by word
  have wcopy : ∀ i, i < 8 → memLoad32 n5.mem (S + BitVec.ofNat 32 (0x69C + 4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 (0x67C + 4 * i)) := fun i hi => by
    rw [mem5, fill_word_out (sepS S (c := 0x67C) (n := 32) (d := 0x69C + 4 * i) (k := 4) (.inl (by omega)) (by decide)
        (by omega)),
      load_frame fr3 (below16 _ (by omega)), ← add_ofNat_assoc S 0x69C (4 * i), cp_word (by omega) (by decide),
      add_ofNat_assoc, ← hM1,
      st32_word_out (sepS S (c := 0x3C) (n := 4) (d := 0x67C + 4 * i) (k := 4) (.inl (by omega)) (by decide) (by omega))]
  have wzero : ∀ i, i < 8 → memLoad32 n5.mem (S + BitVec.ofNat 32 (0x67C + 4 * i)) = 0 := fun i hi => by
    rw [mem5, ← add_ofNat_assoc S 0x67C (4 * i)]; exact fill_word0 (by omega) (by decide)
  have sp5 : reg n5 sp = S := by
    rw [k5' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rsp
  obtain ⟨n6, c6, u6⟩ := u5.block gdPre3 C5.self gdPre3_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdPre3]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp5]
    show (S + BitVec.ofNat 32 0x69C).toNat % 4 = 0
    rw [F.at _ (by decide)]
    omega)
  have r6 : ∀ q, reg n6 q = (runBlock gdPre3 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have t6 : St n5.mem GD n6 0x354 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
  have e22 : reg n6 (27 : Fin 32) = 8 := by
    rw [r6, runBlock_reg _ _ _ 27 u5.zero (by decide), k5' 27 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact r27
  obtain ⟨n7, d7, u7⟩ := t6.notTaken C5.self 0x358 gd_at_354 (by decide) (by
    show (reg n6 (27 : Fin 32) == reg n6 x0) = false; rw [e22, t6.zero]; rfl)
  refine ⟨n7, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (.single d7)))))),
    ⟨u7.pc, rfl, fun _ => rfl⟩, by rw [u7.mem]; exact C5, fun i hi => by rw [u7.mem]; exact wcopy i hi,
    fun i hi => by rw [u7.mem]; exact wzero i hi, ?_, fun x hx hj hw => ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [u7.mem, mem5, fill_word_out (sepS S (c := 0x67C) (n := 32) (d := 0x3C) (k := 4) (.inr (by decide)) (by decide)
        (by decide)),
      load_frame fr3 (below16 0x3C (by decide)),
      cp_word_out (sepS S (c := 0x69C) (n := 32) (d := 0x3C) (k := 4) (.inr (by decide)) (by decide) (by decide)),
      ← hM1, memLoad32_store32_same]
  · have e0 : S + BitVec.ofNat 32 0x67C + BitVec.ofNat 32 0 = S + BitVec.ofNat 32 0x67C := add_ofNat_zero _
    rw [u7.mem, mem5, fillBytes_sep (by have := hw.sub (c := 0) (l := 32) (by decide); rwa [e0] at this) (Nat.le_refl _),
      fr3 x hx, copyBytes_sep (by have := hw.sub (c := 0x20) (l := 32) (by decide); rwa [add_ofNat_assoc] at this)
        (Nat.le_refl _), ← hM1]
    exact memStore32_get_sep hj
  · rw [u7.regs, r6]; simp +decide only [runBlock, BInstr.run, gdPre3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl
  · rw [u7.regs, r6]; simp +decide only [runBlock, BInstr.run, gdPre3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl
  · rw [u7.regs, r6]; simp +decide only [runBlock, BInstr.run, gdPre3, upd, ↓reduceIte]
    rw [sp5]
    have := wcopy 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    show memLoad32 n5.mem (S + BitVec.ofNat 32 0x69C) = _
    exact this
  · rw [u7.regs, r6]; simp +decide only [runBlock, BInstr.run, gdPre3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl
  · have h0 : q ≠ a0 := pkeep_ne (r := a0) hq rfl
    have hb : q ∉ gdPre3.filterMap BInstr.dst := by simp only [gdPre3]; revert hq; revert q; decide
    rw [u7.regs, r6, runBlock_reg _ _ _ q u5.zero hb,
      k5' q h0 (pkeep_ne (r := a1) hq rfl) (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := a3) hq rfl)
        (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := a6) hq rfl)
        (pkeep_ne (r := a7) hq rfl) (pkeep_ne (r := t0) hq rfl) (pkeep_ne (r := t1) hq rfl)
        (pkeep_ne (r := 7) hq rfl) (pkeep_ne (r := 28) hq rfl) (pkeep_ne (r := 29) hq rfl)
        (pkeep_ne (r := 30) hq rfl) (pkeep_ne (r := ra) hq rfl)]

def gdP1 : List BInstr :=
  [.aluImm .add a0 sp 0x43C, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0, .aluImm .add (24 : Fin 32) sp 0x43C]
def gdP2 : List BInstr :=
  [.aluImm .add (26 : Fin 32) x0 0x0, .aluImm .add (8 : Fin 32) sp 0x67C, .aluImm .add (9 : Fin 32) x0 0x8,
   .aluImm .add (23 : Fin 32) sp 0xE4]
def gdP3 : List BInstr := [.aluImm .add a0 sp 0x6BC, .aluImm .add a1 sp 0x43C, .aluImm .add a2 x0 0x20]
def gdP4 : List BInstr :=
  [.sw sp (20 : Fin 32) 0x43C, .aluImm .add a1 sp 0x43C, .lw a0 sp 0x43C, .aluImm .sltu a0 a0 0x1,
   .alu .and (24 : Fin 32) a0 (26 : Fin 32), .sb sp (24 : Fin 32) 0x43C, .lbu a0 sp 0x43C, .aluImm .add a0 a0 0xFFFFFFFF,
   .alu .and a2 (26 : Fin 32) a0, .alu .add a0 x0 (20 : Fin 32), .aluImm .add a1 x0 0x0]
def gdP5 : List BInstr :=
  [.aluImm .add a0 sp 0x43C, .aluImm .add a1 sp 0x6BC, .aluImm .add a2 sp 0x67C, .alu .add a3 x0 (24 : Fin 32)]
def gdP6 : List BInstr := [.aluImm .add a0 sp 0x67C, .aluImm .add a1 sp 0x43C, .aluImm .add a2 x0 0x20]
def gdP7 : List BInstr := [.lw a1 sp 0x3C, .aluImm .add a1 a1 0x1]

theorem gdP1_end : blockEnd p256DecompressCode 0x404 gdP1 = some 0x412 := by decide
theorem gdP2_end : blockEnd p256DecompressCode 0x41A gdP2 = some 0x426 := by decide
theorem gdP3_end : blockEnd p256DecompressCode 0x448 gdP3 = some 0x454 := by decide
theorem gdP4_end : blockEnd p256DecompressCode 0x45C gdP4 = some 0x482 := by decide
theorem gdP5_end : blockEnd p256DecompressCode 0x48A gdP5 = some 0x498 := by decide
theorem gdP6_end : blockEnd p256DecompressCode 0x4A0 gdP6 = some 0x4AC := by decide
theorem gdP7_end : blockEnd p256DecompressCode 0x4B4 gdP7 = some 0x4B8 := by decide


/-- The registers the end of a squaring leaves alone. -/
def gdPostKeep (q : Fin 32) : Bool :=
  q.val ∉ [1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 23, 24, 26, 28, 29, 30, 31]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The end of a squaring**, from 0x404 to the loop's head at 0x31C: the
conditional subtraction of the modulus, which leaves at `S + 0x67C` the
accumulator when the top carry `s11` is zero and the subtraction borrowed,
and the difference otherwise. -/
theorem gd_sq_post {M : Word → BitVec 8} {S : Word} {n : Machine} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0x404 (reg n)) (rsp : reg n sp = S) :
    ∃ (n' : Machine) (Dv : Nat) (b : Word), Steps n n' ∧ St n'.mem GD n' 0x31C (reg n') ∧ GdCode n'.mem ∧
      (b = 0 ∨ b = 0xFFFFFFFF) ∧ Dv < 2 ^ 256 ∧
      accV M (S + BitVec.ofNat 32 0x67C) 8 + 2 ^ 256 * maskBit b = accV M (S + BitVec.ofNat 32 0xE4) 8 + Dv ∧
      accV n'.mem (S + BitVec.ofNat 32 0x67C) 8 =
        (if (reg n (20 : Fin 32)).toNat = 0 ∧ maskBit b = 1 then accV M (S + BitVec.ofNat 32 0x67C) 8 else Dv) ∧
      reg n' a1 = memLoad32 M (S + BitVec.ofNat 32 0x3C) + 1 ∧
      (∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 →
        Sep (S + BitVec.ofNat 32 0x67C) 32 x 1 → Sep (S + BitVec.ofNat 32 0x6BC) 32 x 1 → n'.mem x = M x) ∧
      ∀ q, gdPostKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb4 : (S + 0xFFFFFFFC).toNat = S.toNat - 4 := F.below 4 (by decide) (by decide)
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb40 : (S + 0xFFFFFFC0).toNat = S.toNat - 0x40 := F.below 0x40 (by decide) (by decide)
  have lowS : ∀ (c : Nat) (B : Word) (k : Nat), 0 < k → k ≤ 0x100 → B.toNat = S.toNat - k → ∀ d l, d + l ≤ 0x710 →
      Sep B k (S + BitVec.ofNat 32 d) l := fun c B k hk hk' hB d l hd =>
    sep_of_le (by rw [hB, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have hiB : ∀ (B : Word) (k : Nat), B.toNat + k ≤ S.toNat → ∀ x : Word, 0x40000000 ≤ x.toNat → Sep B k x 1 :=
    fun B k h x hx => sep_of_le (by omega) (by have := x.isLt; omega)
  -- clear the buffer at S + 0x43C
  obtain ⟨n1, c1, u1⟩ := s.block gdP1 C.self gdP1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gdP1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, mem2, k2⟩ := c_memset (dst := S + BitVec.ofNat 32 0x43C) (b := 0) (N := 32)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x412 (reg n1)) C.self C.K.K gd_at_412 gd_at_416 (by decide) (by decide)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdP1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdP1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdP1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    (by rw [F.at 0x43C (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  obtain ⟨M2, hM2⟩ : ∃ M2, fillBytes M (S + BitVec.ofNat 32 0x43C) ((0 : Word).extractLsb' 0 8) 32 = M2 := ⟨_, rfl⟩
  rw [hM2] at mem2
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M2 x = M x := fun x hx => by
    rw [← hM2, fillBytes_sep (F.hiOut (c := 0x43C) (n := 32) (by decide) hx) (Nat.le_refl _)]
  have C2 := C.hi h2hi
  have k2' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (24 : Fin 32) →
      reg n2 q = reg n q := fun q h0 h1 h2 h3 h4 h5 h6 hr h24 => by
    have hb : q ∉ gdP1.filterMap BInstr.dst := by simp only [gdP1]; revert h0 h1 h2 h24; revert q; decide
    rw [k2 q h0 h2 h3 h4 h5 h6 hr, r1, runBlock_reg _ _ _ q hz hb]
  have e24 : reg n2 (24 : Fin 32) = S + BitVec.ofNat 32 0x43C := by
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r1]
    simp +decide only [runBlock, BInstr.run, gdP1, upd, ↓reduceIte]; rw [rsp]; rfl
  have sp2 : reg n2 sp = S := by
    rw [k2' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact rsp
  -- the subtraction
  have u2' : St M2 GD n2 0x41A (reg n2) := ⟨u2.pc, mem2, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := u2'.block gdP2 C2.self gdP2_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gdP2 (M2, reg n2)).2 q := fun q => by rw [u3.regs]
  have t3 : St M2 GD n3 0x426 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have e9 : reg n3 (9 : Fin 32) = 8 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, gdP2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl
  obtain ⟨n4, d4, u4⟩ := t3.notTaken C2.self 0x428 gd_at_426 (by decide) (by
    show (reg n3 (9 : Fin 32) == reg n3 x0) = false; rw [e9, t3.zero]; rfl)
  have k3 : ∀ q, q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (23 : Fin 32) → q ≠ (26 : Fin 32) → reg n4 q = reg n2 q :=
    fun q h8 h9 h18 h20 => by
      have hb : q ∉ gdP2.filterMap BInstr.dst := by simp only [gdP2]; revert h8 h9 h18 h20; revert q; decide
      rw [u4.regs, r3, runBlock_reg _ _ _ q u2.zero hb]
  have sB : Sep (S + 0xFFFFFFFC) 4 BSUB borrowingSubCode.length :=
    sep_of_le (by rw [hb4, show BSUB.toNat = 0x403a2320 from rfl]; omega) (by decide)
  have sFC : Sep (S + 0xFFFFFFFC) 4 GD p256DecompressCode.length :=
    sep_of_le (by rw [hb4, show GD.toNat = 0x403a5fdc from rfl]; omega) (by decide)
  obtain ⟨n5, M5, c5, u5, hc5, hbs5, fr5, hm5, hv5, sp5, k5⟩ := gd_sub_loop (F := S) (acc := S + BitVec.ofNat 32 0x67C)
    (np := S + BitVec.ofNat 32 0xE4) (D := S + BitVec.ofNat 32 0x43C) (M0 := M2) (by omega)
    (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)
    (by rw [F.at _ (by decide)]; omega)
    (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide)) (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide))
    (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide))
    (sepS S (.inl (by decide)) (by decide) (by decide)) (sepS S (.inr (by decide)) (by decide) (by decide))
    sB sFC (F.sepHi (by decide) (by decide) (by decide)) (F.sepHi (by decide) (by decide) (by decide))
    7 0 (by decide) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St M2 GD n4 0x428 (reg n4)) C2.self C2.K.K.bsub (fun _ _ _ => rfl)
    (.inl rfl) (by simp [accV, maskBit])
    (by rw [k3 sp (by decide) (by decide) (by decide) (by decide)]; exact sp2)
    (by rw [Nat.mul_zero, add_ofNat_zero, u4.regs, r3]; simp +decide only [runBlock, BInstr.run, gdP2, upd, ↓reduceIte]
        rw [sp2]; rfl)
    (by rw [Nat.mul_zero, add_ofNat_zero, u4.regs, r3]; simp +decide only [runBlock, BInstr.run, gdP2, upd, ↓reduceIte]
        rw [sp2]; rfl)
    (by rw [Nat.mul_zero, add_ofNat_zero, k3 24 (by decide) (by decide) (by decide) (by decide), e24])
    (by rw [u4.regs, e9]; rfl)
    (by rw [u4.regs, r3]; simp +decide only [runBlock, BInstr.run, gdP2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
  have lo4 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFFC) 4 x 1 := fun x hx =>
    hiB _ 4 (by rw [hb4]; omega) x hx
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    hiB _ 16 (by rw [hb16]; omega) x hx
  have lo50 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFC0) 0x40 x 1 := fun x hx =>
    hiB _ 0x40 (by rw [hb40]; omega) x hx
  have h5hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M5 x = M x := fun x hx => by
    rw [fr5 x (lo4 x hx) (F.hiOut (c := 0x43C) (n := 32) (by decide) hx), h2hi x hx]
  have C5 := C.hi h5hi
  have s27 : reg n5 (20 : Fin 32) = reg n (20 : Fin 32) := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), k3 _ (by decide) (by decide) (by decide) (by decide),
      k2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  -- copy the difference to S + 0x6BC
  obtain ⟨n6, c6, u6⟩ := u5.block gdP3 hc5 gdP3_end ⟨trivial, trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock gdP3 (M5, reg n5)).2 q := fun q => by rw [u6.regs]
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide)
  have b16 : ∀ c, c + 32 ≤ 0x710 → Sep (S + BitVec.ofNat 32 c) 32 (S + 0xFFFFFFF0) 16 := fun c hc =>
    (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have w48 : ∀ c, c + 32 ≤ 0x710 → (S + BitVec.ofNat 32 c).toNat + 32 < 2 ^ 32 := fun c hc => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n7, c7, u7, fr7, k7⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x6BC) (src := S + BitVec.ofNat 32 0x43C)
    (S := S) (N := 32) (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St M5 GD n6 0x454 (reg n6)) C5.self C5.K.K gd_at_454 gd_at_458
    (by decide) (by decide) (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdP3, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdP3, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, gdP3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    ⟨C5.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have h7hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n7.mem x = M x := fun x hx => by
    rw [fr7 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x6BC) (n := 32) (by decide) hx) (Nat.le_refl _), h5hi x hx]
  have C7 := C.hi h7hi
  have k7' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n7 q = reg n5 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ gdP3.filterMap BInstr.dst := by simp only [gdP3]; revert h0 h1 h2; revert q; decide
      rw [k7 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r6, runBlock_reg _ _ _ q u5.zero hb]
  have sp7 : reg n7 sp = S := by
    rw [k7' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp5
  -- the choice
  obtain ⟨mc, hmc⟩ : ∃ mc, reg n (20 : Fin 32) = mc := ⟨_, rfl⟩
  obtain ⟨bw, hbw⟩ : ∃ bw, reg n5 (26 : Fin 32) = bw := ⟨_, rfl⟩
  rw [hbw] at hm5 hv5
  have e27 : reg n7 (20 : Fin 32) = mc := by
    rw [k7' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s27, hmc]
  have e20 : reg n7 (26 : Fin 32) = bw := by
    rw [k7' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbw]
  obtain ⟨cc, hcc⟩ : ∃ cc, aluEval .and (aluEval .sltu mc 1) bw = cc := ⟨_, rfl⟩
  have hcv := choice_val mc bw hm5
  rw [hcc] at hcv
  have hc01 : cc = 0 ∨ cc = 1 := by
    rw [hcv]; by_cases h : mc.toNat = 0 ∧ maskBit bw = 1
    · rw [ite_eq_left h]; exact .inr rfl
    · rw [ite_eq_right h]; exact .inl rfl
  have u7' : St n7.mem GD n7 0x45C (reg n7) := u7
  have a62C : (S + BitVec.ofNat 32 0x43C).toNat % 4 = 0 := by rw [F.at _ (by decide)]; omega
  obtain ⟨n8, c8, u8⟩ := u7'.block gdP4 C7.self gdP4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdP4]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp7]
    exact ⟨⟨a62C, F.sepHi (by decide) (by decide) (by decide)⟩, a62C, F.sepHi (by decide) (by decide) (by decide)⟩)
  have r8 : ∀ q, reg n8 q = (runBlock gdP4 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have m8 : n8.mem = memStore8 (memStore32 n7.mem (S + BitVec.ofNat 32 0x43C) mc) (S + BitVec.ofNat 32 0x43C)
      (cc.extractLsb' 0 8) := by
    rw [u8.mem]; simp +decide only [runBlock, BInstr.run, gdP4, upd, ↓reduceIte]
    rw [sp7, e27, e20, memLoad32_store32_same, ← hcc]; rfl
  have v24 : reg n8 (24 : Fin 32) = cc := by
    rw [r8]; simp +decide only [runBlock, BInstr.run, gdP4, upd, ↓reduceIte]
    rw [sp7, e27, e20, memLoad32_store32_same, ← hcc]
  have k8 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (24 : Fin 32) → reg n8 q = reg n7 q := fun q h0 h1 h2 h24 => by
    have hb : q ∉ gdP4.filterMap BInstr.dst := by simp only [gdP4]; revert h0 h1 h2 h24; revert q; decide
    rw [r8, runBlock_reg _ _ _ q u7'.zero hb]
  have hc8 : CodeIn n8.mem GD p256DecompressCode := by
    rw [m8]; exact CodeIn.store8 (CodeIn.store32 C7.self (F.sepHi (by decide) (by decide) (by decide)))
      (F.sepHi (by decide) (by decide) (by decide))
  have h8hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n8.mem x = M x := fun x hx => by
    rw [m8, memStore8_ne (fun e => (F.hiOut (c := 0x43C) (n := 1) (by decide) hx) 0 (by decide) 0 (by decide)
      (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (F.hiOut (c := 0x43C) (n := 4) (by decide) hx), h7hi x hx]
  have C8 := C.hi h8hi
  -- borrowing_sub, whose result goes unused
  obtain ⟨n9, c9, u9, _, _, sp9, fr9, mem9⟩ := (⟨u8.pc, rfl, fun _ => rfl⟩ : St n8.mem GD n8 0x482 (reg n8)).bsubCall
    C8.self C8.K.K.bsub (by decide) gd_at_482 gd_at_486 (by decide) (by decide)
    (by rw [k8 sp (by decide) (by decide) (by decide) (by decide)]; exact sp7) (by omega) sB
  have h9hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n9.mem x = M x := fun x hx => by
    rw [mem9 x (lo4 x hx), h8hi x hx]
  have C9 := C.hi h9hi
  have k9 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (24 : Fin 32) → reg n9 q = reg n7 q :=
    fun q h0 h1 h2 h3 h4 hr h24 => by rw [fr9 q h0 h1 h2 h3 h4 hr, k8 q h0 h1 h2 h24]
  have e24' : reg n9 (24 : Fin 32) = cc := by rw [fr9 _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), v24]
  -- select into S + 0x43C, then copy it to the accumulator
  obtain ⟨n10, c10, u10⟩ := u9.block gdP5 C9.self gdP5_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock gdP5 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  obtain ⟨n11, c11, u11, vals, fr11, sp11x, k11⟩ := c2_sel (out := S + BitVec.ofNat 32 0x43C)
    (ap := S + BitVec.ofNat 32 0x6BC) (bp := S + BitVec.ofNat 32 0x67C) (c := cc) (S := S)
    (⟨u10.pc, u10.mem, fun _ => rfl⟩ : St n9.mem GD n10 0x498 (reg n10)) C9.self C9.K F gd_at_498 gd_at_49c (by decide) (by decide)
    (by rw [r10, runBlock_reg _ _ _ sp u9.zero (by decide)]; exact sp9)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, gdP5, upd, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, gdP5, upd, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, gdP5, upd, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, gdP5, upd, ↓reduceIte]; rw [e24']
        exact BitVec.zero_add _)
    hc01 (by decide) (by decide) (by decide) rfl rfl rfl (by decide) (by decide) (by decide)
  have h11hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n11.mem x = M x := fun x hx => by
    rw [fr11 x (lo50 x hx) (F.hiOut (c := 0x43C) (n := 32) (by decide) hx), h9hi x hx]
  have C11 := C.hi h11hi
  have k11' : ∀ q, sel8Keep q = true → q ≠ ra → reg n11 q = reg n9 q := fun q hq hr => by
    have hb : q ∉ gdP5.filterMap BInstr.dst := by simp only [gdP5]; revert hq; revert q; decide
    rw [k11 q hq hr, r10, runBlock_reg _ _ _ q u9.zero hb]
  have sp11 : reg n11 sp = S := by rw [k11' sp rfl (by decide)]; exact sp9
  obtain ⟨n12, c12, u12⟩ := u11.block gdP6 C11.self gdP6_end ⟨trivial, trivial, trivial, trivial⟩
  have r12 : ∀ q, reg n12 q = (runBlock gdP6 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  obtain ⟨n13, c13, u13, fr13, k13⟩ := c_memcpy (dst := S + BitVec.ofNat 32 0x67C) (src := S + BitVec.ofNat 32 0x43C)
    (S := S) (N := 32) (⟨u12.pc, u12.mem, fun _ => rfl⟩ : St n11.mem GD n12 0x4AC (reg n12)) C11.self C11.K.K gd_at_4ac gd_at_4b0
    (by decide) (by decide) (by rw [r12, runBlock_reg _ _ _ sp u11.zero (by decide)]; exact sp11)
    (by rw [r12]; simp +decide only [runBlock, BInstr.run, gdP6, upd, ↓reduceIte]; rw [sp11]; rfl)
    (by rw [r12]; simp +decide only [runBlock, BInstr.run, gdP6, upd, ↓reduceIte]; rw [sp11]; rfl)
    (by rw [r12]; simp +decide only [runBlock, BInstr.run, gdP6, upd, ↓reduceIte]; (try rw [u11.zero]); try rfl)
    ⟨C11.K.K.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have h13hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n13.mem x = M x := fun x hx => by
    rw [fr13 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x67C) (n := 32) (by decide) hx) (Nat.le_refl _),
      h11hi x hx]
  have C13 := C.hi h13hi
  have k13' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n13 q = reg n11 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ gdP6.filterMap BInstr.dst := by simp only [gdP6]; revert h0 h1 h2; revert q; decide
      rw [k13 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r12, runBlock_reg _ _ _ q u11.zero hb]
  have sp13 : reg n13 sp = S := by
    rw [k13' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp11
  -- the frame, through each step
  have frame : ∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 →
      Sep (S + BitVec.ofNat 32 0x67C) 32 x 1 → Sep (S + BitVec.ofNat 32 0x6BC) 32 x 1 → n13.mem x = M x := by
    intro x h50 h62 h98 h9E
    have h16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
      have := h50.sub (c := 0x30) (l := 16) (by decide)
      rwa [show S + 0xFFFFFFC0 + BitVec.ofNat 32 0x30 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
    have h4 : Sep (S + 0xFFFFFFFC) 4 x 1 := by
      have := h50.sub (c := 0x3C) (l := 4) (by decide)
      rwa [show S + 0xFFFFFFC0 + BitVec.ofNat 32 0x3C = S + 0xFFFFFFFC by rw [BitVec.add_assoc]; rfl] at this
    rw [fr13 x h16, copyBytes_sep h98 (Nat.le_refl _), fr11 x h50 h62, mem9 x h4, m8,
      memStore8_ne (fun e => h62 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (h62.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
      fr7 x h16, copyBytes_sep h9E (Nat.le_refl _), fr5 x h4 h62, ← hM2, fillBytes_sep h62 (Nat.le_refl _)]
  -- the accumulator, word by word
  have below16 : ∀ c, c + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  have below4 : ∀ c, c + 4 ≤ 0x710 → Sep (S + 0xFFFFFFFC) 4 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb4, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  have below50 : ∀ c, c + 4 ≤ 0x710 → Sep (S + 0xFFFFFFC0) 0x40 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb40, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  have n9acc : ∀ i, i < 8 → memLoad32 n9.mem (S + BitVec.ofNat 32 0x67C + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 0x67C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [add_ofNat_assoc, load_frame mem9 (below4 _ (by omega)), m8, ld_ofNat, ld_ofNat]
    have h62 : ∀ j, j < 4 → Sep (S + BitVec.ofNat 32 0x43C) 4 (S + BitVec.ofNat 32 (0x67C + 4 * i) + BitVec.ofNat 32 j) 1 :=
      fun j hj => by rw [add_ofNat_assoc]; exact sepS S (.inl (by omega)) (by decide) (by omega)
    rw [memStore8_ne (fun e => (h62 3 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 2 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 1 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 0 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (h62 3 (by decide)), memStore32_get_sep (h62 2 (by decide)),
      memStore32_get_sep (h62 1 (by decide)), memStore32_get_sep (h62 0 (by decide)), ← ld_ofNat, ← ld_ofNat,
      load_frame fr7 (below16 _ (by omega)),
      cp_word_out (sepS S (c := 0x6BC) (n := 32) (d := 0x67C + 4 * i) (k := 4) (.inr (by omega)) (by decide) (by omega)),
      load_frame2 fr5 (below4 _ (by omega)) (sepS S (c := 0x43C) (n := 32) (d := 0x67C + 4 * i) (k := 4)
        (.inl (by omega)) (by decide) (by omega)), ← hM2,
      fill_word_out (sepS S (c := 0x43C) (n := 32) (d := 0x67C + 4 * i) (k := 4) (.inl (by omega)) (by decide) (by omega))]
  have n9d : ∀ i, i < 8 → memLoad32 n9.mem (S + BitVec.ofNat 32 0x6BC + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M5 (S + BitVec.ofNat 32 0x43C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [add_ofNat_assoc, load_frame mem9 (below4 _ (by omega)), m8, ld_ofNat, ld_ofNat]
    have h62 : ∀ j, j < 4 → Sep (S + BitVec.ofNat 32 0x43C) 4 (S + BitVec.ofNat 32 (0x6BC + 4 * i) + BitVec.ofNat 32 j) 1 :=
      fun j hj => by rw [add_ofNat_assoc]; exact sepS S (.inl (by omega)) (by decide) (by omega)
    rw [memStore8_ne (fun e => (h62 3 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 2 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 1 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 0 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (h62 3 (by decide)), memStore32_get_sep (h62 2 (by decide)),
      memStore32_get_sep (h62 1 (by decide)), memStore32_get_sep (h62 0 (by decide)), ← ld_ofNat, ← ld_ofNat,
      load_frame fr7 (below16 _ (by omega)), ← add_ofNat_assoc, cp_word (by omega) (by decide)]
  have n13acc : ∀ i, i < 8 → memLoad32 n13.mem (S + BitVec.ofNat 32 0x67C + BitVec.ofNat 32 (4 * i)) =
      if cc = 1 then memLoad32 M (S + BitVec.ofNat 32 0x67C + BitVec.ofNat 32 (4 * i))
      else memLoad32 M5 (S + BitVec.ofNat 32 0x43C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [load_frame fr13 (by rw [add_ofNat_assoc]; exact below16 _ (by omega)), cp_word (by omega) (by decide),
      vals i hi, n9acc i hi, n9d i hi]
  -- reload the count and loop
  have a3C : (S + BitVec.ofNat 32 0x3C).toNat % 4 = 0 := by rw [F.at _ (by decide)]; omega
  obtain ⟨n14, c14, u14⟩ := u13.block gdP7 C13.self gdP7_end (by
    simp only [BlockOk, BInstr.ok, gdP7]
    simp +decide only [and_true]
    rw [sp13]; exact a3C)
  have r14 : ∀ q, reg n14 q = (runBlock gdP7 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
  have t14 : St n13.mem GD n14 0x4B8 (reg n14) := ⟨u14.pc, u14.mem, fun _ => rfl⟩
  obtain ⟨n15, d15, u15⟩ := t14.jump C13.self gd_at_4b8 (off' := 0x31C) (by decide) (by rw [t14.pc]; decide)
  have s3C : ∀ c, c + 32 ≤ 0x710 → 0x3C + 4 ≤ c → Sep (S + BitVec.ofNat 32 c) 32 (S + BitVec.ofNat 32 0x3C) 4 :=
    fun c h1 h2 => sepS S (.inr (by omega)) (by omega) (by decide)
  have h3C : memLoad32 n13.mem (S + BitVec.ofNat 32 0x3C) = memLoad32 M (S + BitVec.ofNat 32 0x3C) :=
    memLoad32_congr fun j hj => frame _ ((below50 0x3C (by decide)).subR (c := j) (l := 1) (by omega))
      ((s3C 0x43C (by decide) (by decide)).subR (c := j) (l := 1) (by omega))
      ((s3C 0x67C (by decide) (by decide)).subR (c := j) (l := 1) (by omega))
      ((s3C 0x6BC (by decide) (by decide)).subR (c := j) (l := 1) (by omega))
  have hdv : accV M5 (S + BitVec.ofNat 32 0x43C) 8 < 2 ^ 256 := accV_lt M5 _ 8
  have sA : ∀ d, d + 4 ≤ 0x43C → Sep (S + BitVec.ofNat 32 0x43C) 32 (S + BitVec.ofNat 32 d) 4 :=
    fun d hd => sepS S (.inr (by omega)) (by decide) (by omega)
  have sA' : ∀ d, 0x43C + 32 ≤ d → d + 4 ≤ 0x710 → Sep (S + BitVec.ofNat 32 0x43C) 32 (S + BitVec.ofNat 32 d) 4 :=
    fun d hd hd' => sepS S (.inl (by omega)) (by decide) (by omega)
  have eA : accV M2 (S + BitVec.ofNat 32 0x67C) 8 = accV M (S + BitVec.ofNat 32 0x67C) 8 :=
    accV_congr2 8 fun i hi => by
      rw [← hM2, add_ofNat_assoc, fill_word_out (sA' _ (by omega) (by omega))]
  have eN : accV M2 (S + BitVec.ofNat 32 0xE4) 8 = accV M (S + BitVec.ofNat 32 0xE4) 8 :=
    accV_congr2 8 fun i hi => by
      rw [← hM2, add_ofNat_assoc, fill_word_out (sA _ (by omega))]
  rw [eA, eN] at hv5
  refine ⟨n15, accV M5 (S + BitVec.ofNat 32 0x43C) 8, bw,
    c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (c11.trans
      (c12.trans (c13.trans (c14.trans (.single d15)))))))))))))),
    ⟨u15.pc, by rw [u15.mem], fun _ => rfl⟩, by rw [u15.mem]; exact C13, hm5, hdv, hv5, ?_, ?_, ?_, ?_⟩
  · rw [u15.mem, hmc]
    by_cases hcd : mc.toNat = 0 ∧ maskBit bw = 1
    · rw [ite_eq_left hcd]
      have h1 : cc = 1 := by rw [hcv, ite_eq_left hcd]
      exact accV_congr2 8 fun i hi => by rw [n13acc i hi, ite_eq_left h1]
    · rw [ite_eq_right hcd]
      have h0 : cc ≠ 1 := by rw [hcv, ite_eq_right hcd]; decide
      exact accV_congr2 8 fun i hi => by rw [n13acc i hi, ite_eq_right h0]
  · rw [u15.regs, r14]; simp +decide only [runBlock, BInstr.run, gdP7, upd, ↓reduceIte]
    rw [sp13]; show aluEval .add (memLoad32 n13.mem (S + BitVec.ofNat 32 0x3C)) 1 = _; rw [h3C]; rfl
  · intro x h50 h62 h98 h9E; rw [u15.mem]; exact frame x h50 h62 h98 h9E
  · intro q hq
    have hb14 : q ∉ gdP7.filterMap BInstr.dst := by simp only [gdP7]; revert hq; revert q; decide
    have ne : ∀ r : Fin 32, gdPostKeep r = false → q ≠ r := fun r hr => pkeep_ne hq hr
    rw [u15.regs, r14, runBlock_reg _ _ _ q u13.zero hb14,
      k13' q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl) (ne a7 rfl)
        (ne t0 rfl) (ne t1 rfl) (ne 7 rfl) (ne 28 rfl) (ne 29 rfl) (ne 30 rfl) (ne ra rfl),
      k11' q (by revert hq; revert q; decide) (ne ra rfl),
      k9 q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne ra rfl) (ne 24 rfl),
      k7' q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl) (ne a7 rfl)
        (ne t0 rfl) (ne t1 rfl) (ne 7 rfl) (ne 28 rfl) (ne 29 rfl) (ne 30 rfl) (ne ra rfl),
      k5 q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne ra rfl) (ne 8 rfl) (ne 23 rfl)
        (ne 24 rfl) (ne 9 rfl) (ne 26 rfl),
      k3 q (ne 8 rfl) (ne 9 rfl) (ne 23 rfl) (ne 26 rfl),
      k2' q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl) (ne ra rfl) (ne 24 rfl)]


/-- The registers a squaring leaves alone. -/
def gdSqKeep (q : Fin 32) : Bool := q.val ∈ [2, 3, 4, 18, 19, 21, 22, 25, 27]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **One squaring in Montgomery form**, from 0x322 to the loop's head at
0x31C: for the working value `W < N` at `S + 0x67C` and the modulus `N`
at `S + 0xE4`, it leaves `R < N` at `S + 0x67C` with
`R · 2³⁸⁴ ≡ W · W (mod N)`, and counts the pass in `a1`. -/
theorem gd_sq {M : Word → BitVec 8} {S : Word} {n : Machine} {j : Nat} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0x322 (reg n)) (rsp : reg n sp = S) (ra1 : reg n a1 = BitVec.ofNat 32 j)
    (r27 : reg n (27 : Fin 32) = 8)
    (r18 : reg n (18 : Fin 32) = S + BitVec.ofNat 32 0x69C) (r22 : reg n (22 : Fin 32) = 0xFFFFFFFF)
    (r21 : reg n (21 : Fin 32) = S + BitVec.ofNat 32 0xE8) (r25 : reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x680)
    (r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x6A0)
    (hN0 : memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF)
    (hW : accV M (S + BitVec.ofNat 32 0x67C) 8 < accV M (S + BitVec.ofNat 32 0xE4) 8) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x31C (reg n') ∧ GdCode n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x67C) 8 < accV M (S + BitVec.ofNat 32 0xE4) 8 ∧
      accV n'.mem (S + BitVec.ofNat 32 0x67C) 8 * 2 ^ 256 % accV M (S + BitVec.ofNat 32 0xE4) 8 =
        accV M (S + BitVec.ofNat 32 0x67C) 8 * accV M (S + BitVec.ofNat 32 0x67C) 8 %
          accV M (S + BitVec.ofNat 32 0xE4) 8 ∧
      reg n' a1 = BitVec.ofNat 32 j + 1 ∧
      (∀ x, Sep (S + 0xFFFFFFC0) 0x40 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
        Sep (S + BitVec.ofNat 32 0x43C) 32 x 1 → Sep (S + BitVec.ofNat 32 0x67C) 0x60 x 1 → n'.mem x = M x) ∧
      ∀ q, gdSqKeep q = true → reg n' q = reg n q := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1, C1, wcopy, wzero, w3C, fr1, e27, e17, e16, e5, k1⟩ :=
    gd_sq_pre (j := j) C F s rsp ra1 r27
  have k1' : ∀ q, gdSqKeep q = true → reg n1 q = reg n q := fun q hq => k1 q (by revert hq; revert q; decide)
  have sep98 : ∀ d, d + 4 ≤ 0x710 → (0x67C + 0x40 ≤ d ∨ d + 4 ≤ 0x67C) →
      Sep (S + BitVec.ofNat 32 0x67C) 0x40 (S + BitVec.ofNat 32 d) 4 :=
    fun d h1 h2 => sepS S h2 (by decide) (by omega)
  have hb16 : (S + BitVec.ofNat 32 (2 ^ 32 - 16)).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + BitVec.ofNat 32 (2 ^ 32 - 16)) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have nfr : ∀ i, i < 8 → memLoad32 n1.mem (S + BitVec.ofNat 32 (0xE4 + 4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 (0xE4 + 4 * i)) := fun i hi =>
    memLoad32_congr fun q hq => fr1 _ ((lo16 _ (by omega)).subR (c := q) (l := 1) (by omega))
      ((sepS S (c := 0x3C) (n := 4) (d := 0xE4 + 4 * i) (k := 4) (.inl (by omega)) (by decide) (by omega)).subR
        (c := q) (l := 1) (by omega))
      ((sep98 _ (by omega) (.inr (by omega))).subR (c := q) (l := 1) (by omega))
  have eN : accV n1.mem (S + BitVec.ofNat 32 0xE4) 8 = accV M (S + BitVec.ofNat 32 0xE4) 8 :=
    accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, nfr i hi]
  have eX : accV n1.mem (S + BitVec.ofNat 32 0x69C) 8 = accV M (S + BitVec.ofNat 32 0x67C) 8 :=
    accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, add_ofNat_assoc, wcopy i hi]
  have eA0 : accV n1.mem (S + BitVec.ofNat 32 0x67C) 8 = 0 :=
    accV_zero 8 fun i hi => by rw [add_ofNat_assoc]; exact wzero i hi
  have eN0 : memLoad32 n1.mem (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF := by
    have := nfr 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this, hN0]
  have hNpos : 0 < accV M (S + BitVec.ofNat 32 0xE4) 8 := by omega
  -- the loop
  obtain ⟨n2, M2, c2, u2, hc2, hf2, ⟨U, hU⟩, hbd2, k2⟩ := gd_outer (B := GD) (acc := S + BitVec.ofNat 32 0x67C)
    (xp := S + BitVec.ofNat 32 0x69C) (np := S + BitVec.ofNat 32 0xE4) (M0 := n1.mem)
    (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)
    (by rw [F.at _ (by decide)]; omega) (sepS S (.inl (by decide)) (by decide) (by decide))
    (sepS S (.inr (by decide)) (by decide) (by decide)) (F.sepHi (by decide) (by decide) (by decide)) eN0
    (by rw [eX, eN]; exact hW) 7 0 (by decide) u1 C1.self (fun _ _ => rfl)
    ⟨0, by rw [eA0, e27, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, Nat.mul_zero, Nat.zero_mul,
      Nat.add_zero, show accV n1.mem (S + BitVec.ofNat 32 0x69C) 0 = 0 from rfl, Nat.zero_mul]⟩
    (by rw [eA0, e27, eN, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]; omega)
    (by rw [e5]; rfl) (by rw [k1' 18 rfl]; exact r18)
    (by rw [e16]; have := wcopy 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this; exact this.symm)
    (by rw [k1' 22 rfl]; exact r22) (by rw [k1' sp rfl, rsp]; rfl)
    (by rw [k1' 21 rfl, r21, add_ofNat_assoc])
    (by rw [k1' 25 rfl, r25, add_ofNat_assoc]) (by rw [k1' 19 rfl, r19, add_ofNat_assoc]) e17 (by rw [k1' 27 rfl]; exact r27)
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M2 x = M x := fun x hx => by
    rw [hf2 x (F.hiOut (c := 0x67C) (n := 32) (by decide) hx)]
    exact fr1 x (F.lowHi (c := 16) (by decide) rfl hx (by have := x.isLt; omega)) (F.hiOut (c := 0x3C) (n := 4) (by decide) hx)
      (F.hiOut (c := 0x67C) (n := 0x40) (by decide) hx)
  have C2 := C.hi h2hi
  have sp2 : reg n2 sp = S := by rw [k2 sp rfl, k1' sp rfl]; exact rsp
  obtain ⟨n3, Dv, b, c3, u3, C3, hb, hDv, hsub, hres, ha13, fr3, k3⟩ := gd_sq_post C2 F u2 sp2
  -- the arithmetic
  have eN2 : accV M2 (S + BitVec.ofNat 32 0xE4) 8 = accV M (S + BitVec.ofNat 32 0xE4) 8 := by
    rw [← eN]
    exact accV_congr2 8 fun i hi => memLoad32_congr fun q hq => hf2 _ (by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact sepS S (c := 0x67C) (n := 32) (d := 0xE4 + (4 * i + q)) (k := 1) (.inr (by omega)) (by decide) (by omega))
  rw [eN2] at hsub
  obtain ⟨A, hA⟩ : ∃ A, accV M2 (S + BitVec.ofNat 32 0x67C) 8 = A := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, accV M (S + BitVec.ofNat 32 0xE4) 8 = N := ⟨_, rfl⟩
  obtain ⟨mc, hmc⟩ : ∃ mc, (reg n2 (20 : Fin 32)).toNat = mc := ⟨_, rfl⟩
  rw [hA, hN] at hsub
  rw [hA, hmc] at hres
  rw [hA, hmc, show (2 : Nat) ^ (32 * 8) = 2 ^ 256 from rfl, eN, hN, eX] at hU
  rw [hA, hmc, show (2 : Nat) ^ (32 * 8) = 2 ^ 256 from rfl, eN, hN] at hbd2
  have hNl : N < 2 ^ 256 := by rw [← hN]; exact accV_lt M _ 8
  have fin := mm_final_arith hDv hNl hbd2 hsub (mb_le1 b)
  rw [hN] at hNpos
  have hR : accV n3.mem (S + BitVec.ofNat 32 0x67C) 8 = (A + mc * 2 ^ 256) % N := by rw [hres, fin]
  refine ⟨n3, c1.trans (c2.trans c3), u3, C3, by rw [hN, hR]; exact Nat.mod_lt _ hNpos,
    by rw [hN, hR]; exact mont_congr8 rfl hU, ?_, fun x h50 h3C h62 h98 => ?_, fun q hq => ?_⟩
  · rw [ha13, show memLoad32 M2 (S + BitVec.ofNat 32 0x3C) = memLoad32 n1.mem (S + BitVec.ofNat 32 0x3C) from
      memLoad32_congr fun q hq => hf2 _ (by
        rw [add_ofNat_assoc]
        exact sepS S (c := 0x67C) (n := 32) (d := 0x3C + q) (k := 1) (.inr (by omega)) (by decide) (by omega)), w3C]
  · have hA48 : Sep (S + BitVec.ofNat 32 0x67C) 32 x 1 := by
      have := h98.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    have hE48 : Sep (S + BitVec.ofNat 32 0x6BC) 32 x 1 := by
      have := h98.sub (c := 0x40) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
    have h60 : Sep (S + BitVec.ofNat 32 0x67C) 0x40 x 1 := by
      have := h98.sub (c := 0) (l := 0x40) (by decide); rwa [add_ofNat_zero] at this
    have h16 : Sep (S + BitVec.ofNat 32 (2 ^ 32 - 16)) 16 x 1 := by
      have := h50.sub (c := 0x30) (l := 16) (by decide)
      rwa [show S + 0xFFFFFFC0 + BitVec.ofNat 32 0x30 = S + BitVec.ofNat 32 (2 ^ 32 - 16) by rw [BitVec.add_assoc]; rfl]
        at this
    rw [fr3 x h50 h62 hA48 hE48, hf2 x hA48, fr1 x h16 h3C h60]
  · rw [k3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), k1' q hq]


end C3.RV32.Gd
