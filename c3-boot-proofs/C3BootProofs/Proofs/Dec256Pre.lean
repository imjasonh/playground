import C3BootProofs.Proofs.Dec256Pow

/-!
# P-256 point decompression: before the exponentiation

The loops between `decompress`'s entry and its limb loop at 0x2D4: the
exponent's bit width, the zeroing and filling of the table, and the table
of `α`'s first 16 Montgomery powers. The 8-limb counterpart of
`Dec384Pre.lean`.
-/

namespace C3.RV32.Gd

open C3.Image C3.RV32.Dq C3.RV32.P3 C3.RV32.P2

set_option maxRecDepth 20000

/-! ## The table of powers -/

def gdT1 : List BInstr :=
  [.aluImm .add (9 : Fin 32) (19 : Fin 32) 0x20, .aluImm .add a0 sp 0x6BC,
   .aluImm .add a2 sp 0x1DC, .aluImm .add a4 x0 0x1, .alu .add a1 x0 (19 : Fin 32), .aluImm .add a3 sp 0xE4]
def gdT2 : List BInstr := [.aluImm .add a1 sp 0x6BC, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (9 : Fin 32)]
def gdT3 : List BInstr := [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, .alu .add (19 : Fin 32) x0 (9 : Fin 32)]

theorem gdT1_end : blockEnd p256DecompressCode 0x226 gdT1 = some 0x236 := by decide
theorem gdT2_end : blockEnd p256DecompressCode 0x23E gdT2 = some 0x248 := by decide
theorem gdT3_end : blockEnd p256DecompressCode 0x250 gdT3 = some 0x254 := by decide

theorem cnt14_dec : ∀ k : Nat, k < 14 → BitVec.ofNat 32 (14 - k) + 0xFFFFFFFF = BitVec.ofNat 32 (14 - (k + 1)) := by decide
theorem cnt14_ne : ∀ k : Nat, k < 14 → branchTaken .bne (BitVec.ofNat 32 (14 - (k + 1))) 0 = decide (k + 1 < 14) := by
  decide

theorem tab_next8 (S : Word) (k : Nat) :
    S + BitVec.ofNat 32 (0x45C + 32 * k) + 0x20 = S + BitVec.ofNat 32 (0x45C + 32 * (k + 1)) := by
  rw [show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]; congr 2

/-- The parts of memory the table loop changes. -/
def GdTabFrame (S : Word) (M' M : Word → BitVec 8) : Prop :=
  ∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep (S + BitVec.ofNat 32 0x6BC) 32 x 1 →
    Sep (S + BitVec.ofNat 32 0x47C) (32 * 14) x 1 → M' x = M x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **One pass of the table loop**, from 0x226: entry `k + 2` of the table at
`S + 0x43C` becomes the Montgomery product of entry `k + 1` and `α`. -/
theorem gd_tbl_iter {M : Word → BitVec 8} {S : Word} {n : Machine} {k A : Nat} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0x226 (reg n)) (rsp : reg n sp = S) (hk : k < 14)
    (r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 (0x45C + 32 * k)) (r8 : reg n (8 : Fin 32) = BitVec.ofNat 32 (14 - k))
    (hN0 : memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF) (hN : accV M (S + BitVec.ofNat 32 0xE4) 8 = p256)
    (hA : A < p256) (hAv : accV M (S + BitVec.ofNat 32 0x1DC) 8 = A)
    (hT : accV M (S + BitVec.ofNat 32 (0x45C + 32 * k)) 8 = mpow2 A (k + 1)) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' (if k + 1 < 14 then 0x226 else 0x256) (reg n') ∧ GdCode n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 (0x45C + 32 * (k + 1))) 8 = mpow2 A (k + 2) ∧
      (∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep (S + BitVec.ofNat 32 0x6BC) 32 x 1 →
        Sep (S + BitVec.ofNat 32 (0x45C + 32 * (k + 1))) 32 x 1 → n'.mem x = M x) ∧
      reg n' (19 : Fin 32) = S + BitVec.ofNat 32 (0x45C + 32 * (k + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (14 - (k + 1)) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1⟩ := s.block gdT1 C.self gdT1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock gdT1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, hv2, fr2, sp2, k2⟩ := gd_mm (out := S + BitVec.ofNat 32 0x6BC)
    (xp := S + BitVec.ofNat 32 (0x45C + 32 * k)) (yp := S + BitVec.ofNat 32 0x1DC) (S := S)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x236 (reg n1)) C F gd_at_236 gd_at_23a (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdT1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdT1, upd, ↓reduceIte]; rw [r19]; exact BitVec.zero_add _)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdT1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdT1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdT1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    (co := 0x6BC) (cx := 0x45C + 32 * k) (cy := 0x1DC) (by decide) (by omega) (by decide) rfl rfl rfl (by decide)
    (by omega) (by decide) hN0 hN (by rw [hAv]; exact hA)
  have e1 : p2fm (mpow2 A (k + 1)) A = mpow2 A (k + 2) := by
    rw [show p2fm (mpow2 A (k + 1)) A = p2fm (mpow2 A (k + 1)) (mpow2 A 1) by rw [mpow2_one A hA], mpow2_add]
  rw [hT, hAv, e1] at hv2
  have k2' : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n q := fun q hq => by
    rw [k2 q (by revert hq; revert q; decide), r1, runBlock_reg _ _ _ q hz (by simp only [gdT1]; revert hq; revert q; decide)]
  have e9 : reg n2 (9 : Fin 32) = S + BitVec.ofNat 32 (0x45C + 32 * (k + 1)) := by
    rw [k2 9 (by decide), r1]; simp +decide only [runBlock, BInstr.run, gdT1, upd, ↓reduceIte]; rw [r19]; exact tab_next8 S k
  have hbF : (S + 0xFFFFFF40).toNat = S.toNat - 0xC0 := F.below 0xC0 (by decide) (by decide)
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx =>
    fr2 x (sep_of_le (by rw [hbF]; omega) (by have := x.isLt; omega)) (F.hiOut (c := 0x6BC) (n := 32) (by decide) hx)
  have C2 := C.hi h2hi
  -- copy the product to entry k + 2
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide)
  have b16 : ∀ c, c + 32 ≤ 0x710 → Sep (S + BitVec.ofNat 32 c) 32 (S + 0xFFFFFFF0) 16 := fun c hc =>
    (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have w48 : ∀ c, c + 32 ≤ 0x710 → (S + BitVec.ofNat 32 c).toNat + 32 < 2 ^ 32 := fun c hc => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n3, c3, u3⟩ := u2.block gdT2 C2.self gdT2_end ⟨trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock gdT2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, fr4, k4⟩ := c_memcpy (dst := S + BitVec.ofNat 32 (0x45C + 32 * (k + 1)))
    (src := S + BitVec.ofNat 32 0x6BC) (S := S) (N := 32)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem GD n3 0x248 (reg n3)) C2.self C2.K.K gd_at_248 gd_at_24c
    (by decide) (by decide) (by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdT2, upd, ↓reduceIte]; rw [e9]; exact BitVec.zero_add _)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdT2, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, gdT2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
    ⟨C2.K.K.body, F.sepHi (by omega) (by decide) (by decide), hFC, b16 _ (by omega), b16 _ (by decide),
      sepS S (.inl (by omega)) (by omega) (by decide), fA, fW, w48 _ (by omega), w48 _ (by decide)⟩
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have h4hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n4.mem x = M x := fun x hx => by
    rw [fr4 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x45C + 32 * (k + 1)) (n := 32) (by omega) hx) (Nat.le_refl _),
      h2hi x hx]
  have C4 := C.hi h4hi
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n4 q = reg n2 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ gdT2.filterMap BInstr.dst := by simp only [gdT2]; revert h0 h1 h2; revert q; decide
      rw [k4 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r3, runBlock_reg _ _ _ q u2.zero hb]
  have kk : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n2 q :=
    fun q hq => k4' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  obtain ⟨n5, c5, u5⟩ := u4.block gdT3 C4.self gdT3_end ⟨trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock gdT3 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have e8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 (14 - (k + 1)) := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, gdT3, upd, ↓reduceIte]
    rw [kk 8 (by decide), k2' 8 (by decide), r8]; exact cnt14_dec k hk
  have t5 : St n4.mem GD n5 0x254 (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
  have hb5 : branchTaken .bne (reg n5 (8 : Fin 32)) (reg n5 x0) = decide (k + 1 < 14) := by
    rw [e8, t5.zero]; exact cnt14_ne k hk
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have hval : accV n4.mem (S + BitVec.ofNat 32 (0x45C + 32 * (k + 1))) 8 = mpow2 A (k + 2) := by
    rw [← hv2]
    refine cp_accV8 (by omega) (by decide) fun i hi => ?_
    rw [load_frame fr4 (l16 _ (by omega)), ← add_ofNat_assoc S (0x45C + 32 * (k + 1)), cp_word (by omega) (by decide),
      add_ofNat_assoc]
  have post : ∀ n6 : Machine, (∀ q, reg n6 q = reg n5 q) → n6.mem = n4.mem →
      GdCode n6.mem ∧ accV n6.mem (S + BitVec.ofNat 32 (0x45C + 32 * (k + 1))) 8 = mpow2 A (k + 2) ∧
      (∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep (S + BitVec.ofNat 32 0x6BC) 32 x 1 →
        Sep (S + BitVec.ofNat 32 (0x45C + 32 * (k + 1))) 32 x 1 → n6.mem x = M x) ∧
      reg n6 (19 : Fin 32) = S + BitVec.ofNat 32 (0x45C + 32 * (k + 1)) ∧
      reg n6 (8 : Fin 32) = BitVec.ofNat 32 (14 - (k + 1)) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 24, 25, 26, 27] → reg n6 q = reg n q := fun n6 h6 m6 => by
    refine ⟨by rw [m6]; exact C4, by rw [m6]; exact hval, fun x hF h9E hT' => ?_, ?_, by rw [h6, e8], fun q hq => ?_⟩
    · have h16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
        have := hF.sub (c := 0xB0) (l := 16) (by decide)
        rwa [show S + 0xFFFFFF40 + BitVec.ofNat 32 0xB0 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
      rw [m6, fr4 x h16, copyBytes_sep hT' (Nat.le_refl _), fr2 x hF h9E]
    · rw [h6, r5]; simp +decide only [runBlock, BInstr.run, gdT3, upd, ↓reduceIte]; rw [kk 9 (by decide), e9]
      exact BitVec.zero_add _
    · by_cases hs : q = sp
      · subst hs; rw [h6, r5, runBlock_reg _ _ _ sp u4.zero (by decide), kk sp (by decide), sp2, rsp]
      · rw [h6, r5, runBlock_reg _ _ _ q u4.zero (by simp only [gdT3]; revert hq; revert q; decide),
          kk q (by revert hq; revert q; decide), k2' q (by revert hs hq; revert q; decide)]
  by_cases hl : k + 1 < 14
  · obtain ⟨n6, d6, u6⟩ := t5.taken C4.self 0x226 gd_at_254 (by decide) (by rw [hb5]; exact decide_eq_true hl)
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := post n6 u6.regs u6.mem
    exact ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))),
      by rw [ite_eq_left hl]; exact ⟨u6.pc, rfl, fun _ => rfl⟩, p1, p2, p3, p4, p5, p6⟩
  · obtain ⟨n6, d6, u6⟩ := t5.notTaken C4.self 0x256 gd_at_254 (by decide) (by rw [hb5]; exact decide_eq_false hl)
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := post n6 u6.regs u6.mem
    exact ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.single d6))))),
      by rw [ite_eq_right hl]; exact ⟨u6.pc, rfl, fun _ => rfl⟩, p1, p2, p3, p4, p5, p6⟩

theorem GdTabFrame.trans {S : Word} {M1 M2 M3 : Word → BitVec 8} (h1 : GdTabFrame S M2 M1) (h2 : GdTabFrame S M3 M2) :
    GdTabFrame S M3 M1 := fun x a b c => (h2 x a b c).trans (h1 x a b c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The table loop**, from pass `k` to its end at 0x256: entries `0..15`
of the table at `S + 0x43C` become `α`'s first 16 Montgomery powers. -/
theorem gd_tbl {S : Word} {A : Nat} (F : Fr S 0x710) (hA : A < p256) :
    ∀ m k, k + m + 1 = 14 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → St M GD n 0x226 (reg n) →
      reg n sp = S → reg n (19 : Fin 32) = S + BitVec.ofNat 32 (0x45C + 32 * k) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (14 - k) →
      memLoad32 M (S + BitVec.ofNat 32 0xE4) = 0xFFFFFFFF → accV M (S + BitVec.ofNat 32 0xE4) 8 = p256 →
      accV M (S + BitVec.ofNat 32 0x1DC) 8 = A →
      (∀ j, j ≤ k + 1 → accV M (S + BitVec.ofNat 32 (0x43C + 32 * j)) 8 = mpow2 A j) →
      ∃ n', Steps n n' ∧ St n'.mem GD n' 0x256 (reg n') ∧ GdCode n'.mem ∧
        (∀ j, j < 16 → accV n'.mem (S + BitVec.ofNat 32 (0x43C + 32 * j)) 8 = mpow2 A j) ∧ GdTabFrame S n'.mem M ∧
        ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q := by
  have hSl := F.lo; have hSh := F.hi
  have hbF : (S + 0xFFFFFF40).toNat = S.toNat - 0xC0 := F.below 0xC0 (by decide) (by decide)
  -- what one pass leaves alone
  have keep : ∀ {k : Nat} {M M' : Word → BitVec 8}, k < 14 →
      (∀ x, Sep (S + 0xFFFFFF40) 0xC0 x 1 → Sep (S + BitVec.ofNat 32 0x6BC) 32 x 1 →
        Sep (S + BitVec.ofNat 32 (0x45C + 32 * (k + 1))) 32 x 1 → M' x = M x) →
      ∀ d, d + 4 ≤ 0x6BC → (d + 4 ≤ 0x45C + 32 * (k + 1) ∨ 0x45C + 32 * (k + 2) ≤ d) →
        memLoad32 M' (S + BitVec.ofNat 32 d) = memLoad32 M (S + BitVec.ofNat 32 d) := by
    intro k M M' hk h d hd hd'
    refine memLoad32_congr fun q hq => ?_
    rw [add_ofNat_assoc]
    exact h _ (sep_of_le (by rw [hbF, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
      (sepS S (.inr (by omega)) (by decide) (by omega))
      (sepS S (by rcases hd' with h | h; exact .inr (by omega); exact .inl (by omega)) (by omega) (by omega))
  intro m
  induction m with
  | zero =>
    intro k hk M n C s rsp r19 r8 hN0 hN hAv hT
    obtain rfl : k = 13 := by omega
    obtain ⟨n1, c1, u1, C1, hv1, fr1, e19, e8, k1⟩ := gd_tbl_iter C F s rsp (by decide) r19 r8 hN0 hN hA hAv (hT 14 (by decide))
    refine ⟨n1, c1, u1, C1, fun j hj => ?_, fun x a b c => fr1 x a b ?_, k1⟩
    · by_cases hj15 : j = 15
      · subst hj15; exact hv1
      · rw [← hT j (by omega)]
        exact accV_congr2 8 fun i hi => by
          rw [add_ofNat_assoc, keep (by decide) fr1 _ (by omega) (.inl (by omega))]
    · have := c.sub (c := 32 * 13) (l := 32) (by decide); rwa [add_ofNat_assoc] at this
  | succ m ih =>
    intro k hk M n C s rsp r19 r8 hN0 hN hAv hT
    have hTk : accV M (S + BitVec.ofNat 32 (0x45C + 32 * k)) 8 = mpow2 A (k + 1) := by
      rw [show 0x45C + 32 * k = 0x43C + 32 * (k + 1) by omega]; exact hT (k + 1) (Nat.le_refl _)
    obtain ⟨n1, c1, u1, C1, hv1, fr1, e19, e8, k1⟩ := gd_tbl_iter C F s rsp (by omega) r19 r8 hN0 hN hA hAv hTk
    rw [ite_eq_left (show k + 1 < 14 by omega)] at u1
    have kp := keep (k := k) (by omega) fr1
    obtain ⟨n2, c2, u2, C2, hT2, fr2, k2⟩ := ih (k + 1) (by omega) C1 u1 (by rw [k1 sp (by decide)]; exact rsp) e19 e8
      (by rw [kp _ (by decide) (.inl (by omega))]; exact hN0)
      (by rw [← hN]; exact accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, kp _ (by omega) (.inl (by omega))])
      (by rw [← hAv]; exact accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, kp _ (by omega) (.inl (by omega))])
      (fun j hj => by
        by_cases hj2 : j = k + 2
        · subst hj2; rw [show 0x43C + 32 * (k + 2) = 0x45C + 32 * (k + 1) by omega]; exact hv1
        · rw [← hT j (by omega)]
          exact accV_congr2 8 fun i hi => by rw [add_ofNat_assoc, kp _ (by omega) (.inl (by omega))])
    refine ⟨n2, c1.trans c2, u2, C2, hT2, GdTabFrame.trans (fun x a b c => fr1 x a b ?_) fr2,
      fun q hq => by rw [k2 q hq, k1 q hq]⟩
    have := c.sub (c := 32 * k) (l := 32) (by omega)
    rwa [add_ofNat_assoc, show 0x47C + 32 * k = 0x45C + 32 * (k + 1) by omega] at this

/-! ## Filling the table -/

def gdZ1 : List BInstr := [.aluImm .add a2 x0 0x20, .alu .add a0 x0 (8 : Fin 32), .aluImm .add a1 x0 0x0]
def gdZ2 : List BInstr := [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x20, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]
def gdO1 : List BInstr := [.aluImm .add a2 x0 0x20, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (24 : Fin 32)]
def gdO2 : List BInstr := [.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x20, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

theorem gdZ1_end : blockEnd p256DecompressCode 0x19C gdZ1 = some 0x1A4 := by decide
theorem gdZ2_end : blockEnd p256DecompressCode 0x1AC gdZ2 = some 0x1B2 := by decide
theorem gdO1_end : blockEnd p256DecompressCode 0x1FA gdO1 = some 0x202 := by decide
theorem gdO2_end : blockEnd p256DecompressCode 0x20A gdO2 = some 0x210 := by decide

theorem cnt16_dec : ∀ k : Nat, k < 16 → BitVec.ofNat 32 (16 - k) + 0xFFFFFFFF = BitVec.ofNat 32 (16 - (k + 1)) := by decide
theorem cnt16_ne : ∀ k : Nat, k < 16 → branchTaken .bne (BitVec.ofNat 32 (16 - (k + 1))) 0 = decide (k + 1 < 16) := by
  decide

theorem ptr32 (S : Word) (c k : Nat) :
    aluEval .add (S + BitVec.ofNat 32 (c + 32 * k)) 0x20 = S + BitVec.ofNat 32 (c + 32 * (k + 1)) := by
  show S + BitVec.ofNat 32 (c + 32 * k) + BitVec.ofNat 32 0x20 = _
  rw [add_ofNat_assoc]; congr 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The zeroing loop**, from pass `k` at 0x19C to its end at 0x1B4: it
writes only the 0x200 bytes at `S + 0x21C`. -/
theorem gd_zero16 {S : Word} (F : Fr S 0x710) :
    ∀ m k, k + m + 1 = 16 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → St M GD n 0x19C (reg n) →
      reg n (8 : Fin 32) = S + BitVec.ofNat 32 (0x21C + 32 * k) → reg n (9 : Fin 32) = BitVec.ofNat 32 (16 - k) →
      ∃ n', Steps n n' ∧ St n'.mem GD n' 0x1B4 (reg n') ∧ GdCode n'.mem ∧
        (∀ x, Sep (S + BitVec.ofNat 32 0x21C) 0x200 x 1 → n'.mem x = M x) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (8 : Fin 32) →
          q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hSl := F.lo; have hSh := F.hi
  have step : ∀ k, k < 16 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → St M GD n 0x19C (reg n) →
      reg n (8 : Fin 32) = S + BitVec.ofNat 32 (0x21C + 32 * k) → reg n (9 : Fin 32) = BitVec.ofNat 32 (16 - k) →
      ∃ n', Steps n n' ∧ St n'.mem GD n' (if k + 1 < 16 then 0x19C else 0x1B4) (reg n') ∧ GdCode n'.mem ∧
        (∀ x, Sep (S + BitVec.ofNat 32 (0x21C + 32 * k)) 32 x 1 → n'.mem x = M x) ∧
        reg n' (8 : Fin 32) = S + BitVec.ofNat 32 (0x21C + 32 * (k + 1)) ∧
        reg n' (9 : Fin 32) = BitVec.ofNat 32 (16 - (k + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (8 : Fin 32) →
          q ≠ (9 : Fin 32) → reg n' q = reg n q := by
    intro k hk M n C s r8 r9
    have hz := s.zero
    obtain ⟨n1, c1, u1⟩ := s.block gdZ1 C.self gdZ1_end ⟨trivial, trivial, trivial, trivial⟩
    have r1 : ∀ q, reg n1 q = (runBlock gdZ1 (M, reg n)).2 q := fun q => by rw [u1.regs]
    obtain ⟨n2, c2, u2, mem2, k2⟩ := c_memset (dst := S + BitVec.ofNat 32 (0x21C + 32 * k)) (b := 0) (N := 32)
      (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x1A4 (reg n1)) C.self C.K.K gd_at_1a4 gd_at_1a8 (by decide) (by decide)
      (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdZ1, upd, ↓reduceIte]; rw [r8]; exact BitVec.zero_add _)
      (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdZ1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
      (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdZ1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
      (by rw [F.at _ (by omega)]; omega) (F.sepHi (by omega) (by decide) (by decide))
    have h2 : ∀ x, Sep (S + BitVec.ofNat 32 (0x21C + 32 * k)) 32 x 1 → n2.mem x = M x := fun x hx => by
      rw [mem2, fillBytes_sep hx (Nat.le_refl _)]
    have C2 := C.hi fun x hx => h2 x (F.hiOut (by omega) hx)
    have k2' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg n2 q = reg n q :=
      fun q h0 h1 h2 h3 h4 h5 h6 hr => by
        rw [k2 q h0 h2 h3 h4 h5 h6 hr, r1, runBlock_reg _ _ _ q hz (by simp only [gdZ1]; revert h0 h1 h2; revert q; decide)]
    obtain ⟨n3, c3, u3⟩ := u2.block gdZ2 C2.self gdZ2_end ⟨trivial, trivial, trivial⟩
    have r3 : ∀ q, reg n3 q = (runBlock gdZ2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
    have e8 : reg n3 (8 : Fin 32) = S + BitVec.ofNat 32 (0x21C + 32 * (k + 1)) := by
      rw [r3]; simp +decide only [runBlock, BInstr.run, gdZ2, upd, ↓reduceIte]
      rw [k2' 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8]
      exact ptr32 S 0x21C k
    have e9 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 (16 - (k + 1)) := by
      rw [r3]; simp +decide only [runBlock, BInstr.run, gdZ2, upd, ↓reduceIte]
      rw [k2' 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9]
      exact cnt16_dec k hk
    have t3 : St n2.mem GD n3 0x1B2 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    have hb : branchTaken .bne (reg n3 (9 : Fin 32)) (reg n3 x0) = decide (k + 1 < 16) := by
      rw [e9, t3.zero]; exact cnt16_ne k hk
    have kk : ∀ n4 : Machine, (∀ q, reg n4 q = reg n3 q) → ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 →
        q ≠ a6 → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n4 q = reg n q :=
      fun n4 h4 q h0 h1 h2 h3 h4' h5 h6 hr h8 h9 => by
        rw [h4, r3, runBlock_reg _ _ _ q u2.zero (by simp only [gdZ2]; revert h8 h9; revert q; decide),
          k2' q h0 h1 h2 h3 h4' h5 h6 hr]
    by_cases hl : k + 1 < 16
    · obtain ⟨n4, d4, u4⟩ := t3.taken C2.self 0x19C gd_at_1b2 (by decide) (by rw [hb]; exact decide_eq_true hl)
      exact ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), by rw [ite_eq_left hl]; exact ⟨u4.pc, rfl, fun _ => rfl⟩,
        by rw [u4.mem]; exact C2, fun x hx => by rw [u4.mem]; exact h2 x hx, by rw [u4.regs, e8], by rw [u4.regs, e9],
        kk n4 u4.regs⟩
    · obtain ⟨n4, d4, u4⟩ := t3.notTaken C2.self 0x1B4 gd_at_1b2 (by decide) (by rw [hb]; exact decide_eq_false hl)
      exact ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), by rw [ite_eq_right hl]; exact ⟨u4.pc, rfl, fun _ => rfl⟩,
        by rw [u4.mem]; exact C2, fun x hx => by rw [u4.mem]; exact h2 x hx, by rw [u4.regs, e8], by rw [u4.regs, e9],
        kk n4 u4.regs⟩
  intro m
  induction m with
  | zero =>
    intro k hk M n C s r8 r9
    obtain rfl : k = 15 := by omega
    obtain ⟨n1, c1, u1, C1, h1, _, _, k1⟩ := step 15 (by decide) C s r8 r9
    exact ⟨n1, c1, u1, C1, fun x hx => h1 x (by
      have := hx.sub (c := 32 * 15) (l := 32) (by decide); rwa [add_ofNat_assoc] at this), k1⟩
  | succ m ih =>
    intro k hk M n C s r8 r9
    obtain ⟨n1, c1, u1, C1, h1, e8, e9, k1⟩ := step k (by omega) C s r8 r9
    rw [ite_eq_left (show k + 1 < 16 by omega)] at u1
    obtain ⟨n2, c2, u2, C2, h2, k2⟩ := ih (k + 1) (by omega) C1 u1 e8 e9
    refine ⟨n2, c1.trans c2, u2, C2, fun x hx => (h2 x hx).trans (h1 x ?_),
      fun q h0 h1' h2' h3 h4 h5 h6 hr h8 h9 => by
        rw [k2 q h0 h1' h2' h3 h4 h5 h6 hr h8 h9, k1 q h0 h1' h2' h3 h4 h5 h6 hr h8 h9]⟩
    have := hx.sub (c := 32 * k) (l := 32) (by omega); rwa [add_ofNat_assoc] at this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The ones loop**, from pass `k` at 0x1FA to its end at 0x212: entries
`k..15` of the table at `S + 0x43C` become copies of the 32 bytes at `ONE`. -/
theorem gd_ones16 {S ONE : Word} (F : Fr S 0x710) (hOF : Sep (S + 0xFFFFFFF0) 16 ONE 32)
    (hOT : Sep (S + BitVec.ofNat 32 0x43C) 0x200 ONE 32) (hOw : ONE.toNat + 32 < 2 ^ 32) :
    ∀ m k, k + m + 1 = 16 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → St M GD n 0x1FA (reg n) →
      reg n sp = S → reg n (9 : Fin 32) = S + BitVec.ofNat 32 (0x43C + 32 * k) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (16 - k) → reg n (24 : Fin 32) = ONE →
      ∃ n', Steps n n' ∧ St n'.mem GD n' 0x212 (reg n') ∧ GdCode n'.mem ∧
        (∀ j, k ≤ j → j < 16 → accV n'.mem (S + BitVec.ofNat 32 (0x43C + 32 * j)) 8 = accV M ONE 8) ∧
        (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 (0x43C + 32 * k)) (32 * (16 - k)) x 1 →
          n'.mem x = M x) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
          q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → q ≠ (8 : Fin 32) →
          q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide)
  have b16 : ∀ c, c + 32 ≤ 0x710 → Sep (S + BitVec.ofNat 32 c) 32 (S + 0xFFFFFFF0) 16 := fun c hc =>
    (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have l16 : ∀ d, d + 4 ≤ 0x710 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have step : ∀ k, k < 16 → ∀ {M : Word → BitVec 8} {n : Machine}, GdCode M → St M GD n 0x1FA (reg n) →
      reg n sp = S → reg n (9 : Fin 32) = S + BitVec.ofNat 32 (0x43C + 32 * k) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (16 - k) → reg n (24 : Fin 32) = ONE →
      ∃ n', Steps n n' ∧ St n'.mem GD n' (if k + 1 < 16 then 0x1FA else 0x212) (reg n') ∧ GdCode n'.mem ∧
        accV n'.mem (S + BitVec.ofNat 32 (0x43C + 32 * k)) 8 = accV M ONE 8 ∧
        (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 (0x43C + 32 * k)) 32 x 1 → n'.mem x = M x) ∧
        reg n' (9 : Fin 32) = S + BitVec.ofNat 32 (0x43C + 32 * (k + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (16 - (k + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
          q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → q ≠ (8 : Fin 32) →
          q ≠ (9 : Fin 32) → reg n' q = reg n q := by
    intro k hk M n C s rsp r9 r8 r24
    have hz := s.zero
    obtain ⟨n1, c1, u1⟩ := s.block gdO1 C.self gdO1_end ⟨trivial, trivial, trivial, trivial⟩
    have r1 : ∀ q, reg n1 q = (runBlock gdO1 (M, reg n)).2 q := fun q => by rw [u1.regs]
    have hTO : Sep (S + BitVec.ofNat 32 (0x43C + 32 * k)) 32 ONE 32 := by
      have := hOT.sub (c := 32 * k) (l := 32) (by omega); rwa [add_ofNat_assoc] at this
    obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := S + BitVec.ofNat 32 (0x43C + 32 * k)) (src := ONE) (S := S) (N := 32)
      (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M GD n1 0x202 (reg n1)) C.self C.K.K gd_at_202 gd_at_206 (by decide) (by decide)
      (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
      (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdO1, upd, ↓reduceIte]; rw [r9]; exact BitVec.zero_add _)
      (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdO1, upd, ↓reduceIte]; rw [r24]; exact BitVec.zero_add _)
      (by rw [r1]; simp +decide only [runBlock, BInstr.run, gdO1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
      ⟨C.K.K.body, F.sepHi (by omega) (by decide) (by decide), hFC, b16 _ (by omega), hOF.symm, hTO, fA, fW,
        by rw [F.at _ (by omega)]; omega, hOw⟩
    have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = M x := fun x hx => by
      rw [fr2 x (lo16 x hx), copyBytes_sep (F.hiOut (by omega) hx) (Nat.le_refl _)]
    have C2 := C.hi h2hi
    have k2' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n2 q = reg n q :=
      fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
        have hb : q ∉ gdO1.filterMap BInstr.dst := by simp only [gdO1]; revert h0 h1 h2; revert q; decide
        rw [k2 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r1, runBlock_reg _ _ _ q hz hb]
    have ka : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n q :=
      fun q hq => k2' q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    obtain ⟨n3, c3, u3⟩ := u2.block gdO2 C2.self gdO2_end ⟨trivial, trivial, trivial⟩
    have r3 : ∀ q, reg n3 q = (runBlock gdO2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
    have e9 : reg n3 (9 : Fin 32) = S + BitVec.ofNat 32 (0x43C + 32 * (k + 1)) := by
      rw [r3]; simp +decide only [runBlock, BInstr.run, gdO2, upd, ↓reduceIte]; rw [ka 9 (by decide), r9]
      exact ptr32 S 0x43C k
    have e8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 (16 - (k + 1)) := by
      rw [r3]; simp +decide only [runBlock, BInstr.run, gdO2, upd, ↓reduceIte]; rw [ka 8 (by decide), r8]
      exact cnt16_dec k hk
    have t3 : St n2.mem GD n3 0x210 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
    have hb : branchTaken .bne (reg n3 (8 : Fin 32)) (reg n3 x0) = decide (k + 1 < 16) := by
      rw [e8, t3.zero]; exact cnt16_ne k hk
    have hv : accV n2.mem (S + BitVec.ofNat 32 (0x43C + 32 * k)) 8 = accV M ONE 8 :=
      accV_congr2 8 fun i hi => by
        rw [load_frame fr2 (by rw [add_ofNat_assoc]; exact l16 _ (by omega)), cp_word (by omega) (by decide)]
    have kk : ∀ n4 : Machine, (∀ q, reg n4 q = reg n3 q) → ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 →
        q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
        q ≠ (30 : Fin 32) → q ≠ ra → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n4 q = reg n q :=
      fun n4 h4 q h0 h1 h2 h3 h4' h5 h6 h7 h8 h9 h10 h11 h12 h13 hr q8 q9 => by
        rw [h4, r3, runBlock_reg _ _ _ q u2.zero (by simp only [gdO2]; revert q8 q9; revert q; decide),
          k2' q h0 h1 h2 h3 h4' h5 h6 h7 h8 h9 h10 h11 h12 h13 hr]
    have fr : ∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → Sep (S + BitVec.ofNat 32 (0x43C + 32 * k)) 32 x 1 → n2.mem x = M x :=
      fun x h16 hT => by rw [fr2 x h16, copyBytes_sep hT (Nat.le_refl _)]
    by_cases hl : k + 1 < 16
    · obtain ⟨n4, d4, u4⟩ := t3.taken C2.self 0x1FA gd_at_210 (by decide) (by rw [hb]; exact decide_eq_true hl)
      exact ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), by rw [ite_eq_left hl]; exact ⟨u4.pc, rfl, fun _ => rfl⟩,
        by rw [u4.mem]; exact C2, by rw [u4.mem]; exact hv, fun x a b => by rw [u4.mem]; exact fr x a b,
        by rw [u4.regs, e9], by rw [u4.regs, e8], kk n4 u4.regs⟩
    · obtain ⟨n4, d4, u4⟩ := t3.notTaken C2.self 0x212 gd_at_210 (by decide) (by rw [hb]; exact decide_eq_false hl)
      exact ⟨n4, c1.trans (c2.trans (c3.trans (.single d4))), by rw [ite_eq_right hl]; exact ⟨u4.pc, rfl, fun _ => rfl⟩,
        by rw [u4.mem]; exact C2, by rw [u4.mem]; exact hv, fun x a b => by rw [u4.mem]; exact fr x a b,
        by rw [u4.regs, e9], by rw [u4.regs, e8], kk n4 u4.regs⟩
  intro m
  induction m with
  | zero =>
    intro k hk M n C s rsp r9 r8 r24
    obtain rfl : k = 15 := by omega
    obtain ⟨n1, c1, u1, C1, hv1, h1, _, _, k1⟩ := step 15 (by decide) C s rsp r9 r8 r24
    refine ⟨n1, c1, u1, C1, fun j hj1 hj2 => by obtain rfl : j = 15 := by omega
                                                exact hv1, fun x a b => h1 x a b, k1⟩
  | succ m ih =>
    intro k hk M n C s rsp r9 r8 r24
    obtain ⟨n1, c1, u1, C1, hv1, h1, e9, e8, k1⟩ := step k (by omega) C s rsp r9 r8 r24
    rw [ite_eq_left (show k + 1 < 16 by omega)] at u1
    have kx : ∀ q, q.val ∈ [2, 24] → reg n1 q = reg n q := fun q hq => k1 q (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide)
    obtain ⟨n2, c2, u2, C2, hv2, h2, k2⟩ := ih (k + 1) (by omega) C1 u1 (by rw [kx sp (by decide)]; exact rsp) e9 e8
      (by rw [kx 24 (by decide)]; exact r24)
    have hTOk : Sep (S + BitVec.ofNat 32 (0x43C + 32 * k)) 32 ONE 32 := by
      have := hOT.sub (c := 32 * k) (l := 32) (by omega); rwa [add_ofNat_assoc] at this
    have hO1 : accV n1.mem ONE 8 = accV M ONE 8 := accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
      rw [add_ofNat_assoc]
      exact h1 _ (hOF.subR (c := 4 * i + q) (l := 1) (by omega)) (hTOk.subR (c := 4 * i + q) (l := 1) (by omega))
    have hsub : ∀ x, Sep (S + BitVec.ofNat 32 (0x43C + 32 * k)) (32 * (16 - k)) x 1 →
        Sep (S + BitVec.ofNat 32 (0x43C + 32 * (k + 1))) (32 * (16 - (k + 1))) x 1 ∧
        Sep (S + BitVec.ofNat 32 (0x43C + 32 * k)) 32 x 1 := fun x hx => by
      refine ⟨?_, hx.sub (c := 0) (l := 32) (by omega) |> fun h => by rwa [add_ofNat_zero] at h⟩
      have := hx.sub (c := 32) (l := 32 * (16 - (k + 1))) (by omega)
      rwa [add_ofNat_assoc, show 0x43C + 32 * k + 32 = 0x43C + 32 * (k + 1) by omega] at this
    refine ⟨n2, c1.trans c2, u2, C2, fun j hj1 hj2 => ?_, fun x a b => (h2 x a (hsub x b).1).trans (h1 x a (hsub x b).2),
      fun q h0 h1' h2' h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr q8 q9 => by
        rw [k2 q h0 h1' h2' h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr q8 q9,
          k1 q h0 h1' h2' h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr q8 q9]⟩
    by_cases hjk : j = k
    · subst hjk
      rw [← hv1]
      exact accV_congr2 8 fun i hi => memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc, add_ofNat_assoc]
        have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
        exact h2 _ (sep_of_le (by rw [hb16, F.at _ (by omega)]; omega) (by rw [F.at _ (by omega)]; omega))
          (sepS S (.inr (by omega)) (by omega) (by omega))
    · rw [hv2 j (by omega) hj2, hO1]

/-! ## The exponent's bit width -/

def gdL0 : List BInstr := [.aluImm .add a0 x0 0x0, .lui a1 0x40000000, .aluImm .add a2 x0 0x10, .aluImm .add a1 a1 0xFFFFFFFF]
def gdL1 : List BInstr :=
  [.alu .sub a3 x0 a2, .alu .srl a3 a1 a3, .sw sp a3 0x43C, .lw a3 sp 0x43C, .aluImm .sltu a3 a3 0x1, .sb sp a3 0x43C,
   .lbu a3 sp 0x43C, .alu .sll a4 a1 a2, .alu .xor a4 a4 a1, .alu .sub a3 x0 a3, .alu .and a4 a4 a3, .alu .and a3 a3 a2,
   .alu .xor a1 a1 a4, .alu .add a0 a0 a3, .aluImm .srl a2 a2 0x1]
def gdL2 : List BInstr :=
  [.sw sp a1 0x43C, .aluImm .add a1 sp 0x43C, .lw a1 sp 0x43C, .aluImm .sltu a1 a1 0x1, .sb sp a1 0x43C,
   .aluImm .add a1 sp 0x43C, .lbu a1 sp 0x43C, .aluImm .and a1 a1 0x1, .alu .add (8 : Fin 32) a0 a1]

theorem gdL0_end : blockEnd p256DecompressCode 0xE4 gdL0 = some 0xEE := by decide
theorem gdL1_end : blockEnd p256DecompressCode 0xF0 gdL1 = some 0x120 := by decide
theorem gdL2_end : blockEnd p256DecompressCode 0x122 gdL2 = some 0x144 := by decide

set_option maxRecDepth 100000 in
/-- One pass of the leading-zero loop, from 0xF0 to its test at 0x120. -/
theorem gd_lz_iter {M : Word → BitVec 8} {S : Word} {n : Machine} {A0 A1 A2 : Word} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0xF0 (reg n)) (rsp : reg n sp = S) (ra0 : reg n a0 = A0) (ra1 : reg n a1 = A1)
    (ra2 : reg n a2 = A2) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x120 (reg n') ∧ GdCode n'.mem ∧
      (∀ x, Sep (S + BitVec.ofNat 32 0x43C) 4 x 1 → n'.mem x = M x) ∧
      reg n' a0 = (dqLz A0 A1 A2).1 ∧ reg n' a1 = (dqLz A0 A1 A2).2.1 ∧ reg n' a2 = (dqLz A0 A1 A2).2.2 ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg n' q = reg n q := by
  have hz := s.zero
  have a62C : (S + BitVec.ofNat 32 0x43C).toNat % 4 = 0 := by have := F.al; rw [F.at _ (by decide)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block gdL1 C.self gdL1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdL1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp]; exact ⟨⟨a62C, F.sepHi (by decide) (by decide) (by decide)⟩, a62C, F.sepHi (by decide) (by decide) (by decide)⟩)
  have m1 : ∀ x, Sep (S + BitVec.ofNat 32 0x43C) 4 x 1 → n1.mem x = M x := fun x hx => by
    rw [u1.mem]; simp +decide only [runBlock, BInstr.run, gdL1, upd, ↓reduceIte]; rw [rsp]
    rw [memStore8_ne (fun e => hx 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm))]
    exact memStore32_get_sep hx
  refine ⟨n1, c1, ⟨u1.pc, rfl, fun _ => rfl⟩, C.hi fun x hx => m1 x (F.hiOut (by decide) hx), m1, ?_, ?_, ?_,
    fun q h0 h1 h2 h3 h4 => ?_⟩
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, gdL1, upd, ↓reduceIte]
    rw [rsp, ra0, ra1, ra2, hz, memLoad32_store32_same, memStore8_same]; rfl
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, gdL1, upd, ↓reduceIte]
    rw [rsp, ra1, ra2, hz, memLoad32_store32_same, memStore8_same]; rfl
  · rw [u1.regs]; simp +decide only [runBlock, BInstr.run, gdL1, upd, ↓reduceIte]; rw [ra2]; rfl
  · rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [gdL1]; revert h0 h1 h2 h3 h4; revert q; decide)]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The exponent's bit width**, from 0xE4 to 0x144: the constant-time
leading-zero count of the exponent's top limb `0x3FFFFFFF` leaves 2 in `s0`. -/
theorem gd_lz {M : Word → BitVec 8} {S : Word} {n : Machine} (C : GdCode M) (F : Fr S 0x710)
    (s : St M GD n 0xE4 (reg n)) (rsp : reg n sp = S) :
    ∃ n', Steps n n' ∧ St n'.mem GD n' 0x144 (reg n') ∧ GdCode n'.mem ∧
      (∀ x, Sep (S + BitVec.ofNat 32 0x43C) 4 x 1 → n'.mem x = M x) ∧ reg n' (8 : Fin 32) = 2 ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n0, c0, u0⟩ := s.block gdL0 C.self gdL0_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r0 : ∀ q, reg n0 q = (runBlock gdL0 (M, reg n)).2 q := fun q => by rw [u0.regs]
  have e0 : reg n0 a0 = 0 := by rw [r0]; simp +decide only [runBlock, BInstr.run, gdL0, upd, ↓reduceIte]; (try rw [hz]); try rfl
  have e1 : reg n0 a1 = 0x3FFFFFFF := by rw [r0]; simp +decide only [runBlock, BInstr.run, gdL0, upd, ↓reduceIte]; try rfl
  have e2 : reg n0 a2 = 16 := by rw [r0]; simp +decide only [runBlock, BInstr.run, gdL0, upd, ↓reduceIte]; (try rw [hz]); try rfl
  have k0 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n0 q = reg n q := fun q h0 h1 h2 => by
    rw [r0, runBlock_reg _ _ _ q hz (by simp only [gdL0]; revert h0 h1 h2; revert q; decide)]
  have t0 : St M GD n0 0xEE (reg n0) := ⟨u0.pc, u0.mem, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := t0.notTaken C.self 0xF0 gd_at_ee (by decide) (by
    show (reg n0 a2 == reg n0 x0) = false; rw [e2, t0.zero]; rfl)
  have sp1 : reg n1 sp = S := by rw [u1.regs, k0 sp (by decide) (by decide) (by decide)]; exact rsp
  -- five passes
  have pass : ∀ {Mx : Word → BitVec 8} {m : Machine} {A0 A1 A2 B0 B1 B2 : Word}, GdCode Mx → St Mx GD m 0xF0 (reg m) →
      reg m sp = S → reg m a0 = A0 → reg m a1 = A1 → reg m a2 = A2 → dqLz A0 A1 A2 = (B0, B1, B2) →
      ∃ m', Steps m m' ∧ St m'.mem GD m' (if B2 ≠ 0 then 0xF0 else 0x122) (reg m') ∧ GdCode m'.mem ∧
        (∀ x, Sep (S + BitVec.ofNat 32 0x43C) 4 x 1 → m'.mem x = Mx x) ∧ reg m' a0 = B0 ∧ reg m' a1 = B1 ∧
        reg m' a2 = B2 ∧ ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg m' q = reg m q := by
    intro Mx m A0 A1 A2 B0 B1 B2 Cx sx rsx r0' r1' r2' hl
    obtain ⟨m1, c1, v1, C1, f1, g0, g1, g2, gk⟩ := gd_lz_iter Cx F sx rsx r0' r1' r2'
    rw [hl] at g0 g1 g2; simp only at g0 g1 g2
    by_cases hb : B2 ≠ 0
    · obtain ⟨m2, d2, v2⟩ := v1.taken C1.self 0xF0 gd_at_120 (by decide) (by
        show (reg m1 a2 != reg m1 x0) = true; rw [g2, v1.zero]; exact bne_iff_ne.mpr hb)
      exact ⟨m2, c1.trans (.single d2), by rw [ite_eq_left hb]; exact ⟨v2.pc, rfl, fun _ => rfl⟩, by rw [v2.mem]; exact C1,
        fun x hx => by rw [v2.mem]; exact f1 x hx, by rw [v2.regs, g0], by rw [v2.regs, g1], by rw [v2.regs, g2],
        fun q a b c d e => by rw [v2.regs, gk q a b c d e]⟩
    · have hb' : B2 = 0 := by
        by_cases h : B2 = 0
        · exact h
        · exact absurd h hb
      obtain ⟨m2, d2, v2⟩ := v1.notTaken C1.self 0x122 gd_at_120 (by decide) (by
        show (reg m1 a2 != reg m1 x0) = false; rw [g2, v1.zero, hb']; rfl)
      exact ⟨m2, c1.trans (.single d2), by rw [ite_eq_right hb]; exact ⟨v2.pc, rfl, fun _ => rfl⟩, by rw [v2.mem]; exact C1,
        fun x hx => by rw [v2.mem]; exact f1 x hx, by rw [v2.regs, g0], by rw [v2.regs, g1], by rw [v2.regs, g2],
        fun q a b c d e => by rw [v2.regs, gk q a b c d e]⟩
  have u1' : St M GD n1 0xF0 (reg n1) := u1.self
  obtain ⟨p1, cp1, w1, D1, f1, a01, a11, a21, k1⟩ := pass C u1' sp1 (by rw [u1.regs, e0]) (by rw [u1.regs, e1])
    (by rw [u1.regs, e2]) lz1
  rw [ite_eq_left (by decide)] at w1
  have kk : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg m' q = reg m q) →
      reg m' sp = reg m sp := fun h => h sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have sp1' : reg p1 sp = S := by rw [kk k1]; exact sp1
  obtain ⟨p2, cp2, w2, D2, f2, a02, a12, a22, k2⟩ := pass D1 w1 sp1' a01 a11 a21 lz2
  rw [ite_eq_left (by decide)] at w2
  have sp2 : reg p2 sp = S := by rw [kk k2]; exact sp1'
  obtain ⟨p3, cp3, w3, D3, f3, a03, a13, a23, k3⟩ := pass D2 w2 sp2 a02 a12 a22 lz3
  rw [ite_eq_left (by decide)] at w3
  have sp3 : reg p3 sp = S := by rw [kk k3]; exact sp2
  obtain ⟨p4, cp4, w4, D4, f4, a04, a14, a24, k4⟩ := pass D3 w3 sp3 a03 a13 a23 lz4
  rw [ite_eq_left (by decide)] at w4
  have sp4 : reg p4 sp = S := by rw [kk k4]; exact sp3
  obtain ⟨p5, cp5, w5, D5, f5, a05, a15, a25, k5⟩ := pass D4 w4 sp4 a04 a14 a24 lz5
  rw [ite_eq_right (by decide)] at w5
  have sp5 : reg p5 sp = S := by rw [kk k5]; exact sp4
  -- the last test of the top limb
  have a62C : (S + BitVec.ofNat 32 0x43C).toNat % 4 = 0 := by have := F.al; rw [F.at _ (by decide)]; omega
  obtain ⟨p6, cp6, w6⟩ := w5.block gdL2 D5.self gdL2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, gdL2]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp5]; exact ⟨⟨a62C, F.sepHi (by decide) (by decide) (by decide)⟩, a62C, F.sepHi (by decide) (by decide) (by decide)⟩)
  have m6 : ∀ x, Sep (S + BitVec.ofNat 32 0x43C) 4 x 1 → p6.mem x = p5.mem x := fun x hx => by
    rw [w6.mem]; simp +decide only [runBlock, BInstr.run, gdL2, upd, ↓reduceIte]; rw [sp5]
    rw [memStore8_ne (fun e => hx 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm))]
    exact memStore32_get_sep hx
  refine ⟨p6, c0.trans (.cons d1 (cp1.trans (cp2.trans (cp3.trans (cp4.trans (cp5.trans cp6)))))),
    ⟨w6.pc, rfl, fun _ => rfl⟩, D5.hi fun x hx => m6 x (F.hiOut (by decide) hx),
    fun x hx => by rw [m6 x hx, f5 x hx, f4 x hx, f3 x hx, f2 x hx, f1 x hx], ?_, fun q h0 h1 h2 h3 h4 h8 => ?_⟩
  · rw [w6.regs]; simp +decide only [runBlock, BInstr.run, gdL2, upd, ↓reduceIte]
    rw [sp5, a05, a15, memLoad32_store32_same, memStore8_same]; rfl
  · rw [w6.regs, runBlock_reg _ _ _ q w5.zero (by simp only [gdL2]; revert h0 h1 h8; revert q; decide),
      k5 q h0 h1 h2 h3 h4, k4 q h0 h1 h2 h3 h4, k3 q h0 h1 h2 h3 h4, k2 q h0 h1 h2 h3 h4, k1 q h0 h1 h2 h3 h4, u1.regs,
      k0 q h0 h1 h2]


end C3.RV32.Gd
