import C3BootProofs.Proofs.Pv384Calls

/-!
# `p384_verify_prehash`: the prologue and the checks

From the entry to 0x156, where the signature and key have passed their
checks, or to the return of 0 when one fails.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

theorem ld_st_pv {M : Word → BitVec 8} {S v : Word} {c d : Nat} (hc : c % 4 = 0) (hd : d % 4 = 0)
    (hc' : c + 4 ≤ 0x10000) (hd' : d + 4 ≤ 0x10000) :
    memLoad32 (memStore32 M (S + BitVec.ofNat 32 c) v) (S + BitVec.ofNat 32 d) =
      if c = d then v else memLoad32 M (S + BitVec.ofNat 32 d) := by
  by_cases h : c = d
  · subst h; rw [ite_eq_left rfl, memLoad32_store32_same]
  · rw [ite_eq_right h, memLoad32_store32_sep (sepS S (by omega) (by omega) (by omega))]

/-- The prologue's saves, in order, at the top of the frame. -/
def pvSaves (M : Word → BitVec 8) (B : Word) (n : Machine) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 ((M)) (B + BitVec.ofNat 32 0x219c) (reg n ra)) (B + BitVec.ofNat 32 0x2198) (reg n (8 : Fin 32))) (B + BitVec.ofNat 32 0x2194) (reg n (9 : Fin 32))) (B + BitVec.ofNat 32 0x2190) (reg n (18 : Fin 32))) (B + BitVec.ofNat 32 0x218c) (reg n (19 : Fin 32))) (B + BitVec.ofNat 32 0x2188) (reg n (20 : Fin 32))) (B + BitVec.ofNat 32 0x2184) (reg n (21 : Fin 32))) (B + BitVec.ofNat 32 0x2180) (reg n (22 : Fin 32))) (B + BitVec.ofNat 32 0x217c) (reg n (23 : Fin 32))) (B + BitVec.ofNat 32 0x2178) (reg n (24 : Fin 32))) (B + BitVec.ofNat 32 0x2174) (reg n (25 : Fin 32))) (B + BitVec.ofNat 32 0x2170) (reg n (26 : Fin 32))) (B + BitVec.ofNat 32 0x216c) (reg n (27 : Fin 32))

theorem pvSaves_read {M : Word → BitVec 8} {B : Word} {n : Machine} :
    ∀ k, k < 13 → memLoad32 (pvSaves M B n) (B + BitVec.ofNat 32 (0x219C - 4 * k)) = reg n (savedReg k) := by
  intro k hk
  match k, hk with
  | 0, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 1, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 2, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 3, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 4, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 5, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 6, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 7, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 8, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 9, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 10, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 11, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide), ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl
  | 12, _ => unfold pvSaves; rw [ld_st_pv (by decide) (by decide) (by decide) (by decide), ite_eq_left (by decide)]; rfl

theorem pvSaves_out {M : Word → BitVec 8} {B : Word} {n : Machine} {x : Word}
    (h : Sep (B + BitVec.ofNat 32 0x216C) 0x34 x 1) : pvSaves M B n x = M x := by
  have hs : ∀ c, 0x216C ≤ c → c + 4 ≤ 0x21A0 → Sep (B + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := h.sub (c := c - 0x216C) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x216C + (c - 0x216C) = c by omega] at this
  unfold pvSaves
  rw [memStore32_get_sep (hs 0x216c (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2170 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2174 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2178 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x217c (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2180 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2184 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2188 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x218c (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2190 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2194 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x2198 (by decide) (by decide))]
  rw [memStore32_get_sep (hs 0x219c (by decide) (by decide))]

def pvA1 : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFF00, .sw sp ra 0xFC, .sw sp (8 : Fin 32) 0xF8, .sw sp (9 : Fin 32) 0xF4, .sw sp (18 : Fin 32) 0xF0, .sw sp (19 : Fin 32) 0xEC, .sw sp (20 : Fin 32) 0xE8, .sw sp (21 : Fin 32) 0xE4, .sw sp (22 : Fin 32) 0xE0, .sw sp (23 : Fin 32) 0xDC, .sw sp (24 : Fin 32) 0xD8, .sw sp (25 : Fin 32) 0xD4, .sw sp (26 : Fin 32) 0xD0, .sw sp (27 : Fin 32) 0xCC,
   .lui a5 0x2000, .aluImm .add a5 a5 0xFFFFFC80, .alu .sub sp sp a5, .alu .add (21 : Fin 32) x0 a4,
   .alu .add (9 : Fin 32) x0 a3, .alu .add (19 : Fin 32) x0 a2, .alu .add (20 : Fin 32) x0 a1,
   .alu .add (8 : Fin 32) x0 a0, .lui a2 0x3FCC4000, .aluImm .add a2 a2 0x470, .aluImm .add a1 x0 0x30,
   .aluImm .add a3 x0 0x30, .alu .add a0 x0 (9 : Fin 32)]

theorem pvA1_end : blockEnd p384VerifyPrehashCode 0 pvA1 = some 0x42 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The prologue**, from the entry to the first `in_scalar_range` call at
0x42: save `ra` and `s0..s11` at the top of the frame and open the frame at
`B + 0x420`, with the arguments in `s0`, `s4`, `s3`, `s1`, and `s5`. -/
theorem pv_pro {M : Word → BitVec 8} {n : Machine} {B : Word} (C : PvCode M) (F : Fr B 0x21A0)
    (s : St M PV n 0 (reg n)) (rsp : reg n sp = B + 0x21A0) :
    ∃ n', Steps n n' ∧ St (pvSaves M B n) PV n' 0x42 (reg n') ∧
      reg n' sp = B + 0x420 ∧ reg n' (8 : Fin 32) = reg n a0 ∧ reg n' (20 : Fin 32) = reg n a1 ∧
      reg n' (19 : Fin 32) = reg n a2 ∧ reg n' (9 : Fin 32) = reg n a3 ∧ reg n' (21 : Fin 32) = reg n a4 ∧
      reg n' a0 = reg n a3 ∧ reg n' a1 = 0x30 ∧ reg n' a2 = 0x3FCC4470 ∧ reg n' a3 = 0x30 ∧
      ∀ q, q.val ∈ [3, 4] → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (B + 0x21A0) 0xFFFFFF00 = B + BitVec.ofNat 32 0x20A0 := by
    show B + 0x21A0 + 0xFFFFFF00 = B + BitVec.ofNat 32 0x20A0
    rw [BitVec.add_assoc]; rfl
  have alB : ∀ (k : Word), 0x20A0 + k.toNat + 4 ≤ 0x21A0 → (0x20A0 + k.toNat) % 4 = 0 →
      (B + BitVec.ofNat 32 0x20A0 + k).toNat % 4 = 0 := fun k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  have sepB : ∀ (k : Word), 0x20A0 + k.toNat + 4 ≤ 0x21A0 →
      Sep (B + BitVec.ofNat 32 0x20A0 + k) 4 PV p384VerifyPrehashCode.length := fun k h1 => by
    rw [frame_lit k (by omega)]; exact F.sepHi (by omega) (by decide) (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block pvA1 C.self pvA1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, pvA1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA]
    exact ⟨⟨alB 0xFC (by decide) (by decide), sepB 0xFC (by decide)⟩,
      ⟨alB 0xF8 (by decide) (by decide), sepB 0xF8 (by decide)⟩,
      ⟨alB 0xF4 (by decide) (by decide), sepB 0xF4 (by decide)⟩,
      ⟨alB 0xF0 (by decide) (by decide), sepB 0xF0 (by decide)⟩,
      ⟨alB 0xEC (by decide) (by decide), sepB 0xEC (by decide)⟩,
      ⟨alB 0xE8 (by decide) (by decide), sepB 0xE8 (by decide)⟩,
      ⟨alB 0xE4 (by decide) (by decide), sepB 0xE4 (by decide)⟩,
      ⟨alB 0xE0 (by decide) (by decide), sepB 0xE0 (by decide)⟩,
      ⟨alB 0xDC (by decide) (by decide), sepB 0xDC (by decide)⟩,
      ⟨alB 0xD8 (by decide) (by decide), sepB 0xD8 (by decide)⟩,
      ⟨alB 0xD4 (by decide) (by decide), sepB 0xD4 (by decide)⟩,
      ⟨alB 0xD0 (by decide) (by decide), sepB 0xD0 (by decide)⟩,
      ⟨alB 0xCC (by decide) (by decide), sepB 0xCC (by decide)⟩⟩)
  have m1 : n1.mem = pvSaves M B n := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, pvA1]; simp +decide only [upd, ↓reduceIte]
    rw [rsp, hA]
    simp (disch := decide) only [frame_lit]
    rfl
  have g : ∀ q, reg n1 q = (runBlock pvA1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  refine ⟨n1, c1, ⟨u1.pc, m1, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]; rw [rsp]
    show B + 0x21A0 + 0xFFFFFF00 - 0x1C80 = B + 0x420
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_assoc]; rfl
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]; exact BitVec.zero_add _
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]; show 0#32 + (0#32 + reg n a3) = reg n a3; rw [BitVec.zero_add, BitVec.zero_add]
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]
  · rw [g]; simp +decide only [runBlock, BInstr.run, pvA1, upd, ↓reduceIte]
  · rw [g, runBlock_reg _ _ _ q hz (by simp only [pvA1]; revert hq; revert q; decide)]

end C3.RV32.Pv
