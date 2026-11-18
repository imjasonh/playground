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

def pvE : List BInstr :=
  [.lui a1 0x2000, .aluImm .add a1 a1 0xFFFFFC80, .alu .add sp sp a1, .lw ra sp 0xFC, .lw (8 : Fin 32) sp 0xF8, .lw (9 : Fin 32) sp 0xF4, .lw (18 : Fin 32) sp 0xF0, .lw (19 : Fin 32) sp 0xEC, .lw (20 : Fin 32) sp 0xE8, .lw (21 : Fin 32) sp 0xE4, .lw (22 : Fin 32) sp 0xE0, .lw (23 : Fin 32) sp 0xDC, .lw (24 : Fin 32) sp 0xD8, .lw (25 : Fin 32) sp 0xD4, .lw (26 : Fin 32) sp 0xD0, .lw (27 : Fin 32) sp 0xCC, .aluImm .add sp sp 0x100]

theorem pvE_end : blockEnd p384VerifyPrehashCode 0x130 pvE = some 0x154 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The epilogue**, from 0x130 to the return: restore `ra` and `s0..s11`
from the top of the frame, close the frame, and return with `a0` as it was. -/
theorem pv_epi {M : Word → BitVec 8} {n : Machine} {B : Word} {v : Nat → Word} (C : PvCode M) (F : Fr B 0x21A0)
    (s : St M PV n 0x130 (reg n)) (rsp : reg n sp = B + 0x420)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x219C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0) :
    ∃ n', Steps n n' ∧ n'.pc = v 0 ∧ n'.mem = M ∧ reg n' sp = B + 0x21A0 ∧
      (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧ reg n' a0 = reg n a0 ∧
      reg n' (3 : Fin 32) = reg n (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n (4 : Fin 32) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hA : aluEval .add (B + 0x420) (aluEval .add 0x2000 0xFFFFFC80) = B + BitVec.ofNat 32 0x20A0 := by
    show B + 0x420 + (0x2000 + 0xFFFFFC80) = B + BitVec.ofNat 32 0x20A0
    rw [BitVec.add_assoc]; rfl
  have alB : ∀ (k : Word), 0x20A0 + k.toNat + 4 ≤ 0x21A0 → (0x20A0 + k.toNat) % 4 = 0 →
      (B + BitVec.ofNat 32 0x20A0 + k).toNat % 4 = 0 := fun k h1 h2 => by
    rw [frame_lit k (by omega), F.at _ (by omega)]; omega
  obtain ⟨n1, c1, u1⟩ := s.block pvE C.self pvE_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, pvE]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [rsp, hA]
    exact ⟨alB 0xFC (by decide) (by decide), alB 0xF8 (by decide) (by decide), alB 0xF4 (by decide) (by decide), alB 0xF0 (by decide) (by decide), alB 0xEC (by decide) (by decide), alB 0xE8 (by decide) (by decide), alB 0xE4 (by decide) (by decide), alB 0xE0 (by decide) (by decide), alB 0xDC (by decide) (by decide), alB 0xD8 (by decide) (by decide), alB 0xD4 (by decide) (by decide), alB 0xD0 (by decide) (by decide), alB 0xCC (by decide) (by decide)⟩)
  have m1 : (runBlock pvE (M, reg n)).1 = M := rfl
  obtain ⟨n2, st2, pc2, mem2, regs2⟩ := u1.jalr (by rw [m1]; exact C.self) pv_at_154
  have ra1 : (runBlock pvE (M, reg n)).2 ra = v 0 := by
    simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte]
    rw [rsp, hA, frame_lit _ (by decide)]; exact hS 0 (by decide)
  refine ⟨n2, c1.trans (.single st2), ?_, mem2.trans m1, ?_, fun k hk => ?_, ?_, ?_, ?_⟩
  · rw [pc2, ra1]; exact (congrArg (· &&& ~~~1) (BitVec.add_zero _)).trans hret
  · rw [regs2]; simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte]; rw [rsp]
    show B + 0x420 + (0x2000 + 0xFFFFFC80) + 0x100 = B + 0x21A0
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  · rw [regs2]
    match k, hk with
    | 0, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 0 (by decide)
    | 1, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 1 (by decide)
    | 2, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 2 (by decide)
    | 3, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 3 (by decide)
    | 4, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 4 (by decide)
    | 5, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 5 (by decide)
    | 6, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 6 (by decide)
    | 7, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 7 (by decide)
    | 8, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 8 (by decide)
    | 9, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 9 (by decide)
    | 10, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 10 (by decide)
    | 11, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 11 (by decide)
    | 12, _ =>
      simp +decide only [runBlock, BInstr.run, pvE, upd, ↓reduceIte, savedReg]
      rw [rsp, hA, frame_lit _ (by decide)]; exact hS 12 (by decide)
    | _ + 13, h => exact absurd h (by omega)
  · rw [regs2, runBlock_reg _ _ _ a0 hz (by decide)]
  · rw [regs2, runBlock_reg _ _ _ 3 hz (by decide)]
  · rw [regs2, runBlock_reg _ _ _ 4 hz (by decide)]

/-! ## The checks -/

def pvA2 : List BInstr :=
  [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0x470, .aluImm .add a1 x0 0x30, .aluImm .add a3 x0 0x30,
   .alu .add a0 x0 (21 : Fin 32)]
def pvA3 : List BInstr := [.alu .add a1 x0 a0, .aluImm .add a0 x0 0x0]
def pvA4 : List BInstr := [.aluImm .add a0 sp 0xB8, .alu .add a1 x0 (8 : Fin 32)]

theorem pvA2_end : blockEnd p384VerifyPrehashCode 0x4C pvA2 = some 0x5E := by decide
theorem pvA3_end : blockEnd p384VerifyPrehashCode 0x66 pvA3 = some 0x6A := by decide
theorem pvA4_end : blockEnd p384VerifyPrehashCode 0x76 pvA4 = some 0x7A := by decide

abbrev ISRN : Word := 0x3FCC4470

/-- A region of the frame at `S = B + 0x420` lies inside the 0x230C bytes
from `B - 0x1A0` that `p384_verify_prehash` may write. -/
theorem pvR_hi {B x : Word} {c l : Nat} (hx : Sep (B + 0xFFFFFE60) 0x230C x 1) (h : c + l ≤ 0x1D4C) :
    Sep (B + 0x420 + BitVec.ofNat 32 c) l x 1 := by
  have := hx.sub (c := 0x5C0 + c) (l := l) (by omega)
  rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x5C0 + c) = B + 0x420 + BitVec.ofNat 32 c by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl, show (0x420 : Word).toNat = 0x420 from rfl]
    omega] at this

theorem pvR_lo {B x : Word} {k : Nat} (hx : Sep (B + 0xFFFFFE60) 0x230C x 1) (hk : k ≤ 0x5C0) (hk0 : 0 < k) :
    Sep (B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)) k x 1 := by
  have := hx.sub (c := 0x5C0 - k) (l := k) (by omega)
  rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x5C0 - k) = B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k) by
    rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0xFFFFFE60 : Word).toNat = 0xFFFFFE60 from rfl, show (0x420 : Word).toNat = 0x420 from rfl]
    omega] at this

/-- The first three checks: `r` and `s` in range, and a key `from_sec1_bytes` accepts. -/
def PvCk1 (M : Word → BitVec 8) (pk rp sp' : Word) : Prop :=
  inScalarRange (memBytes M rp 48) (memBytes M ISRN 48) ∧ inScalarRange (memBytes M sp' 48) (memBytes M ISRN 48) ∧
    Fs.FsOk M pk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The first checks**, from 0x42 to 0x86: `in_scalar_range` on `r` and
`s`, the key's tag, and `from_sec1_bytes`, or the jump to the return of 0. -/
theorem pv_stA1 {M : Word → BitVec 8} {n : Machine} {B pk rp sp' : Word} (C : PvCode M) (D : PvData M)
    (F : Fr B 0x21A0) (s : St M PV n 0x42 (reg n)) (rsp : reg n sp = B + 0x420) (ra0 : reg n a0 = rp)
    (ra1 : reg n a1 = 0x30) (ra2 : reg n a2 = ISRN) (ra3 : reg n a3 = 0x30) (r8 : reg n (8 : Fin 32) = pk)
    (r21 : reg n (21 : Fin 32) = sp') (sPK : Sep pk 0x61 (B + 0xFFFFFE60) 0x230C)
    (hPK : pk.toNat + 0x61 ≤ 0x40000000) :
    ∃ n', Steps n n' ∧ (∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n'.mem x = M x) ∧ reg n' sp = B + 0x420 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 9, 19, 20, 21] → reg n' q = reg n q) ∧
      ((St n'.mem PV n' 0x130 (reg n') ∧ reg n' a0 = 0 ∧ ¬ PvCk1 M pk rp sp') ∨
       (St n'.mem PV n' 0x86 (reg n') ∧ PvCk1 M pk rp sp' ∧ PvCode n'.mem ∧ PvData n'.mem ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0xBC) 12 = Fs.fsVal M pk 1 * 2 ^ 384 % p384 ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0xEC) 12 = Fs.fsVal M pk 0x31 * 2 ^ 384 % p384 ∧
        n'.mem (B + 0x420 + BitVec.ofNat 32 0x11C) = 0)) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  -- in_scalar_range(r)
  obtain ⟨n1, c1, u1, a01, k1⟩ := c_isr (x := rp) (y := ISRN) (k := 0x30) (k' := 0x30) s C.self C.isr pv_at_42 pv_at_46
    (by decide) (by decide) ra0 ra1 ra2 ra3 (by decide) (by decide)
  have fail : ∀ {m : Machine}, St M PV m 0x130 (reg m) → reg m a0 = 0 → Steps n m →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 19, 20, 21] → reg m q = reg n q) → ¬ PvCk1 M pk rp sp' →
      ∃ n', Steps n n' ∧ (∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n'.mem x = M x) ∧ reg n' sp = B + 0x420 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 9, 19, 20, 21] → reg n' q = reg n q) ∧
        ((St n'.mem PV n' 0x130 (reg n') ∧ reg n' a0 = 0 ∧ ¬ PvCk1 M pk rp sp') ∨
         (St n'.mem PV n' 0x86 (reg n') ∧ PvCk1 M pk rp sp' ∧ PvCode n'.mem ∧ PvData n'.mem ∧
          accV n'.mem (B + 0x420 + BitVec.ofNat 32 0xBC) 12 = Fs.fsVal M pk 1 * 2 ^ 384 % p384 ∧
          accV n'.mem (B + 0x420 + BitVec.ofNat 32 0xEC) 12 = Fs.fsVal M pk 0x31 * 2 ^ 384 % p384 ∧
          n'.mem (B + 0x420 + BitVec.ofNat 32 0x11C) = 0)) := fun {m} sm am cm km nk =>
    ⟨m, cm, fun x _ => by rw [sm.mem], by rw [km sp (by decide)]; exact rsp,
      fun q hq => km q (by revert hq; revert q; decide), .inl ⟨⟨sm.pc, rfl, fun _ => rfl⟩, am, nk⟩⟩
  by_cases h1 : inScalarRange (memBytes M rp 48) (memBytes M ISRN 48)
  case neg =>
    obtain ⟨n2, d2, u2⟩ := u1.taken C.self 0x130 pv_at_4a (by decide) (by
      show (reg n1 a0 == reg n1 x0) = true; rw [a01, ite_eq_right h1, u1.zero]; rfl)
    exact fail u2.self (by rw [u2.regs, a01, ite_eq_right h1]) (c1.trans (.single d2))
      (fun q hq => by rw [u2.regs, k1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide)]) (fun h => h1 h.1)
  obtain ⟨n2, d2, u2⟩ := u1.notTaken C.self 0x4C pv_at_4a (by decide) (by
    show (reg n1 a0 == reg n1 x0) = false; rw [a01, ite_eq_left h1, u1.zero]; rfl)
  have k12 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n q :=
    fun q hq => by rw [u2.regs, k1 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  -- in_scalar_range(s)
  obtain ⟨n3, c3, u3⟩ := u2.self.block pvA2 C.self pvA2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock pvA2 (M, reg n2)).2 q := fun q => by rw [u3.regs]
  obtain ⟨n4, c4, u4, a04, k4⟩ := c_isr (x := sp') (y := ISRN) (k := 0x30) (k' := 0x30)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St M PV n3 0x5E (reg n3)) C.self C.isr pv_at_5e pv_at_62 (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, pvA2, upd, ↓reduceIte]; rw [k12 21 (by decide), r21]
        exact BitVec.zero_add _)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, pvA2, upd, ↓reduceIte]; try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, pvA2, upd, ↓reduceIte]; try rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, pvA2, upd, ↓reduceIte]; try rfl) (by decide) (by decide)
  have k34 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n q :=
    fun q hq => by
      rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.self.zero (by simp only [pvA2]; revert hq; revert q; decide),
        k12 q hq]
  obtain ⟨n5, c5, u5⟩ := u4.block pvA3 C.self pvA3_end ⟨trivial, trivial, trivial⟩
  have r5 : ∀ q, reg n5 q = (runBlock pvA3 (M, reg n4)).2 q := fun q => by rw [u5.regs]
  have t5 : St M PV n5 0x6A (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n q :=
    fun q hq => by rw [r5, runBlock_reg _ _ _ q u4.zero (by simp only [pvA3]; revert hq; revert q; decide), k34 q hq]
  have a05 : reg n5 a0 = 0 := by rw [r5]; simp +decide only [runBlock, BInstr.run, pvA3, upd, ↓reduceIte]; try rfl
  have a15 : reg n5 a1 = (if inScalarRange (memBytes M sp' 48) (memBytes M ISRN 48) then 1 else 0) := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, pvA3, upd, ↓reduceIte]; rw [a04]; exact BitVec.zero_add _
  by_cases h2 : inScalarRange (memBytes M sp' 48) (memBytes M ISRN 48)
  case neg =>
    obtain ⟨n6, d6, u6⟩ := t5.taken C.self 0x130 pv_at_6a (by decide) (by
      show (reg n5 a1 == reg n5 x0) = true; rw [a15, ite_eq_right h2, t5.zero]; rfl)
    exact fail u6.self (by rw [u6.regs, a05]) (c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.single d6))))))
      (fun q hq => by rw [u6.regs, k5 q (by revert hq; revert q; decide)]) (fun h => h2 h.2.1)
  obtain ⟨n6, d6, u6⟩ := t5.notTaken C.self 0x6C pv_at_6a (by decide) (by
    show (reg n5 a1 == reg n5 x0) = false; rw [a15, ite_eq_left h2, t5.zero]; rfl)
  -- the tag
  obtain ⟨n7, d7, u7⟩ := u6.self.lbu C.self pv_at_6c (off' := 0x70) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.self.aluImm C.self pv_at_70 (off' := 0x72) (by decide)
  have e8a1 : reg n8 a1 = (M pk).zeroExtend 32 := by
    rw [u8.regs, upd_ne (by decide) (by decide), u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [u6.regs, k5 8 (by decide), r8, add_lit_zero]
  have e8a2 : reg n8 a2 = 4 := by rw [u8.regs]; simp +decide only [upd, ↓reduceIte]; rw [u7.self.zero]; rfl
  have k8 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n q :=
    fun q hq => by
      rw [u8.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide), u7.regs,
        upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide), u6.regs, k5 q hq]
  have a08 : reg n8 a0 = 0 := by
    rw [u8.regs, upd_ne (by decide) (by decide), u7.regs, upd_ne (by decide) (by decide), u6.regs, a05]
  by_cases h3 : M pk = 4
  case neg =>
    obtain ⟨n9, d9, u9⟩ := u8.self.taken C.self 0x130 pv_at_72 (by decide) (by
      show (reg n8 a1 != reg n8 a2) = true
      rw [e8a1, e8a2]
      have : ∀ b : BitVec 8, b ≠ 4 → (b.zeroExtend 32 != (4 : Word)) = true := by decide
      exact this _ h3)
    exact fail u9.self (by rw [u9.regs, a08])
      (c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.cons d6 (.cons d7 (.cons d8 (.single d9)))))))))
      (fun q hq => by rw [u9.regs, k8 q (by revert hq; revert q; decide)]) (fun h => h3 h.2.2.1)
  obtain ⟨n9, d9, u9⟩ := u8.self.notTaken C.self 0x76 pv_at_72 (by decide) (by
    show (reg n8 a1 != reg n8 a2) = false; rw [e8a1, e8a2, h3]; rfl)
  -- from_sec1_bytes
  obtain ⟨n10, c10, u10⟩ := u9.self.block pvA4 C.self pvA4_end ⟨trivial, trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock pvA4 (M, reg n9)).2 q := fun q => by rw [u10.regs]
  have sp9 : reg n9 sp = B + 0x420 := by rw [u9.regs, k8 sp (by decide)]; exact rsp
  have hb1A : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  obtain ⟨n11, c11, u11, sp11, k11, ok11, bad11, fr11⟩ := c_fs (inp := pk) (out := B + BitVec.ofNat 32 0x4D8)
    (⟨u10.pc, u10.mem, fun _ => rfl⟩ : St M PV n10 0x7A (reg n10)) C.self C D F (by decide) pv_at_7a pv_at_7e
    (by decide) (by decide) (by rw [r10, runBlock_reg _ _ _ sp u9.self.zero (by decide)]; exact sp9)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, pvA4, upd, ↓reduceIte]; rw [sp9]; show B + 0x420 + 0xB8 = B + BitVec.ofNat 32 0x4D8; rw [BitVec.add_assoc]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, pvA4, upd, ↓reduceIte]
        rw [u9.regs, k8 8 (by decide), r8]; exact BitVec.zero_add _)
    (sPK.subR (c := 0) (l := 0x5C0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h) hPK
    (co := 0x4D8) (by decide) (by decide) rfl (by decide)
  have hR11 : ∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n11.mem x = M x := fun x hx =>
    fr11 x (hx.sub (c := 0) (l := 0x5C0) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
      (by have := hx.sub (c := 0x1A0 + 0x4D8) (l := 0x68) (by decide)
          rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x4D8) = BitVec.ofNat 32 0x4D8 from rfl]
            at this)
  have C11 : PvCode n11.mem := C.hi fun x hx => fr11 x (sep_of_le (by rw [hb1A]; omega) (by have := x.isLt; omega))
    (F.hiOut (c := 0x4D8) (n := 0x68) (by decide) hx)
  have D11 : PvData n11.mem := D.of F fun x hx => fr11 x (hx.sub (c := 0) (l := 0x5C0) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h) (by
      have := hx.sub (c := 0x1A0 + 0x4D8) (l := 0x68) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 (0x1A0 + 0x4D8) = BitVec.ofNat 32 0x4D8 from rfl]
        at this)
  have k11' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n11 q = reg n q :=
    fun q hq => by
      by_cases hsp : q = sp
      · subst hsp; rw [sp11, rsp]
      · rw [k11 q (by revert hq hsp; revert q; decide), r10,
          runBlock_reg _ _ _ q u9.self.zero (by simp only [pvA4]; revert hq hsp; revert q; decide), u9.regs, k8 q hq]
  obtain ⟨n12, d12, u12⟩ := u11.lw C11.self pv_at_82 (off' := 0x84) (by decide)
    (by rw [sp11, show B + 0x420 + 0xB8 = B + BitVec.ofNat 32 0x4D8 by rw [BitVec.add_assoc]; rfl, F.at _ (by decide)]
        omega)
  have e12 : reg (n12) a0 = memLoad32 n11.mem (B + BitVec.ofNat 32 0x4D8) := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [sp11, show B + 0x420 + 0xB8 = B + BitVec.ofNat 32 0x4D8 by rw [BitVec.add_assoc]; rfl]
  have k12' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n12 q = reg n q :=
    fun q hq => by rw [u12.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide), k11' q hq]
  by_cases h4 : Fs.FsOk M pk
  case neg =>
    obtain ⟨n13, d13, u13⟩ := u12.self.taken C11.self 0x12E pv_at_84 (by decide) (by
      show (reg n12 a0 != reg n12 x0) = true; rw [e12, bad11 h4, u12.self.zero]; rfl)
    obtain ⟨n14, d14, u14⟩ := u13.self.aluImm C11.self pv_at_12e (off' := 0x130) (by decide)
    refine ⟨n14, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.cons d6 (.cons d7 (.cons d8 (.cons d9 (c10.trans (c11.trans (.cons d12 (.cons d13 (.single d14))))))))))))), fun x hx => by rw [u14.mem]; exact hR11 x hx,
      by rw [u14.regs, upd_ne (by decide) (by decide), u13.regs, k12' sp (by decide)]; exact rsp,
      fun q hq => by rw [u14.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide), u13.regs,
        k12' q (by revert hq; revert q; decide)], .inl ⟨⟨u14.pc, by rw [u14.mem], fun _ => rfl⟩, by
          rw [u14.regs]; simp +decide only [upd, ↓reduceIte]; rw [u13.self.zero]; rfl, fun h => h4 h.2.2⟩⟩
  obtain ⟨tg, xv, yv, idb⟩ := ok11 h4
  obtain ⟨n13, d13, u13⟩ := u12.self.notTaken C11.self 0x86 pv_at_84 (by decide) (by
    show (reg n12 a0 != reg n12 x0) = false; rw [e12, tg, u12.self.zero]; rfl)
  refine ⟨n13, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.cons d6 (.cons d7 (.cons d8 (.cons d9 (c10.trans (c11.trans (.cons d12 (.single d13)))))))))))), fun x hx => by rw [u13.mem]; exact hR11 x hx,
    by rw [u13.regs, k12' sp (by decide)]; exact rsp,
    fun q hq => by rw [u13.regs, k12' q (by revert hq; revert q; decide)], .inr ⟨⟨u13.pc, by rw [u13.mem], fun _ => rfl⟩,
      ⟨h1, h2, h4⟩, by rw [u13.mem]; exact C11, by rw [u13.mem]; exact D11, ?_, ?_, ?_⟩⟩
  · rw [u13.mem, ← xv, show B + 0x420 + BitVec.ofNat 32 0xBC = B + BitVec.ofNat 32 0x4D8 + BitVec.ofNat 32 4 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
  · rw [u13.mem, ← yv, show B + 0x420 + BitVec.ofNat 32 0xEC = B + BitVec.ofNat 32 0x4D8 + BitVec.ofNat 32 0x34 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
  · rw [u13.mem, ← idb, show B + 0x420 + BitVec.ofNat 32 0x11C = B + BitVec.ofNat 32 0x4D8 + BitVec.ofNat 32 0x64 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]

end C3.RV32.Pv
