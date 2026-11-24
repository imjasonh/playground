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
      reg n' a0 = reg n a3 ∧ reg n' a1 = 0x30 ∧ reg n' a2 = (img% p384OrderBeAddress) ∧ reg n' a3 = 0x30 ∧
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

abbrev ISRN : Word := (img% p384OrderBeAddress)

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

theorem accV_eq_zero_iff {M : Word → BitVec 8} {x : Word} :
    ∀ k, accV M x k = 0 ↔ ∀ i, i < k → memLoad32 M (x + BitVec.ofNat 32 (4 * i)) = 0
  | 0 => ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | k + 1 => by
    rw [accV_succ1]
    have ih := accV_eq_zero_iff (M := M) (x := x) k
    have hp : 0 < 2 ^ (32 * k) := Nat.two_pow_pos _
    constructor
    · intro h i hi
      have h1 : accV M x k = 0 := by omega
      have h2 : (memLoad32 M (x + BitVec.ofNat 32 (4 * k))).toNat = 0 := by
        rcases Nat.eq_zero_or_pos (memLoad32 M (x + BitVec.ofNat 32 (4 * k))).toNat with h3 | h3
        · exact h3
        · exfalso; have := Nat.mul_pos h3 hp; omega
      rcases Nat.lt_or_ge i k with hik | hik
      · exact ih.1 h1 i hik
      · obtain rfl : i = k := by omega
        exact BitVec.eq_of_toNat_eq h2
    · intro h
      rw [ih.2 (fun i hi => h i (by omega)), h k (by omega), show (0 : Word).toNat = 0 from rfl]; simp

def pvB1 : List BInstr :=
  [.aluImm .add (8 : Fin 32) sp 0x7FF, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x581, .aluImm .add a1 sp 0xBC,
   .aluImm .add a0 sp 0x58, .aluImm .add a2 x0 0x60]
def pvB2 : List BInstr :=
  [.lbu (18 : Fin 32) sp 0x11C, .lui a0 0x1000, .aluImm .add a0 a0 0x294, .alu .add a0 a0 sp, .alu .add a1 x0 (9 : Fin 32)]
def pvB3 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x298, .alu .add a1 sp a0, .aluImm .add a0 sp 0x270, .aluImm .add a2 x0 0x30]
def pvB4 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x294, .alu .add a0 a0 sp, .alu .add a1 x0 (21 : Fin 32)]
def pvB5 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x298, .alu .add a1 sp a0, .lui a0 0x1000, .aluImm .add a0 a0 0x7A4,
   .alu .add a0 a0 sp, .aluImm .add a2 x0 0x30]
def pvB6 : List BInstr := [.aluImm .add a0 sp 0x270]
def pvB7 : List BInstr := [.aluImm .and a0 a0 0xFF]
def pvB8 : List BInstr := [.lui a0 0x1000, .aluImm .add a0 a0 0x7A4, .alu .add a0 a0 sp]

theorem pvB1_end : blockEnd p384VerifyPrehashCode 0x86 pvB1 = some 0x96 := by decide
theorem pvB2_end : blockEnd p384VerifyPrehashCode 0x9E pvB2 = some 0xAC := by decide
theorem pvB3_end : blockEnd p384VerifyPrehashCode 0xBA pvB3 = some 0xCA := by decide
theorem pvB4_end : blockEnd p384VerifyPrehashCode 0xD2 pvB4 = some 0xDC := by decide
theorem pvB5_end : blockEnd p384VerifyPrehashCode 0xEA pvB5 = some 0x100 := by decide
theorem pvB6_end : blockEnd p384VerifyPrehashCode 0x108 pvB6 = some 0x10A := by decide
theorem pvB7a_end : blockEnd p384VerifyPrehashCode 0x112 pvB7 = some 0x116 := by decide
theorem pvB8_end : blockEnd p384VerifyPrehashCode 0x118 pvB8 = some 0x120 := by decide
theorem pvB7b_end : blockEnd p384VerifyPrehashCode 0x128 pvB7 = some 0x12C := by decide

theorem accV_S {M M' : Word → BitVec 8} {S : Word} {c d : Nat} :
    ∀ k, (∀ q, q < 4 * k → M' (S + BitVec.ofNat 32 (c + q)) = M (S + BitVec.ofNat 32 (d + q))) →
    accV M' (S + BitVec.ofNat 32 c) k = accV M (S + BitVec.ofNat 32 d) k :=
  fun k h => accV_congr2 k fun i hi => by
    rw [ld_ofNat, ld_ofNat]
    simp only [add_ofNat_assoc, Nat.add_assoc]
    rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The other checks: `r` and `s` below the order, and neither zero. -/
def PvCk2 (M : Word → BitVec 8) (rp sp' : Word) : Prop :=
  beNat (memBytes M rp 48) < n384 ∧ beNat (memBytes M sp' 48) < n384 ∧ beNat (memBytes M rp 48) ≠ 0 ∧
    beNat (memBytes M sp' 48) ≠ 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The other checks**, from 0x86 to 0x156: copy the key's coordinates,
read `r` and `s` with `from_slice`, and test them for zero, or jump to the
return of 0. -/
theorem pv_stA2 {M : Word → BitVec 8} {n : Machine} {B rp sp' : Word} (C : PvCode M) (D : PvData M)
    (F : Fr B 0x21A0) (s : St M PV n 0x86 (reg n)) (rsp : reg n sp = B + 0x420) (r9 : reg n (9 : Fin 32) = rp)
    (r21 : reg n (21 : Fin 32) = sp') (sR : Sep rp 48 (B + 0xFFFFFE60) 0x230C)
    (sS : Sep sp' 48 (B + 0xFFFFFE60) 0x230C) :
    ∃ n', Steps n n' ∧ (∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n'.mem x = M x) ∧ reg n' sp = B + 0x420 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 9, 19, 20, 21] → reg n' q = reg n q) ∧
      ((St n'.mem PV n' 0x130 (reg n') ∧ reg n' a0 = 0 ∧ ¬ PvCk2 M rp sp') ∨
       (St n'.mem PV n' 0x156 (reg n') ∧ PvCk2 M rp sp' ∧ PvCode n'.mem ∧ PvData n'.mem ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x58) 12 = accV M (B + 0x420 + BitVec.ofNat 32 0xBC) 12 ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x88) 12 = accV M (B + 0x420 + BitVec.ofNat 32 0xEC) 12 ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12 = beNat (memBytes M rp 48) ∧
        accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x17A4) 12 = beNat (memBytes M sp' 48) ∧
        reg n' (18 : Fin 32) = (M (B + 0x420 + BitVec.ofNat 32 0x11C)).zeroExtend 32 ∧
        reg n' (8 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80)) := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFl := FS.lo; have hFh := FS.hi; have hFa := FS.al
  obtain ⟨fA, fW, hFC⟩ := FS.mc
  have hb16 : (B + 0x420 + 0xFFFFFFF0).toNat = (B + 0x420).toNat - 16 := FS.below 16 (by decide) (by decide)
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (B + 0x420 + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)
  have inR : ∀ {c l : Nat} {x : Word}, c + l ≤ 0x1D4C → Sep (B + 0xFFFFFE60) 0x230C x 1 →
      Sep (B + 0x420 + BitVec.ofNat 32 c) l x 1 := fun h hx => pvR_hi hx h
  have loR : ∀ {k : Nat} {x : Word}, k ≤ 0x5C0 → 0 < k → Sep (B + 0xFFFFFE60) 0x230C x 1 →
      Sep (B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - k)) k x 1 := fun h h0 hx => pvR_lo hx h h0
  -- copy the key's coordinates
  obtain ⟨n1, c1, u1⟩ := s.block pvB1 C.self pvB1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock pvB1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, fr2, k2⟩ := c_memcpy (dst := B + 0x420 + BitVec.ofNat 32 0x58)
    (src := B + 0x420 + BitVec.ofNat 32 0xBC) (S := B + 0x420) (N := 0x60)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M PV n1 0x96 (reg n1)) C.self C.K pv_at_96 pv_at_9a (by decide) (by decide)
    (by rw [r1, runBlock_reg _ _ _ sp hz (by decide)]; exact rsp)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, pvB1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, pvB1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, pvB1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    ⟨C.K.body, FS.sepHi (by decide) (by decide) (by decide), hFC, FS.mcN (by decide), FS.mcN (by decide),
      sepS (B + 0x420) (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [FS.at _ (by decide)]; omega,
      by rw [FS.at _ (by decide)]; omega⟩
  have fr2' : ∀ x, Sep (B + 0x420 + 0xFFFFFFF0) 16 x 1 → Sep (B + 0x420 + BitVec.ofNat 32 0x58) 0x60 x 1 →
      n2.mem x = M x := fun x a b => by rw [fr2 x a, copyBytes_sep b (Nat.le_refl _)]
  have hb1A : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
  have hiR : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (B + 0xFFFFFE60) 0x230C x 1 := fun x hx =>
    sep_of_le (by rw [hb1A]; omega) (by have := x.isLt; omega)
  have bigR : ∀ {x : Word}, Sep (B + 0xFFFFFE60) (0x21A0 + 0x1A0) x 1 → Sep (B + 0xFFFFFE60) 0x230C x 1 :=
    fun hx => by have := hx.sub (c := 0) (l := 0x230C) (by decide); rwa [add_ofNat_zero] at this
  have hR2 : ∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n2.mem x = M x := fun x hx =>
    fr2' x (loR (k := 16) (by decide) (by decide) hx) (inR (by decide) hx)
  have C2 : PvCode n2.mem := C.hi fun x hx => hR2 x (hiR x hx)
  have D2 : PvData n2.mem := D.of F fun x hx => hR2 x (bigR hx)
  have kc : ∀ {m m' : Machine}, (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg m' q = reg m q) →
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q :=
    fun h q hq => h q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
  have k2' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n q :=
    fun q hq => by rw [kc k2 q (by revert hq; revert q; decide), r1,
      runBlock_reg _ _ _ q hz (by simp only [pvB1]; revert hq; revert q; decide)]
  have e28 : reg n2 (8 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80 := by
    rw [kc k2 8 (by decide), r1]; simp +decide only [runBlock, BInstr.run, pvB1, upd, ↓reduceIte]; rw [rsp]
    show B + 0x420 + 0x7FF + 0x581 = B + 0x420 + BitVec.ofNat 32 0xD80; rw [BitVec.add_assoc]; rfl
  have sp2 : reg n2 sp = B + 0x420 := by rw [k2' sp (by decide)]; exact rsp
  -- from_slice(r)
  obtain ⟨n3, c3, u3⟩ := u2.block pvB2 C2.self pvB2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock pvB2 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have v318 : reg n3 (18 : Fin 32) = (M (B + 0x420 + BitVec.ofNat 32 0x11C)).zeroExtend 32 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, pvB2, upd, ↓reduceIte]; rw [sp2]
    show (n2.mem (B + 0x420 + BitVec.ofNat 32 0x11C)).zeroExtend 32 = _
    rw [fr2' _ (FS.lowB hb16 (by decide) (by decide)) (sepS (B + 0x420) (c := 0x58) (n := 0x60) (d := 0x11C) (k := 1)
      (.inl (by decide)) (by decide) (by decide))]
  have sp3 : reg n3 sp = B + 0x420 := by rw [r3, runBlock_reg _ _ _ sp u2.zero (by decide)]; exact sp2
  have sR' : Sep rp 48 (B + 0x420 + 0xFFFFFF10) 0xF0 := by
    have := sR.subR (c := 0x5C0 - 0xF0) (l := 0xF0) (by decide)
    rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x5C0 - 0xF0) = B + 0x420 + 0xFFFFFF10 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl] at this
  have sS' : Sep sp' 48 (B + 0x420 + 0xFFFFFF10) 0xF0 := by
    have := sS.subR (c := 0x5C0 - 0xF0) (l := 0xF0) (by decide)
    rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x5C0 - 0xF0) = B + 0x420 + 0xFFFFFF10 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl] at this
  have mR : memBytes n2.mem rp 48 = memBytes M rp 48 := memBytes_congr fun i hi => hR2 _ (sR.symm.subR (c := i) (l := 1) (by omega))
  have mS : memBytes n2.mem sp' 48 = memBytes M sp' 48 := memBytes_congr fun i hi => hR2 _ (sS.symm.subR (c := i) (l := 1) (by omega))
  obtain ⟨n4, c4, u4, sp4, k4, ok4, bad4, fr4⟩ := c_bf (out := B + 0x420 + BitVec.ofNat 32 0x1294) (b := rp)
    (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St n2.mem PV n3 0xAC (reg n3)) C2.self C2 D2 FS pv_at_ac pv_at_b0 (by decide)
    (by decide) sp3
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, pvB2, upd, ↓reduceIte]; rw [sp2]
        show 0x1000 + 0x294 + (B + 0x420) = B + 0x420 + BitVec.ofNat 32 0x1294; rw [BitVec.add_comm]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, pvB2, upd, ↓reduceIte]; rw [k2' 9 (by decide), r9]
        exact BitVec.zero_add _) (co := 0x1294) (by decide) rfl (by decide) sR'
  rw [mR] at ok4 bad4
  have hR4 : ∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n4.mem x = M x := fun x hx => by
    rw [fr4 x (loR (k := 0xF0) (by decide) (by decide) hx) (inR (by decide) hx), hR2 x hx]
  have C4 : PvCode n4.mem := C.hi fun x hx => hR4 x (hiR x hx)
  have D4 : PvData n4.mem := D.of F fun x hx => hR4 x (bigR hx)
  have k4' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n3 q :=
    fun q hq => by
      by_cases h : q = sp
      · subst h; rw [sp4, sp3]
      · exact k4 q (by revert hq h; revert q; decide)
  have k34 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n q := fun q hq => by
    rw [k4' q (by revert hq; revert q; decide), r3, runBlock_reg _ _ _ q u2.zero (by simp only [pvB2]; revert hq; revert q; decide),
      k2' q (by revert hq; revert q; decide)]
  have e48 : reg n4 (8 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80 := by
    rw [k4' 8 (by decide), r3, runBlock_reg _ _ _ 8 u2.zero (by decide), e28]
  have e418 : reg n4 (18 : Fin 32) = (M (B + 0x420 + BitVec.ofNat 32 0x11C)).zeroExtend 32 := by
    rw [k4' 18 (by decide), v318]
  have a1294 : B + 0x420 + BitVec.ofNat 32 0xD80 + 0x514 = B + 0x420 + BitVec.ofNat 32 0x1294 := by
    rw [BitVec.add_assoc]; rfl
  obtain ⟨n5, d5, u5⟩ := u4.lw C4.self pv_at_b4 (off' := 0xB8) (by decide)
    (by rw [e48, a1294, FS.at _ (by decide)]; omega)
  have e5 : reg n5 a0 = memLoad32 n4.mem (B + 0x420 + BitVec.ofNat 32 0x1294) := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]; rw [e48, a1294]
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n4 q :=
    fun q hq => by rw [u5.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  -- the fail exit through 0x12E
  have fail : ∀ {m : Machine} {Mm : Word → BitVec 8}, St Mm PV m 0x12E (reg m) → CodeIn Mm PV p384VerifyPrehashCode →
      (∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → Mm x = M x) → Steps n m →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 19, 20, 21] → reg m q = reg n q) → ¬ PvCk2 M rp sp' →
      ∃ n', Steps n n' ∧ (∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n'.mem x = M x) ∧ reg n' sp = B + 0x420 ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 9, 19, 20, 21] → reg n' q = reg n q) ∧
        ((St n'.mem PV n' 0x130 (reg n') ∧ reg n' a0 = 0 ∧ ¬ PvCk2 M rp sp') ∨
         (St n'.mem PV n' 0x156 (reg n') ∧ PvCk2 M rp sp' ∧ PvCode n'.mem ∧ PvData n'.mem ∧
          accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x58) 12 = accV M (B + 0x420 + BitVec.ofNat 32 0xBC) 12 ∧
          accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x88) 12 = accV M (B + 0x420 + BitVec.ofNat 32 0xEC) 12 ∧
          accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12 = beNat (memBytes M rp 48) ∧
          accV n'.mem (B + 0x420 + BitVec.ofNat 32 0x17A4) 12 = beNat (memBytes M sp' 48) ∧
          reg n' (18 : Fin 32) = (M (B + 0x420 + BitVec.ofNat 32 0x11C)).zeroExtend 32 ∧
          reg n' (8 : Fin 32) = B + 0x420 + BitVec.ofNat 32 0xD80)) := fun {m Mm} sm cm fm cs km nk => by
    obtain ⟨m1, d1, w1⟩ := sm.aluImm cm pv_at_12e (off' := 0x130) (by decide)
    exact ⟨m1, cs.trans (.single d1), fun x hx => by rw [w1.mem]; exact fm x hx,
      by rw [w1.regs, upd_ne (by decide) (by decide), km sp (by decide)]; exact rsp,
      fun q hq => by rw [w1.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide),
        km q (by revert hq; revert q; decide)],
      .inl ⟨⟨w1.pc, by rw [w1.mem], fun _ => rfl⟩, by rw [w1.regs]; simp +decide only [upd, ↓reduceIte]; rw [sm.zero]; rfl,
        nk⟩⟩
  by_cases hr : beNat (memBytes M rp 48) < n384
  case neg =>
    obtain ⟨n6, d6, u6⟩ := u5.self.taken C4.self 0x12E pv_at_b8 (by decide) (by
      show (reg n5 a0 != reg n5 x0) = true; rw [e5, bad4 (by omega), u5.self.zero]; rfl)
    exact fail u6.self C4.self hR4
      (c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (.single d6))))))
      (fun q hq => by rw [u6.regs, k5 q (by revert hq; revert q; decide), k34 q (by revert hq; revert q; decide)])
      (fun h => hr h.1)
  obtain ⟨tg4, vr4⟩ := ok4 hr
  have hbF0 : (B + 0x420 + 0xFFFFFF10).toNat = (B + 0x420).toNat - 0xF0 := FS.below 0xF0 (by decide) (by decide)
  have hb54 : (B + 0x420 + 0xFFFFFFAC).toNat = (B + 0x420).toNat - 0x54 := FS.below 0x54 (by decide) (by decide)
  have e1298 : B + 0x420 + BitVec.ofNat 32 0x1298 = B + 0x420 + BitVec.ofNat 32 0x1294 + 4 := by
    simp only [BitVec.add_assoc]; rfl
  have p4 : ∀ d, d + 1 ≤ 0x1D80 → (0x1294 + 52 ≤ d ∨ d + 1 ≤ 0x1294) →
      n4.mem (B + 0x420 + BitVec.ofNat 32 d) = n2.mem (B + 0x420 + BitVec.ofNat 32 d) := fun d h1 h2 =>
    fr4 _ (FS.lowB hbF0 (by decide) h1) (sepS (B + 0x420) h2 (by omega) (by omega))
  -- copy r
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken C4.self 0xBA pv_at_b8 (by decide) (by
    show (reg n5 a0 != reg n5 x0) = false; rw [e5, tg4, u5.self.zero]; rfl)
  have t6 : Steps n n6 := c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (.single d6)))))
  have I6 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n6 q = reg n4 q := fun q hq => by rw [u6.regs, k5 q hq]
  obtain ⟨n7, c7, u7⟩ := u6.self.block pvB3 C4.self pvB3_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have rb7 : ∀ q, reg n7 q = (runBlock pvB3 (n4.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have I7 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n7 q = reg n4 q := fun q hq => by
    rw [rb7, runBlock_reg _ _ _ q u6.self.zero (by simp only [pvB3]; revert hq; revert q; decide), I6 q hq]
  have sp6 : reg n6 sp = B + 0x420 := by rw [I6 sp (by decide), sp4]
  obtain ⟨n8, c8, u8, fr8, k8⟩ := c_memcpy (dst := B + 0x420 + BitVec.ofNat 32 0x270)
    (src := B + 0x420 + BitVec.ofNat 32 0x1298) (S := B + 0x420) (N := 0x30)
    (⟨u7.pc, u7.mem, fun _ => rfl⟩ : St n4.mem PV n7 0xCA (reg n7)) C4.self C4.K pv_at_ca pv_at_ce (by decide) (by decide)
    (by rw [I7 sp (by decide), sp4])
    (by rw [rb7]; simp +decide only [runBlock, BInstr.run, pvB3, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [rb7]; simp +decide only [runBlock, BInstr.run, pvB3, upd, ↓reduceIte]; rw [sp6]; rfl)
    (by rw [rb7]; simp +decide only [runBlock, BInstr.run, pvB3, upd, ↓reduceIte]; (try rw [u6.self.zero]); try rfl)
    ⟨C4.K.body, FS.sepHi (by decide) (by decide) (by decide), hFC, FS.mcN (by decide), FS.mcN (by decide),
      sepS (B + 0x420) (.inl (by decide)) (by decide) (by decide), fA, fW, by rw [FS.at _ (by decide)]; omega,
      by rw [FS.at _ (by decide)]; omega⟩
  have t8 : Steps n n8 := t6.trans (c7.trans c8)
  have hR8 : ∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n8.mem x = M x := fun x hx => by
    rw [fr8 x (loR (k := 16) (by decide) (by decide) hx),
      copyBytes_sep (inR (c := 0x270) (l := 0x30) (by decide) hx) (Nat.le_refl _), hR4 x hx]
  have C8 : PvCode n8.mem := C.hi fun x hx => hR8 x (hiR x hx)
  have D8 : PvData n8.mem := D.of F fun x hx => hR8 x (bigR hx)
  have I8 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n4 q := fun q hq => by
    rw [kc k8 q hq, I7 q hq]
  have p8 : ∀ d, d + 1 ≤ 0x1D80 → (0x270 + 0x30 ≤ d ∨ d + 1 ≤ 0x270) →
      n8.mem (B + 0x420 + BitVec.ofNat 32 d) = n4.mem (B + 0x420 + BitVec.ofNat 32 d) := fun d h1 h2 => by
    rw [fr8 _ (FS.lowB hb16 (by decide) h1), copyBytes_sep (sepS (B + 0x420) h2 (by omega) (by omega)) (Nat.le_refl _)]
  have V8 : accV n8.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12 = beNat (memBytes M rp 48) := by
    rw [← vr4, ← e1298]
    exact accV_S 12 fun q hq => by
      rw [fr8 _ (FS.lowB hb16 (by decide) (by omega)), ← add_ofNat_assoc (B + 0x420) 0x270 q,
        cp_at (by omega) (by decide), add_ofNat_assoc]
  -- from_slice(s)
  obtain ⟨n9, c9, u9⟩ := u8.block pvB4 C8.self pvB4_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have rb9 : ∀ q, reg n9 q = (runBlock pvB4 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have I9 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n9 q = reg n4 q := fun q hq => by
    rw [rb9, runBlock_reg _ _ _ q u8.zero (by simp only [pvB4]; revert hq; revert q; decide), I8 q hq]
  have sp8 : reg n8 sp = B + 0x420 := by rw [I8 sp (by decide), sp4]
  have mS8 : memBytes n8.mem sp' 48 = memBytes M sp' 48 :=
    memBytes_congr fun i hi => hR8 _ (sS.symm.subR (c := i) (l := 1) (by omega))
  obtain ⟨n10, c10, u10, sp10, k10, ok10, bad10, fr10⟩ := c_bf (out := B + 0x420 + BitVec.ofNat 32 0x1294) (b := sp')
    (⟨u9.pc, u9.mem, fun _ => rfl⟩ : St n8.mem PV n9 0xDC (reg n9)) C8.self C8 D8 FS pv_at_dc pv_at_e0 (by decide)
    (by decide) (by rw [I9 sp (by decide), sp4])
    (by rw [rb9]; simp +decide only [runBlock, BInstr.run, pvB4, upd, ↓reduceIte]; rw [sp8]
        show 0x1000 + 0x294 + (B + 0x420) = B + 0x420 + BitVec.ofNat 32 0x1294; rw [BitVec.add_comm]; rfl)
    (by rw [rb9]; simp +decide only [runBlock, BInstr.run, pvB4, upd, ↓reduceIte]
        rw [I8 21 (by decide), k34 21 (by decide), r21]
        exact BitVec.zero_add _) (co := 0x1294) (by decide) rfl (by decide) sS'
  rw [mS8] at ok10 bad10
  have t10 : Steps n n10 := t8.trans (c9.trans c10)
  have hR10 : ∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n10.mem x = M x := fun x hx => by
    rw [fr10 x (loR (k := 0xF0) (by decide) (by decide) hx) (inR (by decide) hx), hR8 x hx]
  have C10 : PvCode n10.mem := C.hi fun x hx => hR10 x (hiR x hx)
  have I10 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n10 q = reg n4 q := fun q hq => by
    by_cases h : q = sp
    · subst h; rw [sp10, sp4]
    · rw [k10 q (by revert hq h; revert q; decide), I9 q hq]
  have p10 : ∀ d, d + 1 ≤ 0x1D80 → (0x1294 + 52 ≤ d ∨ d + 1 ≤ 0x1294) →
      n10.mem (B + 0x420 + BitVec.ofNat 32 d) = n8.mem (B + 0x420 + BitVec.ofNat 32 d) := fun d h1 h2 =>
    fr10 _ (FS.lowB hbF0 (by decide) h1) (sepS (B + 0x420) h2 (by omega) (by omega))
  obtain ⟨n11, d11, u11⟩ := u10.lw C10.self pv_at_e4 (off' := 0xE8) (by decide)
    (by rw [I10 8 (by decide), e48, a1294, FS.at _ (by decide)]; omega)
  have e11 : reg n11 a0 = memLoad32 n10.mem (B + 0x420 + BitVec.ofNat 32 0x1294) := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]; rw [I10 8 (by decide), e48, a1294]
  have I11 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n11 q = reg n4 q := fun q hq => by
    rw [u11.regs, upd_ne (by revert hq; revert q; decide) (by revert hq; revert q; decide), I10 q hq]
  have t11 : Steps n n11 := t10.trans (.single d11)
  by_cases hs : beNat (memBytes M sp' 48) < n384
  case neg =>
    obtain ⟨n12, d12, u12⟩ := u11.self.taken C10.self 0x12E pv_at_e8 (by decide) (by
      show (reg n11 a0 != reg n11 x0) = true; rw [e11, bad10 (by omega), u11.self.zero]; rfl)
    exact fail u12.self C10.self hR10 (t11.trans (.single d12))
      (fun q hq => by rw [u12.regs, I11 q (by revert hq; revert q; decide), k34 q (by revert hq; revert q; decide)])
      (fun h => hs h.2.1)
  obtain ⟨tg10, vr10⟩ := ok10 hs
  obtain ⟨n12, d12, u12⟩ := u11.self.notTaken C10.self 0xEA pv_at_e8 (by decide) (by
    show (reg n11 a0 != reg n11 x0) = false; rw [e11, tg10, u11.self.zero]; rfl)
  have t12 : Steps n n12 := t11.trans (.single d12)
  have I12 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n12 q = reg n4 q := fun q hq => by rw [u12.regs, I11 q hq]
  -- copy s
  obtain ⟨n13, c13, u13⟩ := u12.self.block pvB5 C10.self pvB5_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have rb13 : ∀ q, reg n13 q = (runBlock pvB5 (n10.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have I13 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n13 q = reg n4 q := fun q hq => by
    rw [rb13, runBlock_reg _ _ _ q u12.self.zero (by simp only [pvB5]; revert hq; revert q; decide), I12 q hq]
  have sp12 : reg n12 sp = B + 0x420 := by rw [I12 sp (by decide), sp4]
  obtain ⟨n14, c14, u14, fr14, k14⟩ := c_memcpy (dst := B + 0x420 + BitVec.ofNat 32 0x17A4)
    (src := B + 0x420 + BitVec.ofNat 32 0x1298) (S := B + 0x420) (N := 0x30)
    (⟨u13.pc, u13.mem, fun _ => rfl⟩ : St n10.mem PV n13 0x100 (reg n13)) C10.self C10.K pv_at_100 pv_at_104
    (by decide) (by decide) (by rw [I13 sp (by decide), sp4])
    (by rw [rb13]; simp +decide only [runBlock, BInstr.run, pvB5, upd, ↓reduceIte]; rw [sp12]
        show 0x1000 + 0x7A4 + (B + 0x420) = B + 0x420 + BitVec.ofNat 32 0x17A4; rw [BitVec.add_comm]; rfl)
    (by rw [rb13]; simp +decide only [runBlock, BInstr.run, pvB5, upd, ↓reduceIte]; rw [sp12]; rfl)
    (by rw [rb13]; simp +decide only [runBlock, BInstr.run, pvB5, upd, ↓reduceIte]; (try rw [u12.self.zero]); try rfl)
    ⟨C10.K.body, FS.sepHi (by decide) (by decide) (by decide), hFC, FS.mcN (by decide), FS.mcN (by decide),
      sepS (B + 0x420) (.inr (by decide)) (by decide) (by decide), fA, fW, by rw [FS.at _ (by decide)]; omega,
      by rw [FS.at _ (by decide)]; omega⟩
  have t14 : Steps n n14 := t12.trans (c13.trans c14)
  have hR14 : ∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n14.mem x = M x := fun x hx => by
    rw [fr14 x (loR (k := 16) (by decide) (by decide) hx),
      copyBytes_sep (inR (c := 0x17A4) (l := 0x30) (by decide) hx) (Nat.le_refl _), hR10 x hx]
  have C14 : PvCode n14.mem := C.hi fun x hx => hR14 x (hiR x hx)
  have I14 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n14 q = reg n4 q := fun q hq => by
    rw [kc k14 q hq, I13 q hq]
  have p14 : ∀ d, d + 1 ≤ 0x1D80 → (0x17A4 + 0x30 ≤ d ∨ d + 1 ≤ 0x17A4) →
      n14.mem (B + 0x420 + BitVec.ofNat 32 d) = n10.mem (B + 0x420 + BitVec.ofNat 32 d) := fun d h1 h2 => by
    rw [fr14 _ (FS.lowB hb16 (by decide) h1), copyBytes_sep (sepS (B + 0x420) h2 (by omega) (by omega)) (Nat.le_refl _)]
  have V14 : accV n14.mem (B + 0x420 + BitVec.ofNat 32 0x17A4) 12 = beNat (memBytes M sp' 48) := by
    rw [← vr10, ← e1298]
    exact accV_S 12 fun q hq => by
      rw [fr14 _ (FS.lowB hb16 (by decide) (by omega)), ← add_ofNat_assoc (B + 0x420) 0x17A4 q,
        cp_at (by omega) (by decide), add_ofNat_assoc]
  have V270 : accV n14.mem (B + 0x420 + BitVec.ofNat 32 0x270) 12 = beNat (memBytes M rp 48) := by
    rw [← V8]; exact accV_S 12 fun q hq => by rw [p14 _ (by omega) (by omega), p10 _ (by omega) (by omega)]
  -- is_zero(r)
  obtain ⟨n15, c15, u15⟩ := u14.block pvB6 C14.self pvB6_end ⟨trivial, trivial⟩
  have rb15 : ∀ q, reg n15 q = (runBlock pvB6 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  have I15 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n15 q = reg n4 q := fun q hq => by
    rw [rb15, runBlock_reg _ _ _ q u14.zero (by simp only [pvB6]; revert hq; revert q; decide), I14 q hq]
  have sp14 : reg n14 sp = B + 0x420 := by rw [I14 sp (by decide), sp4]
  obtain ⟨n16, c16, u16, sp16, a16, k16, fr16⟩ := c_sz (x := B + 0x420 + BitVec.ofNat 32 0x270)
    (⟨u15.pc, u15.mem, fun _ => rfl⟩ : St n14.mem PV n15 0x10A (reg n15)) C14.self C14 FS pv_at_10a pv_at_10e
    (by decide) (by decide) (by rw [I15 sp (by decide), sp4])
    (by rw [rb15]; simp +decide only [runBlock, BInstr.run, pvB6, upd, ↓reduceIte]; rw [sp14]; rfl)
    (cx := 0x270) (by decide) rfl (by decide)
  have t16 : Steps n n16 := t14.trans (c15.trans c16)
  have hR16 : ∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n16.mem x = M x := fun x hx => by
    rw [fr16 x (loR (k := 0x54) (by decide) (by decide) hx), hR14 x hx]
  have C16 : PvCode n16.mem := C.hi fun x hx => hR16 x (hiR x hx)
  have I16 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n16 q = reg n4 q := fun q hq => by
    by_cases h : q = sp
    · subst h; rw [sp16, sp4]
    · rw [k16 q (by revert hq h; revert q; decide), I15 q hq]
  have p16 : ∀ d, d + 1 ≤ 0x1D80 →
      n16.mem (B + 0x420 + BitVec.ofNat 32 d) = n14.mem (B + 0x420 + BitVec.ofNat 32 d) := fun d h1 =>
    fr16 _ (FS.lowB hb54 (by decide) h1)
  obtain ⟨n17, c17, u17⟩ := u16.block pvB7 C16.self pvB7a_end ⟨trivial, trivial⟩
  have s17 : St n16.mem PV n17 0x116 (reg n17) := ⟨u17.pc, u17.mem, fun _ => rfl⟩
  have I17 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n17 q = reg n4 q := fun q hq => by
    rw [u17.regs, runBlock_reg _ _ _ q u16.zero (by simp only [pvB7]; revert hq; revert q; decide), I16 q hq]
  have t17 : Steps n n17 := t16.trans c17
  by_cases hr0 : beNat (memBytes M rp 48) = 0
  case pos =>
    have hz : ∀ i : Nat, i < 12 → memLoad32 n14.mem (B + 0x420 + BitVec.ofNat 32 0x270 + BitVec.ofNat 32 (4 * i)) = 0 :=
      (accV_eq_zero_iff 12).1 (by rw [V270]; exact hr0)
    obtain ⟨n18, d18, u18⟩ := s17.taken C16.self 0x12E pv_at_116 (by decide) (by
      show (reg n17 a0 != reg n17 x0) = true
      rw [u17.regs, u17.regs]; simp +decide only [runBlock, BInstr.run, pvB7, upd, ↓reduceIte]
      rw [a16, ite_eq_left hz]; decide)
    exact fail u18.self C16.self hR16 (t17.trans (.single d18))
      (fun q hq => by rw [u18.regs, I17 q (by revert hq; revert q; decide), k34 q (by revert hq; revert q; decide)])
      (fun h => h.2.2.1 hr0)
  have hnz : ¬ ∀ i : Nat, i < 12 → memLoad32 n14.mem (B + 0x420 + BitVec.ofNat 32 0x270 + BitVec.ofNat 32 (4 * i)) = 0 :=
    fun h => hr0 (by rw [← V270]; exact (accV_eq_zero_iff 12).2 h)
  obtain ⟨n18, d18, u18⟩ := s17.notTaken C16.self 0x118 pv_at_116 (by decide) (by
    show (reg n17 a0 != reg n17 x0) = false
    rw [u17.regs, u17.regs]; simp +decide only [runBlock, BInstr.run, pvB7, upd, ↓reduceIte]
    rw [a16, ite_eq_right hnz]; decide)
  have t18 : Steps n n18 := t17.trans (.single d18)
  have I18 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n18 q = reg n4 q := fun q hq => by rw [u18.regs, I17 q hq]
  -- is_zero(s)
  obtain ⟨n19, c19, u19⟩ := u18.self.block pvB8 C16.self pvB8_end ⟨trivial, trivial, trivial, trivial⟩
  have rb19 : ∀ q, reg n19 q = (runBlock pvB8 (n16.mem, reg n18)).2 q := fun q => by rw [u19.regs]
  have I19 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n19 q = reg n4 q := fun q hq => by
    rw [rb19, runBlock_reg _ _ _ q u18.self.zero (by simp only [pvB8]; revert hq; revert q; decide), I18 q hq]
  have sp18 : reg n18 sp = B + 0x420 := by rw [I18 sp (by decide), sp4]
  obtain ⟨n20, c20, u20, sp20, a20, k20, fr20⟩ := c_sz (x := B + 0x420 + BitVec.ofNat 32 0x17A4)
    (⟨u19.pc, u19.mem, fun _ => rfl⟩ : St n16.mem PV n19 0x120 (reg n19)) C16.self C16 FS pv_at_120 pv_at_124
    (by decide) (by decide) (by rw [I19 sp (by decide), sp4])
    (by rw [rb19]; simp +decide only [runBlock, BInstr.run, pvB8, upd, ↓reduceIte]; rw [sp18]
        show 0x1000 + 0x7A4 + (B + 0x420) = B + 0x420 + BitVec.ofNat 32 0x17A4; rw [BitVec.add_comm]; rfl)
    (cx := 0x17A4) (by decide) rfl (by decide)
  have t20 : Steps n n20 := t18.trans (c19.trans c20)
  have hR20 : ∀ x, Sep (B + 0xFFFFFE60) 0x230C x 1 → n20.mem x = M x := fun x hx => by
    rw [fr20 x (loR (k := 0x54) (by decide) (by decide) hx), hR16 x hx]
  have C20 : PvCode n20.mem := C.hi fun x hx => hR20 x (hiR x hx)
  have D20 : PvData n20.mem := D.of F fun x hx => hR20 x (bigR hx)
  have I20 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n20 q = reg n4 q := fun q hq => by
    by_cases h : q = sp
    · subst h; rw [sp20, sp4]
    · rw [k20 q (by revert hq h; revert q; decide), I19 q hq]
  have p20 : ∀ d, d + 1 ≤ 0x1D80 →
      n20.mem (B + 0x420 + BitVec.ofNat 32 d) = n16.mem (B + 0x420 + BitVec.ofNat 32 d) := fun d h1 =>
    fr20 _ (FS.lowB hb54 (by decide) h1)
  have V17 : accV n16.mem (B + 0x420 + BitVec.ofNat 32 0x17A4) 12 = beNat (memBytes M sp' 48) := by
    rw [← V14]; exact accV_S 12 fun q hq => by rw [p16 _ (by omega)]
  obtain ⟨n21, c21, u21⟩ := u20.block pvB7 C20.self pvB7b_end ⟨trivial, trivial⟩
  have s21 : St n20.mem PV n21 0x12C (reg n21) := ⟨u21.pc, u21.mem, fun _ => rfl⟩
  have I21 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n21 q = reg n4 q := fun q hq => by
    rw [u21.regs, runBlock_reg _ _ _ q u20.zero (by simp only [pvB7]; revert hq; revert q; decide), I20 q hq]
  have t21 : Steps n n21 := t20.trans c21
  by_cases hs0 : beNat (memBytes M sp' 48) = 0
  case pos =>
    have hz : ∀ i : Nat, i < 12 → memLoad32 n16.mem (B + 0x420 + BitVec.ofNat 32 0x17A4 + BitVec.ofNat 32 (4 * i)) = 0 :=
      (accV_eq_zero_iff 12).1 (by rw [V17]; exact hs0)
    obtain ⟨n22, d22, u22⟩ := s21.notTaken C20.self 0x12E pv_at_12c (by decide) (by
      show (reg n21 a0 == reg n21 x0) = false
      rw [u21.regs, u21.regs]; simp +decide only [runBlock, BInstr.run, pvB7, upd, ↓reduceIte]
      rw [a20, ite_eq_left hz]; decide)
    exact fail u22.self C20.self hR20 (t21.trans (.single d22))
      (fun q hq => by rw [u22.regs, I21 q (by revert hq; revert q; decide), k34 q (by revert hq; revert q; decide)])
      (fun h => h.2.2.2 hs0)
  have hnz2 : ¬ ∀ i : Nat, i < 12 →
      memLoad32 n16.mem (B + 0x420 + BitVec.ofNat 32 0x17A4 + BitVec.ofNat 32 (4 * i)) = 0 :=
    fun h => hs0 (by rw [← V17]; exact (accV_eq_zero_iff 12).2 h)
  obtain ⟨n22, d22, u22⟩ := s21.taken C20.self 0x156 pv_at_12c (by decide) (by
    show (reg n21 a0 == reg n21 x0) = true
    rw [u21.regs, u21.regs]; simp +decide only [runBlock, BInstr.run, pvB7, upd, ↓reduceIte]
    rw [a20, ite_eq_right hnz2]; decide)
  refine ⟨n22, t21.trans (.single d22), fun x hx => by rw [u22.mem]; exact hR20 x hx,
    by rw [u22.regs, I21 sp (by decide), sp4],
    fun q hq => by rw [u22.regs, I21 q (by revert hq; revert q; decide), k34 q (by revert hq; revert q; decide)],
    .inr ⟨⟨u22.pc, rfl, fun _ => rfl⟩, ⟨hr, hs, hr0, hs0⟩, by rw [u22.mem]; exact C20, by rw [u22.mem]; exact D20,
      ?_, ?_, ?_, ?_, by rw [u22.regs, I21 18 (by decide), e418], by rw [u22.regs, I21 8 (by decide), e48]⟩⟩
  · rw [u22.mem]
    exact accV_S 12 fun q hq => by
      rw [p20 _ (by omega), p16 _ (by omega), p14 _ (by omega) (by omega), p10 _ (by omega) (by omega),
        p8 _ (by omega) (by omega), p4 _ (by omega) (by omega), fr2 _ (FS.lowB hb16 (by decide) (by omega)),
        ← add_ofNat_assoc (B + 0x420) 0x58 q, cp_at (by omega) (by decide), add_ofNat_assoc]
  · rw [u22.mem]
    exact accV_S 12 fun q hq => by
      rw [p20 _ (by omega), p16 _ (by omega), p14 _ (by omega) (by omega), p10 _ (by omega) (by omega),
        p8 _ (by omega) (by omega), p4 _ (by omega) (by omega), fr2 _ (FS.lowB hb16 (by decide) (by omega)),
        show 0x88 + q = 0x58 + (0x30 + q) by omega, ← add_ofNat_assoc (B + 0x420) 0x58 (0x30 + q),
        cp_at (by omega) (by decide), add_ofNat_assoc, show 0xBC + (0x30 + q) = 0xEC + q by omega]
  · rw [u22.mem, ← V270]
    exact accV_S 12 fun q hq => by rw [p20 _ (by omega), p16 _ (by omega)]
  · rw [u22.mem, ← V17]
    exact accV_S 12 fun q hq => by rw [p20 _ (by omega)]

end C3.RV32.Pv
