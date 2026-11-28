import C3BootProofs.Proofs.ScalarMontFacts

/-! # `montgomery_mul`'s body, segments 31 to 34

Each theorem steps 40 instructions. `scripts/gen-scalar-mont.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g31 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v169 v186 v226 v272 v274 v278 v280 v293 v314 v322 v355 v382 v384 v386 v401 v455 v470 v507 v523 v641 v645 v647 v662 v700 v733 v739 v747 v827 v830 v843 v946 v961 v987 v990 v992 v995 v996 v997 v998 v999 : Word}
    (s : St Mi B n 0xC06 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v314)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v747)
    (q6 : reg n (6 : Fin 32) = v992)
    (q7 : reg n (7 : Fin 32) = v998)
    (q8 : reg n (8 : Fin 32) = v961)
    (q9 : reg n (9 : Fin 32) = v997)
    (q10 : reg n a0 = v996)
    (q11 : reg n a1 = v186)
    (q12 : reg n a2 = v999)
    (q13 : reg n a3 = v995)
    (q14 : reg n a4 = v987)
    (q15 : reg n a5 = v990)
    (q16 : reg n a6 = v386)
    (q17 : reg n a7 = v278)
    (q18 : reg n (18 : Fin 32) = v662)
    (q19 : reg n (19 : Fin 32) = v827)
    (q20 : reg n (20 : Fin 32) = v946)
    (q21 : reg n (21 : Fin 32) = v470)
    (q22 : reg n (22 : Fin 32) = v293)
    (q23 : reg n (23 : Fin 32) = v355)
    (q24 : reg n (24 : Fin 32) = v274)
    (q25 : reg n (25 : Fin 32) = v280)
    (q26 : reg n (26 : Fin 32) = v523)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v830)
    (q29 : reg n (29 : Fin 32) = v272)
    (q30 : reg n (30 : Fin 32) = v322)
    (q31 : reg n (31 : Fin 32) = v843)
    (slA4 : memLoad32 Mi (F + 0xA4) = v647)
    (slB8 : memLoad32 Mi (F + 0xB8) = v641)
    (slC8 : memLoad32 Mi (F + 0xC8) = v507)
    (slD4 : memLoad32 Mi (F + 0xD4) = v455)
    (slE8 : memLoad32 Mi (F + 0xE8) = v384)
    (slEC : memLoad32 Mi (F + 0xEC) = v382)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v401)
    (sl110 : memLoad32 Mi (F + 0x110) = v645)
    (sl118 : memLoad32 Mi (F + 0x118) = v739)
    (sl11C : memLoad32 Mi (F + 0x11C) = v733)
    (sl12C : memLoad32 Mi (F + 0x12C) = v169)
    (sl130 : memLoad32 Mi (F + 0x130) = v226)
    (sl15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C))
    (sl160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160))
    (sl164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164))
    (sl168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168))
    (sl16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C))
    (sl170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170))
    (sl174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174))
    (sl178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178))
    (sl17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C))
    (sl180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180))
    (sl184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184))
    (sl188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188))
    (sl18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1000 v1003 v1004 v1006 v1007 v1008 v1010 v1011 v1012 v1013 v1014 v1015 v1017 v1018 v1020 v1021 v1022 v1023 v1024 v1025 v1026 v1027 v1028 v1029 v1030 v1031 v1032 v1033 v1034 v1035 v1036 v1037 v1038 v1039 : Word),
      Steps n n' ∧
      St M' B n' 0xC78 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v314 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v747 ∧
      reg n' (6 : Fin 32) = v992 ∧
      reg n' (7 : Fin 32) = v1037 ∧
      reg n' (8 : Fin 32) = v1021 ∧
      reg n' (9 : Fin 32) = v1013 ∧
      reg n' a0 = v1035 ∧
      reg n' a1 = v1036 ∧
      reg n' a2 = v1034 ∧
      reg n' a3 = v1038 ∧
      reg n' a4 = v1029 ∧
      reg n' a5 = v1039 ∧
      reg n' a6 = v386 ∧
      reg n' a7 = v278 ∧
      reg n' (18 : Fin 32) = v662 ∧
      reg n' (19 : Fin 32) = v827 ∧
      reg n' (20 : Fin 32) = v946 ∧
      reg n' (21 : Fin 32) = v470 ∧
      reg n' (22 : Fin 32) = v384 ∧
      reg n' (23 : Fin 32) = v355 ∧
      reg n' (24 : Fin 32) = v274 ∧
      reg n' (25 : Fin 32) = v280 ∧
      reg n' (26 : Fin 32) = v523 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v830 ∧
      reg n' (29 : Fin 32) = v272 ∧
      reg n' (30 : Fin 32) = v322 ∧
      reg n' (31 : Fin 32) = v843 ∧
      memLoad32 M' (F + 0xC8) = v507 ∧
      memLoad32 M' (F + 0xD4) = v455 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x110) = v645 ∧
      memLoad32 M' (F + 0x118) = v739 ∧
      memLoad32 M' (F + 0x11C) = v733 ∧
      memLoad32 M' (F + 0x130) = v226 ∧
      memLoad32 M' (F + 0x15C) = memLoad32 M0 (F + 0x15C) ∧
      memLoad32 M' (F + 0x160) = memLoad32 M0 (F + 0x160) ∧
      memLoad32 M' (F + 0x164) = memLoad32 M0 (F + 0x164) ∧
      memLoad32 M' (F + 0x168) = memLoad32 M0 (F + 0x168) ∧
      memLoad32 M' (F + 0x16C) = memLoad32 M0 (F + 0x16C) ∧
      memLoad32 M' (F + 0x170) = memLoad32 M0 (F + 0x170) ∧
      memLoad32 M' (F + 0x174) = memLoad32 M0 (F + 0x174) ∧
      memLoad32 M' (F + 0x178) = memLoad32 M0 (F + 0x178) ∧
      memLoad32 M' (F + 0x17C) = memLoad32 M0 (F + 0x17C) ∧
      memLoad32 M' (F + 0x180) = memLoad32 M0 (F + 0x180) ∧
      memLoad32 M' (F + 0x184) = memLoad32 M0 (F + 0x184) ∧
      memLoad32 M' (F + 0x188) = memLoad32 M0 (F + 0x188) ∧
      memLoad32 M' (F + 0x18C) = memLoad32 M0 (F + 0x18C) ∧
      aluEval .sltu v995 v186 = v1000 ∧
      aluEval .add v169 v384 = v1003 ∧
      aluEval .add v1000 v1003 = v1004 ∧
      aluEval .add v999 v647 = v1006 ∧
      aluEval .sub v987 v995 = v1007 ∧
      aluEval .sub v1006 v1004 = v1008 ∧
      aluEval .add v641 v1007 = v1010 ∧
      aluEval .mul v747 v700 = v1011 ∧
      aluEval .sltu v1010 v1007 = v1012 ∧
      aluEval .mulhu v747 v700 = v1013 ∧
      aluEval .add v1008 v1012 = v1014 ∧
      aluEval .mul v843 v355 = v1015 ∧
      aluEval .sll v382 0x14 = v1017 ∧
      aluEval .mulhu v843 v355 = v1018 ∧
      aluEval .srl v401 0xC = v1020 ∧
      aluEval .add v1017 v1010 = v1021 ∧
      aluEval .add v1020 v1014 = v1022 ∧
      aluEval .sltu v1021 v1010 = v1023 ∧
      aluEval .add v1022 v1023 = v1024 ∧
      aluEval .add v1011 v1021 = v1025 ∧
      aluEval .add v1024 v1013 = v1026 ∧
      aluEval .sltu v1025 v1021 = v1027 ∧
      aluEval .add v1026 v1027 = v1028 ∧
      aluEval .add v1015 v1025 = v1029 ∧
      aluEval .add v1028 v1018 = v1030 ∧
      aluEval .sltu v1029 v1025 = v1031 ∧
      aluEval .sll v998 0x3 = v1032 ∧
      aluEval .srl v992 0x1D = v1033 ∧
      aluEval .or v1032 v1033 = v1034 ∧
      aluEval .add v1030 v1031 = v1035 ∧
      aluEval .srl v998 0x1D = v1036 ∧
      aluEval .add v1029 v1034 = v1037 ∧
      aluEval .mul v843 v700 = v1038 ∧
      aluEval .mulhu v843 v700 = v1039 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n1000, v1000, d1000, hv1000, u1000⟩ := s.aluG hc smm_at_c06 (off' := 0xC0A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1000
  obtain ⟨n1001, d1001, u1001⟩ := u1000.lwE hc smm_at_c0a (off' := 0xC0E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 300) (by decide)) (v := v169)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl12C])
  obtain ⟨n1002, d1002, u1002⟩ := u1001.lwE hc smm_at_c0e (off' := 0xC10) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 232) (by decide)) (v := v384)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slE8])
  obtain ⟨n1003, v1003, d1003, hv1003, u1003⟩ := u1002.aluG hc smm_at_c10 (off' := 0xC12) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1003
  obtain ⟨n1004, v1004, d1004, hv1004, u1004⟩ := u1003.aluG hc smm_at_c12 (off' := 0xC14) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1004
  obtain ⟨n1005, d1005, u1005⟩ := u1004.lwE hc smm_at_c14 (off' := 0xC16) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 164) (by decide)) (v := v647)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slA4])
  obtain ⟨n1006, v1006, d1006, hv1006, u1006⟩ := u1005.aluG hc smm_at_c16 (off' := 0xC18) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1006
  obtain ⟨n1007, v1007, d1007, hv1007, u1007⟩ := u1006.aluG hc smm_at_c18 (off' := 0xC1A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1007
  obtain ⟨n1008, v1008, d1008, hv1008, u1008⟩ := u1007.aluG hc smm_at_c1a (off' := 0xC1C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1008
  obtain ⟨n1009, d1009, u1009⟩ := u1008.lwE hc smm_at_c1c (off' := 0xC1E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 184) (by decide)) (v := v641)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slB8])
  obtain ⟨n1010, v1010, d1010, hv1010, u1010⟩ := u1009.aluG hc smm_at_c1e (off' := 0xC20) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1010
  obtain ⟨n1011, v1011, d1011, hv1011, u1011⟩ := u1010.aluG hc smm_at_c20 (off' := 0xC24) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1011
  obtain ⟨n1012, v1012, d1012, hv1012, u1012⟩ := u1011.aluG hc smm_at_c24 (off' := 0xC28) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1012
  obtain ⟨n1013, v1013, d1013, hv1013, u1013⟩ := u1012.aluG hc smm_at_c28 (off' := 0xC2C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1013
  obtain ⟨n1014, v1014, d1014, hv1014, u1014⟩ := u1013.aluG hc smm_at_c2c (off' := 0xC2E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1014
  obtain ⟨n1015, v1015, d1015, hv1015, u1015⟩ := u1014.aluG hc smm_at_c2e (off' := 0xC32) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1015
  obtain ⟨n1016, d1016, u1016⟩ := u1015.lwE hc smm_at_c32 (off' := 0xC34) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 236) (by decide)) (v := v382)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slEC])
  obtain ⟨n1017, v1017, d1017, hv1017, u1017⟩ := u1016.aluImmG hc smm_at_c34 (off' := 0xC36) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1017
  obtain ⟨n1018, v1018, d1018, hv1018, u1018⟩ := u1017.aluG hc smm_at_c36 (off' := 0xC3A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1018
  obtain ⟨n1019, d1019, u1019⟩ := u1018.lwE hc smm_at_c3a (off' := 0xC3E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 256) (by decide)) (v := v401)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl100])
  obtain ⟨n1020, v1020, d1020, hv1020, u1020⟩ := u1019.aluImmG hc smm_at_c3e (off' := 0xC40) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1020
  obtain ⟨n1021, v1021, d1021, hv1021, u1021⟩ := u1020.aluG hc smm_at_c40 (off' := 0xC42) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1021
  obtain ⟨n1022, v1022, d1022, hv1022, u1022⟩ := u1021.aluG hc smm_at_c42 (off' := 0xC44) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1022
  obtain ⟨n1023, v1023, d1023, hv1023, u1023⟩ := u1022.aluG hc smm_at_c44 (off' := 0xC48) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1023
  obtain ⟨n1024, v1024, d1024, hv1024, u1024⟩ := u1023.aluG hc smm_at_c48 (off' := 0xC4A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1024
  obtain ⟨n1025, v1025, d1025, hv1025, u1025⟩ := u1024.aluG hc smm_at_c4a (off' := 0xC4C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1025
  obtain ⟨n1026, v1026, d1026, hv1026, u1026⟩ := u1025.aluG hc smm_at_c4c (off' := 0xC4E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1026
  obtain ⟨n1027, v1027, d1027, hv1027, u1027⟩ := u1026.aluG hc smm_at_c4e (off' := 0xC52) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1027
  obtain ⟨n1028, v1028, d1028, hv1028, u1028⟩ := u1027.aluG hc smm_at_c52 (off' := 0xC54) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1028
  obtain ⟨n1029, v1029, d1029, hv1029, u1029⟩ := u1028.aluG hc smm_at_c54 (off' := 0xC56) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1029
  obtain ⟨n1030, v1030, d1030, hv1030, u1030⟩ := u1029.aluG hc smm_at_c56 (off' := 0xC58) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1030
  obtain ⟨n1031, v1031, d1031, hv1031, u1031⟩ := u1030.aluG hc smm_at_c58 (off' := 0xC5C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1031
  obtain ⟨n1032, v1032, d1032, hv1032, u1032⟩ := u1031.aluImmG hc smm_at_c5c (off' := 0xC60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1032
  obtain ⟨n1033, v1033, d1033, hv1033, u1033⟩ := u1032.aluImmG hc smm_at_c60 (off' := 0xC64) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1033
  obtain ⟨n1034, v1034, d1034, hv1034, u1034⟩ := u1033.aluG hc smm_at_c64 (off' := 0xC66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1034
  obtain ⟨n1035, v1035, d1035, hv1035, u1035⟩ := u1034.aluG hc smm_at_c66 (off' := 0xC68) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1035
  obtain ⟨n1036, v1036, d1036, hv1036, u1036⟩ := u1035.aluImmG hc smm_at_c68 (off' := 0xC6C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1036
  obtain ⟨n1037, v1037, d1037, hv1037, u1037⟩ := u1036.aluG hc smm_at_c6c (off' := 0xC70) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1037
  obtain ⟨n1038, v1038, d1038, hv1038, u1038⟩ := u1037.aluG hc smm_at_c70 (off' := 0xC74) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1038
  obtain ⟨n1039, v1039, d1039, hv1039, u1039⟩ := u1038.aluG hc smm_at_c74 (off' := 0xC78) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1039
  have qo1 : reg n1039 ra = v314 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n1039 sp = F := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n1039 (3 : Fin 32) = G3 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n1039 (4 : Fin 32) = G4 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n1039 (5 : Fin 32) = v747 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n1039 (6 : Fin 32) = v992 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n1039 (7 : Fin 32) = v1037 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n1039 (8 : Fin 32) = v1021 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n1039 (9 : Fin 32) = v1013 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n1039 a0 = v1035 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n1039 a1 = v1036 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n1039 a2 = v1034 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n1039 a3 = v1038 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n1039 a4 = v1029 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n1039 a5 = v1039 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n1039 a6 = v386 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n1039 a7 = v278 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n1039 (18 : Fin 32) = v662 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n1039 (19 : Fin 32) = v827 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n1039 (20 : Fin 32) = v946 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n1039 (21 : Fin 32) = v470 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n1039 (22 : Fin 32) = v384 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n1039 (23 : Fin 32) = v355 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n1039 (24 : Fin 32) = v274 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n1039 (25 : Fin 32) = v280 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n1039 (26 : Fin 32) = v523 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n1039 (27 : Fin 32) = v700 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n1039 (28 : Fin 32) = v830 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n1039 (29 : Fin 32) = v272 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n1039 (30 : Fin 32) = v322 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n1039 (31 : Fin 32) = v843 := by rw [u1039.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC8 : memLoad32 Mi (F + 0xC8) = v507 := by
    rw [slC8]
  have soD4 : memLoad32 Mi (F + 0xD4) = v455 := by
    rw [slD4]
  have soF8 : memLoad32 Mi (F + 0xF8) = outp := by
    rw [slF8]
  have so110 : memLoad32 Mi (F + 0x110) = v645 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v739 := by
    rw [sl118]
  have so11C : memLoad32 Mi (F + 0x11C) = v733 := by
    rw [sl11C]
  have so130 : memLoad32 Mi (F + 0x130) = v226 := by
    rw [sl130]
  have so15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [sl15C]
  have so160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [sl160]
  have so164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [sl164]
  have so168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [sl168]
  have so16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [sl16C]
  have so170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [sl170]
  have so174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [sl174]
  have so178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [sl178]
  have so17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [sl17C]
  have so180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [sl180]
  have so184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [sl184]
  have so188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [sl188]
  have so18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [sl18C]
  exact ⟨n1039, Mi, v1000, v1003, v1004, v1006, v1007, v1008, v1010, v1011, v1012, v1013, v1014, v1015, v1017, v1018, v1020, v1021, v1022, v1023, v1024, v1025, v1026, v1027, v1028, v1029, v1030, v1031, v1032, v1033, v1034, v1035, v1036, v1037, v1038, v1039, (.cons d1000 (.cons d1001 (.cons d1002 (.cons d1003 (.cons d1004 (.cons d1005 (.cons d1006 (.cons d1007 (.cons d1008 (.cons d1009 (.cons d1010 (.cons d1011 (.cons d1012 (.cons d1013 (.cons d1014 (.cons d1015 (.cons d1016 (.cons d1017 (.cons d1018 (.cons d1019 (.cons d1020 (.cons d1021 (.cons d1022 (.cons d1023 (.cons d1024 (.cons d1025 (.cons d1026 (.cons d1027 (.cons d1028 (.cons d1029 (.cons d1030 (.cons d1031 (.cons d1032 (.cons d1033 (.cons d1034 (.cons d1035 (.cons d1036 (.cons d1037 (.cons d1038 (.single d1039)))))))))))))))))))))))))))))))))))))))), u1039.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC8, soD4, soF8, so110, so118, so11C, so130, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv1000, hv1003, hv1004, hv1006, hv1007, hv1008, hv1010, hv1011, hv1012, hv1013, hv1014, hv1015, hv1017, hv1018, hv1020, hv1021, hv1022, hv1023, hv1024, hv1025, hv1026, hv1027, hv1028, hv1029, hv1030, hv1031, hv1032, hv1033, hv1034, hv1035, hv1036, hv1037, hv1038, hv1039⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g32 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v226 v272 v274 v278 v280 v314 v322 v355 v384 v386 v455 v470 v507 v523 v645 v662 v700 v733 v739 v747 v827 v830 v843 v946 v992 v1013 v1021 v1029 v1034 v1035 v1036 v1037 v1038 v1039 : Word}
    (s : St Mi B n 0xC78 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v314)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v747)
    (q6 : reg n (6 : Fin 32) = v992)
    (q7 : reg n (7 : Fin 32) = v1037)
    (q8 : reg n (8 : Fin 32) = v1021)
    (q9 : reg n (9 : Fin 32) = v1013)
    (q10 : reg n a0 = v1035)
    (q11 : reg n a1 = v1036)
    (q12 : reg n a2 = v1034)
    (q13 : reg n a3 = v1038)
    (q14 : reg n a4 = v1029)
    (q15 : reg n a5 = v1039)
    (q16 : reg n a6 = v386)
    (q17 : reg n a7 = v278)
    (q18 : reg n (18 : Fin 32) = v662)
    (q19 : reg n (19 : Fin 32) = v827)
    (q20 : reg n (20 : Fin 32) = v946)
    (q21 : reg n (21 : Fin 32) = v470)
    (q22 : reg n (22 : Fin 32) = v384)
    (q23 : reg n (23 : Fin 32) = v355)
    (q24 : reg n (24 : Fin 32) = v274)
    (q25 : reg n (25 : Fin 32) = v280)
    (q26 : reg n (26 : Fin 32) = v523)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v830)
    (q29 : reg n (29 : Fin 32) = v272)
    (q30 : reg n (30 : Fin 32) = v322)
    (q31 : reg n (31 : Fin 32) = v843)
    (slC8 : memLoad32 Mi (F + 0xC8) = v507)
    (slD4 : memLoad32 Mi (F + 0xD4) = v455)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl110 : memLoad32 Mi (F + 0x110) = v645)
    (sl118 : memLoad32 Mi (F + 0x118) = v739)
    (sl11C : memLoad32 Mi (F + 0x11C) = v733)
    (sl130 : memLoad32 Mi (F + 0x130) = v226)
    (sl15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C))
    (sl160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160))
    (sl164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164))
    (sl168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168))
    (sl16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C))
    (sl170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170))
    (sl174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174))
    (sl178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178))
    (sl17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C))
    (sl180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180))
    (sl184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184))
    (sl188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188))
    (sl18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1040 v1041 v1042 v1044 v1045 v1046 v1048 v1049 v1050 v1051 v1052 v1053 v1054 v1055 v1056 v1057 v1058 v1059 v1060 v1061 v1062 v1063 v1064 v1066 v1067 v1068 v1069 v1070 v1071 v1072 v1073 v1074 v1075 v1076 v1077 v1078 v1079 : Word),
      Steps n n' ∧
      St M' B n' 0xCEE (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v314 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v747 ∧
      reg n' (6 : Fin 32) = v992 ∧
      reg n' (7 : Fin 32) = v1037 ∧
      reg n' (8 : Fin 32) = v1021 ∧
      reg n' (9 : Fin 32) = v1070 ∧
      reg n' a0 = v1062 ∧
      reg n' a1 = v1077 ∧
      reg n' a2 = v739 ∧
      reg n' a3 = v1078 ∧
      reg n' a4 = v1079 ∧
      reg n' a5 = v1067 ∧
      reg n' a6 = v386 ∧
      reg n' a7 = v278 ∧
      reg n' (18 : Fin 32) = v662 ∧
      reg n' (19 : Fin 32) = v827 ∧
      reg n' (20 : Fin 32) = v946 ∧
      reg n' (21 : Fin 32) = v470 ∧
      reg n' (22 : Fin 32) = v384 ∧
      reg n' (23 : Fin 32) = v355 ∧
      reg n' (24 : Fin 32) = v274 ∧
      reg n' (25 : Fin 32) = v280 ∧
      reg n' (26 : Fin 32) = v523 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v1059 ∧
      reg n' (29 : Fin 32) = v1074 ∧
      reg n' (30 : Fin 32) = v322 ∧
      reg n' (31 : Fin 32) = v843 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x110) = v645 ∧
      memLoad32 M' (F + 0x11C) = v733 ∧
      memLoad32 M' (F + 0x130) = v226 ∧
      memLoad32 M' (F + 0x15C) = memLoad32 M0 (F + 0x15C) ∧
      memLoad32 M' (F + 0x160) = memLoad32 M0 (F + 0x160) ∧
      memLoad32 M' (F + 0x164) = memLoad32 M0 (F + 0x164) ∧
      memLoad32 M' (F + 0x168) = memLoad32 M0 (F + 0x168) ∧
      memLoad32 M' (F + 0x16C) = memLoad32 M0 (F + 0x16C) ∧
      memLoad32 M' (F + 0x170) = memLoad32 M0 (F + 0x170) ∧
      memLoad32 M' (F + 0x174) = memLoad32 M0 (F + 0x174) ∧
      memLoad32 M' (F + 0x178) = memLoad32 M0 (F + 0x178) ∧
      memLoad32 M' (F + 0x17C) = memLoad32 M0 (F + 0x17C) ∧
      memLoad32 M' (F + 0x180) = memLoad32 M0 (F + 0x180) ∧
      memLoad32 M' (F + 0x184) = memLoad32 M0 (F + 0x184) ∧
      memLoad32 M' (F + 0x188) = memLoad32 M0 (F + 0x188) ∧
      memLoad32 M' (F + 0x18C) = memLoad32 M0 (F + 0x18C) ∧
      aluEval .add v1035 v1036 = v1040 ∧
      aluEval .sltu v1037 v1029 = v1041 ∧
      aluEval .add v1040 v1041 = v1042 ∧
      aluEval .sll v455 0x14 = v1044 ∧
      aluEval .srl v470 0xC = v1045 ∧
      aluEval .add v1044 v830 = v1046 ∧
      aluEval .add v1045 v739 = v1048 ∧
      aluEval .sltu v1046 v830 = v1049 ∧
      aluEval .add v1048 v1049 = v1050 ∧
      aluEval .sll v1042 0x3 = v1051 ∧
      aluEval .add v1050 v1039 = v1052 ∧
      aluEval .add v1038 v1046 = v1053 ∧
      aluEval .srl v1037 0x1D = v1054 ∧
      aluEval .sltu v1053 v1046 = v1055 ∧
      aluEval .or v1054 v1051 = v1056 ∧
      aluEval .add v1055 v1052 = v1057 ∧
      aluEval .srl v1042 0x1D = v1058 ∧
      aluEval .add v1053 v1056 = v1059 ∧
      aluEval .add v1058 v1057 = v1060 ∧
      aluEval .sltu v1059 v1053 = v1061 ∧
      aluEval .add v1060 v1061 = v1062 ∧
      aluEval .sll v1062 0x3 = v1063 ∧
      aluEval .srl v523 0xC = v1064 ∧
      aluEval .sll v507 0x14 = v1066 ∧
      aluEval .add v1066 v272 = v1067 ∧
      aluEval .add v1064 v278 = v1068 ∧
      aluEval .srl v1059 0x1D = v1069 ∧
      aluEval .sltu v1067 v1066 = v1070 ∧
      aluEval .or v1063 v1069 = v1071 ∧
      aluEval .add v1068 v1070 = v1072 ∧
      aluEval .srl v1062 0x1D = v1073 ∧
      aluEval .add v1067 v1071 = v1074 ∧
      aluEval .add v1072 v1073 = v1075 ∧
      aluEval .sltu v1074 v1067 = v1076 ∧
      aluEval .add v1076 v1075 = v1077 ∧
      aluEval .sll v1077 0x3 = v1078 ∧
      aluEval .srl v662 0xC = v1079 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n1040, v1040, d1040, hv1040, u1040⟩ := s.aluG hc smm_at_c78 (off' := 0xC7A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1040
  obtain ⟨n1041, v1041, d1041, hv1041, u1041⟩ := u1040.aluG hc smm_at_c7a (off' := 0xC7E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1041
  obtain ⟨n1042, v1042, d1042, hv1042, u1042⟩ := u1041.aluG hc smm_at_c7e (off' := 0xC80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1042
  obtain ⟨n1043, d1043, u1043⟩ := u1042.lwE hc smm_at_c80 (off' := 0xC82) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 212) (by decide)) (v := v455)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slD4])
  obtain ⟨n1044, v1044, d1044, hv1044, u1044⟩ := u1043.aluImmG hc smm_at_c82 (off' := 0xC84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1044
  obtain ⟨n1045, v1045, d1045, hv1045, u1045⟩ := u1044.aluImmG hc smm_at_c84 (off' := 0xC88) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1045
  obtain ⟨n1046, v1046, d1046, hv1046, u1046⟩ := u1045.aluG hc smm_at_c88 (off' := 0xC8A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1046
  obtain ⟨n1047, d1047, u1047⟩ := u1046.lwE hc smm_at_c8a (off' := 0xC8E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 280) (by decide)) (v := v739)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl118])
  obtain ⟨n1048, v1048, d1048, hv1048, u1048⟩ := u1047.aluG hc smm_at_c8e (off' := 0xC90) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1048
  obtain ⟨n1049, v1049, d1049, hv1049, u1049⟩ := u1048.aluG hc smm_at_c90 (off' := 0xC94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1049
  obtain ⟨n1050, v1050, d1050, hv1050, u1050⟩ := u1049.aluG hc smm_at_c94 (off' := 0xC96) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1050
  obtain ⟨n1051, v1051, d1051, hv1051, u1051⟩ := u1050.aluImmG hc smm_at_c96 (off' := 0xC9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1051
  obtain ⟨n1052, v1052, d1052, hv1052, u1052⟩ := u1051.aluG hc smm_at_c9a (off' := 0xC9C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1052
  obtain ⟨n1053, v1053, d1053, hv1053, u1053⟩ := u1052.aluG hc smm_at_c9c (off' := 0xC9E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1053
  obtain ⟨n1054, v1054, d1054, hv1054, u1054⟩ := u1053.aluImmG hc smm_at_c9e (off' := 0xCA2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1054
  obtain ⟨n1055, v1055, d1055, hv1055, u1055⟩ := u1054.aluG hc smm_at_ca2 (off' := 0xCA6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1055
  obtain ⟨n1056, v1056, d1056, hv1056, u1056⟩ := u1055.aluG hc smm_at_ca6 (off' := 0xCA8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1056
  obtain ⟨n1057, v1057, d1057, hv1057, u1057⟩ := u1056.aluG hc smm_at_ca8 (off' := 0xCAA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1057
  obtain ⟨n1058, v1058, d1058, hv1058, u1058⟩ := u1057.aluImmG hc smm_at_caa (off' := 0xCAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1058
  obtain ⟨n1059, v1059, d1059, hv1059, u1059⟩ := u1058.aluG hc smm_at_cac (off' := 0xCB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1059
  obtain ⟨n1060, v1060, d1060, hv1060, u1060⟩ := u1059.aluG hc smm_at_cb0 (off' := 0xCB2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1060
  obtain ⟨n1061, v1061, d1061, hv1061, u1061⟩ := u1060.aluG hc smm_at_cb2 (off' := 0xCB6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1061
  obtain ⟨n1062, v1062, d1062, hv1062, u1062⟩ := u1061.aluG hc smm_at_cb6 (off' := 0xCB8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1062
  obtain ⟨n1063, v1063, d1063, hv1063, u1063⟩ := u1062.aluImmG hc smm_at_cb8 (off' := 0xCBC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1063
  obtain ⟨n1064, v1064, d1064, hv1064, u1064⟩ := u1063.aluImmG hc smm_at_cbc (off' := 0xCC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1064
  obtain ⟨n1065, d1065, u1065⟩ := u1064.lwE hc smm_at_cc0 (off' := 0xCC2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 200) (by decide)) (v := v507)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slC8])
  obtain ⟨n1066, v1066, d1066, hv1066, u1066⟩ := u1065.aluImmG hc smm_at_cc2 (off' := 0xCC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1066
  obtain ⟨n1067, v1067, d1067, hv1067, u1067⟩ := u1066.aluG hc smm_at_cc4 (off' := 0xCC8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1067
  obtain ⟨n1068, v1068, d1068, hv1068, u1068⟩ := u1067.aluG hc smm_at_cc8 (off' := 0xCCA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1068
  obtain ⟨n1069, v1069, d1069, hv1069, u1069⟩ := u1068.aluImmG hc smm_at_cca (off' := 0xCCE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1069
  obtain ⟨n1070, v1070, d1070, hv1070, u1070⟩ := u1069.aluG hc smm_at_cce (off' := 0xCD2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1070
  obtain ⟨n1071, v1071, d1071, hv1071, u1071⟩ := u1070.aluG hc smm_at_cd2 (off' := 0xCD4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1071
  obtain ⟨n1072, v1072, d1072, hv1072, u1072⟩ := u1071.aluG hc smm_at_cd4 (off' := 0xCD6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1072
  obtain ⟨n1073, v1073, d1073, hv1073, u1073⟩ := u1072.aluImmG hc smm_at_cd6 (off' := 0xCDA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1073
  obtain ⟨n1074, v1074, d1074, hv1074, u1074⟩ := u1073.aluG hc smm_at_cda (off' := 0xCDE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1074
  obtain ⟨n1075, v1075, d1075, hv1075, u1075⟩ := u1074.aluG hc smm_at_cde (off' := 0xCE0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1075
  obtain ⟨n1076, v1076, d1076, hv1076, u1076⟩ := u1075.aluG hc smm_at_ce0 (off' := 0xCE4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1076
  obtain ⟨n1077, v1077, d1077, hv1077, u1077⟩ := u1076.aluG hc smm_at_ce4 (off' := 0xCE6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1077
  obtain ⟨n1078, v1078, d1078, hv1078, u1078⟩ := u1077.aluImmG hc smm_at_ce6 (off' := 0xCEA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1078
  obtain ⟨n1079, v1079, d1079, hv1079, u1079⟩ := u1078.aluImmG hc smm_at_cea (off' := 0xCEE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1079
  have qo1 : reg n1079 ra = v314 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n1079 sp = F := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n1079 (3 : Fin 32) = G3 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n1079 (4 : Fin 32) = G4 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n1079 (5 : Fin 32) = v747 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n1079 (6 : Fin 32) = v992 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n1079 (7 : Fin 32) = v1037 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n1079 (8 : Fin 32) = v1021 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n1079 (9 : Fin 32) = v1070 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n1079 a0 = v1062 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n1079 a1 = v1077 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n1079 a2 = v739 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n1079 a3 = v1078 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n1079 a4 = v1079 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n1079 a5 = v1067 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n1079 a6 = v386 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n1079 a7 = v278 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n1079 (18 : Fin 32) = v662 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n1079 (19 : Fin 32) = v827 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n1079 (20 : Fin 32) = v946 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n1079 (21 : Fin 32) = v470 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n1079 (22 : Fin 32) = v384 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n1079 (23 : Fin 32) = v355 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n1079 (24 : Fin 32) = v274 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n1079 (25 : Fin 32) = v280 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n1079 (26 : Fin 32) = v523 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n1079 (27 : Fin 32) = v700 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n1079 (28 : Fin 32) = v1059 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n1079 (29 : Fin 32) = v1074 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n1079 (30 : Fin 32) = v322 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n1079 (31 : Fin 32) = v843 := by rw [u1079.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soF8 : memLoad32 Mi (F + 0xF8) = outp := by
    rw [slF8]
  have so110 : memLoad32 Mi (F + 0x110) = v645 := by
    rw [sl110]
  have so11C : memLoad32 Mi (F + 0x11C) = v733 := by
    rw [sl11C]
  have so130 : memLoad32 Mi (F + 0x130) = v226 := by
    rw [sl130]
  have so15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [sl15C]
  have so160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [sl160]
  have so164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [sl164]
  have so168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [sl168]
  have so16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [sl16C]
  have so170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [sl170]
  have so174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [sl174]
  have so178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [sl178]
  have so17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [sl17C]
  have so180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [sl180]
  have so184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [sl184]
  have so188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [sl188]
  have so18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [sl18C]
  exact ⟨n1079, Mi, v1040, v1041, v1042, v1044, v1045, v1046, v1048, v1049, v1050, v1051, v1052, v1053, v1054, v1055, v1056, v1057, v1058, v1059, v1060, v1061, v1062, v1063, v1064, v1066, v1067, v1068, v1069, v1070, v1071, v1072, v1073, v1074, v1075, v1076, v1077, v1078, v1079, (.cons d1040 (.cons d1041 (.cons d1042 (.cons d1043 (.cons d1044 (.cons d1045 (.cons d1046 (.cons d1047 (.cons d1048 (.cons d1049 (.cons d1050 (.cons d1051 (.cons d1052 (.cons d1053 (.cons d1054 (.cons d1055 (.cons d1056 (.cons d1057 (.cons d1058 (.cons d1059 (.cons d1060 (.cons d1061 (.cons d1062 (.cons d1063 (.cons d1064 (.cons d1065 (.cons d1066 (.cons d1067 (.cons d1068 (.cons d1069 (.cons d1070 (.cons d1071 (.cons d1072 (.cons d1073 (.cons d1074 (.cons d1075 (.cons d1076 (.cons d1077 (.cons d1078 (.single d1079)))))))))))))))))))))))))))))))))))))))), u1079.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soF8, so110, so11C, so130, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv1040, hv1041, hv1042, hv1044, hv1045, hv1046, hv1048, hv1049, hv1050, hv1051, hv1052, hv1053, hv1054, hv1055, hv1056, hv1057, hv1058, hv1059, hv1060, hv1061, hv1062, hv1063, hv1064, hv1066, hv1067, hv1068, hv1069, hv1070, hv1071, hv1072, hv1073, hv1074, hv1075, hv1076, hv1077, hv1078, hv1079⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g33 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v226 v274 v278 v280 v314 v322 v355 v384 v386 v470 v523 v645 v662 v700 v733 v739 v747 v827 v843 v946 v992 v1021 v1037 v1059 v1062 v1067 v1070 v1074 v1077 v1078 v1079 : Word}
    (s : St Mi B n 0xCEE (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v314)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v747)
    (q6 : reg n (6 : Fin 32) = v992)
    (q7 : reg n (7 : Fin 32) = v1037)
    (q8 : reg n (8 : Fin 32) = v1021)
    (q9 : reg n (9 : Fin 32) = v1070)
    (q10 : reg n a0 = v1062)
    (q11 : reg n a1 = v1077)
    (q12 : reg n a2 = v739)
    (q13 : reg n a3 = v1078)
    (q14 : reg n a4 = v1079)
    (q15 : reg n a5 = v1067)
    (q16 : reg n a6 = v386)
    (q17 : reg n a7 = v278)
    (q18 : reg n (18 : Fin 32) = v662)
    (q19 : reg n (19 : Fin 32) = v827)
    (q20 : reg n (20 : Fin 32) = v946)
    (q21 : reg n (21 : Fin 32) = v470)
    (q22 : reg n (22 : Fin 32) = v384)
    (q23 : reg n (23 : Fin 32) = v355)
    (q24 : reg n (24 : Fin 32) = v274)
    (q25 : reg n (25 : Fin 32) = v280)
    (q26 : reg n (26 : Fin 32) = v523)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v1059)
    (q29 : reg n (29 : Fin 32) = v1074)
    (q30 : reg n (30 : Fin 32) = v322)
    (q31 : reg n (31 : Fin 32) = v843)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl110 : memLoad32 Mi (F + 0x110) = v645)
    (sl11C : memLoad32 Mi (F + 0x11C) = v733)
    (sl130 : memLoad32 Mi (F + 0x130) = v226)
    (sl15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C))
    (sl160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160))
    (sl164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164))
    (sl168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168))
    (sl16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C))
    (sl170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170))
    (sl174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174))
    (sl178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178))
    (sl17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C))
    (sl180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180))
    (sl184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184))
    (sl188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188))
    (sl18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1081 v1082 v1083 v1084 v1085 v1086 v1087 v1088 v1089 v1090 v1091 v1092 v1093 v1094 v1096 v1097 v1098 v1099 v1100 v1101 v1102 v1103 v1104 v1105 v1106 v1107 v1108 v1109 v1110 v1111 v1112 v1113 v1114 v1115 v1116 v1117 v1118 v1119 : Word),
      Steps n n' ∧
      St M' B n' 0xD66 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v314 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v747 ∧
      reg n' (6 : Fin 32) = v992 ∧
      reg n' (7 : Fin 32) = v1037 ∧
      reg n' (8 : Fin 32) = v1100 ∧
      reg n' (9 : Fin 32) = v1104 ∧
      reg n' a0 = v1118 ∧
      reg n' a1 = v1119 ∧
      reg n' a2 = v1116 ∧
      reg n' a3 = v1108 ∧
      reg n' a4 = v1112 ∧
      reg n' a5 = v1111 ∧
      reg n' a6 = v386 ∧
      reg n' a7 = v1096 ∧
      reg n' (18 : Fin 32) = v1089 ∧
      reg n' (19 : Fin 32) = v827 ∧
      reg n' (20 : Fin 32) = v946 ∧
      reg n' (21 : Fin 32) = v470 ∧
      reg n' (22 : Fin 32) = v384 ∧
      reg n' (23 : Fin 32) = v355 ∧
      reg n' (24 : Fin 32) = v274 ∧
      reg n' (25 : Fin 32) = v280 ∧
      reg n' (26 : Fin 32) = v523 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v1059 ∧
      reg n' (29 : Fin 32) = v1074 ∧
      reg n' (30 : Fin 32) = v1110 ∧
      reg n' (31 : Fin 32) = v843 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x130) = v226 ∧
      memLoad32 M' (F + 0x15C) = memLoad32 M0 (F + 0x15C) ∧
      memLoad32 M' (F + 0x160) = memLoad32 M0 (F + 0x160) ∧
      memLoad32 M' (F + 0x164) = memLoad32 M0 (F + 0x164) ∧
      memLoad32 M' (F + 0x168) = memLoad32 M0 (F + 0x168) ∧
      memLoad32 M' (F + 0x16C) = memLoad32 M0 (F + 0x16C) ∧
      memLoad32 M' (F + 0x170) = memLoad32 M0 (F + 0x170) ∧
      memLoad32 M' (F + 0x174) = memLoad32 M0 (F + 0x174) ∧
      memLoad32 M' (F + 0x178) = memLoad32 M0 (F + 0x178) ∧
      memLoad32 M' (F + 0x17C) = memLoad32 M0 (F + 0x17C) ∧
      memLoad32 M' (F + 0x180) = memLoad32 M0 (F + 0x180) ∧
      memLoad32 M' (F + 0x184) = memLoad32 M0 (F + 0x184) ∧
      memLoad32 M' (F + 0x188) = memLoad32 M0 (F + 0x188) ∧
      memLoad32 M' (F + 0x18C) = memLoad32 M0 (F + 0x18C) ∧
      aluEval .sll v645 0x14 = v1081 ∧
      aluEval .add v1081 v274 = v1082 ∧
      aluEval .add v1079 v280 = v1083 ∧
      aluEval .srl v1074 0x1D = v1084 ∧
      aluEval .sltu v1082 v1081 = v1085 ∧
      aluEval .or v1084 v1078 = v1086 ∧
      aluEval .add v1083 v1085 = v1087 ∧
      aluEval .srl v1077 0x1D = v1088 ∧
      aluEval .add v1082 v1086 = v1089 ∧
      aluEval .add v1088 v1087 = v1090 ∧
      aluEval .sltu v1089 v1082 = v1091 ∧
      aluEval .add v1090 v1091 = v1092 ∧
      aluEval .sll v1092 0x3 = v1093 ∧
      aluEval .srl v747 0xC = v1094 ∧
      aluEval .sll v733 0x14 = v1096 ∧
      aluEval .add v1096 v314 = v1097 ∧
      aluEval .add v1094 v322 = v1098 ∧
      aluEval .srl v1089 0x1D = v1099 ∧
      aluEval .sltu v1097 v1096 = v1100 ∧
      aluEval .or v1099 v1093 = v1101 ∧
      aluEval .add v1098 v1100 = v1102 ∧
      aluEval .srl v1092 0x1D = v1103 ∧
      aluEval .add v1097 v1101 = v1104 ∧
      aluEval .add v1103 v1102 = v1105 ∧
      aluEval .sltu v1104 v1097 = v1106 ∧
      aluEval .add v1105 v1106 = v1107 ∧
      aluEval .sll v1107 0x3 = v1108 ∧
      aluEval .srl v843 0xC = v1109 ∧
      aluEval .sll v827 0x14 = v1110 ∧
      aluEval .add v1110 v386 = v1111 ∧
      aluEval .add v1109 v384 = v1112 ∧
      aluEval .srl v1104 0x1D = v1113 ∧
      aluEval .sltu v1111 v1110 = v1114 ∧
      aluEval .or v1113 v1108 = v1115 ∧
      aluEval .add v1114 v1112 = v1116 ∧
      aluEval .srl v1107 0x1D = v1117 ∧
      aluEval .add v1115 v1111 = v1118 ∧
      aluEval .add v1117 v1116 = v1119 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n1080, d1080, u1080⟩ := s.lwE hc smm_at_cee (off' := 0xCF2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 272) (by decide)) (v := v645)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl110])
  obtain ⟨n1081, v1081, d1081, hv1081, u1081⟩ := u1080.aluImmG hc smm_at_cf2 (off' := 0xCF4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1081
  obtain ⟨n1082, v1082, d1082, hv1082, u1082⟩ := u1081.aluG hc smm_at_cf4 (off' := 0xCF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1082
  obtain ⟨n1083, v1083, d1083, hv1083, u1083⟩ := u1082.aluG hc smm_at_cf8 (off' := 0xCFA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1083
  obtain ⟨n1084, v1084, d1084, hv1084, u1084⟩ := u1083.aluImmG hc smm_at_cfa (off' := 0xCFE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1084
  obtain ⟨n1085, v1085, d1085, hv1085, u1085⟩ := u1084.aluG hc smm_at_cfe (off' := 0xD02) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1085
  obtain ⟨n1086, v1086, d1086, hv1086, u1086⟩ := u1085.aluG hc smm_at_d02 (off' := 0xD04) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1086
  obtain ⟨n1087, v1087, d1087, hv1087, u1087⟩ := u1086.aluG hc smm_at_d04 (off' := 0xD06) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1087
  obtain ⟨n1088, v1088, d1088, hv1088, u1088⟩ := u1087.aluImmG hc smm_at_d06 (off' := 0xD08) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1088
  obtain ⟨n1089, v1089, d1089, hv1089, u1089⟩ := u1088.aluG hc smm_at_d08 (off' := 0xD0C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1089
  obtain ⟨n1090, v1090, d1090, hv1090, u1090⟩ := u1089.aluG hc smm_at_d0c (off' := 0xD0E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1090
  obtain ⟨n1091, v1091, d1091, hv1091, u1091⟩ := u1090.aluG hc smm_at_d0e (off' := 0xD12) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1091
  obtain ⟨n1092, v1092, d1092, hv1092, u1092⟩ := u1091.aluG hc smm_at_d12 (off' := 0xD14) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1092
  obtain ⟨n1093, v1093, d1093, hv1093, u1093⟩ := u1092.aluImmG hc smm_at_d14 (off' := 0xD18) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1093
  obtain ⟨n1094, v1094, d1094, hv1094, u1094⟩ := u1093.aluImmG hc smm_at_d18 (off' := 0xD1C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1094
  obtain ⟨n1095, d1095, u1095⟩ := u1094.lwE hc smm_at_d1c (off' := 0xD20) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 284) (by decide)) (v := v733)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl11C])
  obtain ⟨n1096, v1096, d1096, hv1096, u1096⟩ := u1095.aluImmG hc smm_at_d20 (off' := 0xD22) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1096
  obtain ⟨n1097, v1097, d1097, hv1097, u1097⟩ := u1096.aluG hc smm_at_d22 (off' := 0xD26) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1097
  obtain ⟨n1098, v1098, d1098, hv1098, u1098⟩ := u1097.aluG hc smm_at_d26 (off' := 0xD28) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1098
  obtain ⟨n1099, v1099, d1099, hv1099, u1099⟩ := u1098.aluImmG hc smm_at_d28 (off' := 0xD2C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1099
  obtain ⟨n1100, v1100, d1100, hv1100, u1100⟩ := u1099.aluG hc smm_at_d2c (off' := 0xD30) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1100
  obtain ⟨n1101, v1101, d1101, hv1101, u1101⟩ := u1100.aluG hc smm_at_d30 (off' := 0xD32) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1101
  obtain ⟨n1102, v1102, d1102, hv1102, u1102⟩ := u1101.aluG hc smm_at_d32 (off' := 0xD34) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1102
  obtain ⟨n1103, v1103, d1103, hv1103, u1103⟩ := u1102.aluImmG hc smm_at_d34 (off' := 0xD36) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1103
  obtain ⟨n1104, v1104, d1104, hv1104, u1104⟩ := u1103.aluG hc smm_at_d36 (off' := 0xD3A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1104
  obtain ⟨n1105, v1105, d1105, hv1105, u1105⟩ := u1104.aluG hc smm_at_d3a (off' := 0xD3C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1105
  obtain ⟨n1106, v1106, d1106, hv1106, u1106⟩ := u1105.aluG hc smm_at_d3c (off' := 0xD40) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1106
  obtain ⟨n1107, v1107, d1107, hv1107, u1107⟩ := u1106.aluG hc smm_at_d40 (off' := 0xD42) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1107
  obtain ⟨n1108, v1108, d1108, hv1108, u1108⟩ := u1107.aluImmG hc smm_at_d42 (off' := 0xD46) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1108
  obtain ⟨n1109, v1109, d1109, hv1109, u1109⟩ := u1108.aluImmG hc smm_at_d46 (off' := 0xD4A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1109
  obtain ⟨n1110, v1110, d1110, hv1110, u1110⟩ := u1109.aluImmG hc smm_at_d4a (off' := 0xD4E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1110
  obtain ⟨n1111, v1111, d1111, hv1111, u1111⟩ := u1110.aluG hc smm_at_d4e (off' := 0xD52) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1111
  obtain ⟨n1112, v1112, d1112, hv1112, u1112⟩ := u1111.aluG hc smm_at_d52 (off' := 0xD54) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1112
  obtain ⟨n1113, v1113, d1113, hv1113, u1113⟩ := u1112.aluImmG hc smm_at_d54 (off' := 0xD58) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1113
  obtain ⟨n1114, v1114, d1114, hv1114, u1114⟩ := u1113.aluG hc smm_at_d58 (off' := 0xD5C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1114
  obtain ⟨n1115, v1115, d1115, hv1115, u1115⟩ := u1114.aluG hc smm_at_d5c (off' := 0xD5E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1115
  obtain ⟨n1116, v1116, d1116, hv1116, u1116⟩ := u1115.aluG hc smm_at_d5e (off' := 0xD60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1116
  obtain ⟨n1117, v1117, d1117, hv1117, u1117⟩ := u1116.aluImmG hc smm_at_d60 (off' := 0xD62) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1117
  obtain ⟨n1118, v1118, d1118, hv1118, u1118⟩ := u1117.aluG hc smm_at_d62 (off' := 0xD64) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1118
  obtain ⟨n1119, v1119, d1119, hv1119, u1119⟩ := u1118.aluG hc smm_at_d64 (off' := 0xD66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1119
  have qo1 : reg n1119 ra = v314 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n1119 sp = F := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n1119 (3 : Fin 32) = G3 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n1119 (4 : Fin 32) = G4 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n1119 (5 : Fin 32) = v747 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n1119 (6 : Fin 32) = v992 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n1119 (7 : Fin 32) = v1037 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n1119 (8 : Fin 32) = v1100 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n1119 (9 : Fin 32) = v1104 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n1119 a0 = v1118 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n1119 a1 = v1119 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n1119 a2 = v1116 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n1119 a3 = v1108 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n1119 a4 = v1112 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n1119 a5 = v1111 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n1119 a6 = v386 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n1119 a7 = v1096 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n1119 (18 : Fin 32) = v1089 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n1119 (19 : Fin 32) = v827 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n1119 (20 : Fin 32) = v946 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n1119 (21 : Fin 32) = v470 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n1119 (22 : Fin 32) = v384 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n1119 (23 : Fin 32) = v355 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n1119 (24 : Fin 32) = v274 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n1119 (25 : Fin 32) = v280 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n1119 (26 : Fin 32) = v523 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n1119 (27 : Fin 32) = v700 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n1119 (28 : Fin 32) = v1059 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n1119 (29 : Fin 32) = v1074 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n1119 (30 : Fin 32) = v1110 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n1119 (31 : Fin 32) = v843 := by rw [u1119.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soF8 : memLoad32 Mi (F + 0xF8) = outp := by
    rw [slF8]
  have so130 : memLoad32 Mi (F + 0x130) = v226 := by
    rw [sl130]
  have so15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [sl15C]
  have so160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [sl160]
  have so164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [sl164]
  have so168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [sl168]
  have so16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [sl16C]
  have so170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [sl170]
  have so174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [sl174]
  have so178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [sl178]
  have so17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [sl17C]
  have so180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [sl180]
  have so184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [sl184]
  have so188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [sl188]
  have so18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [sl18C]
  exact ⟨n1119, Mi, v1081, v1082, v1083, v1084, v1085, v1086, v1087, v1088, v1089, v1090, v1091, v1092, v1093, v1094, v1096, v1097, v1098, v1099, v1100, v1101, v1102, v1103, v1104, v1105, v1106, v1107, v1108, v1109, v1110, v1111, v1112, v1113, v1114, v1115, v1116, v1117, v1118, v1119, (.cons d1080 (.cons d1081 (.cons d1082 (.cons d1083 (.cons d1084 (.cons d1085 (.cons d1086 (.cons d1087 (.cons d1088 (.cons d1089 (.cons d1090 (.cons d1091 (.cons d1092 (.cons d1093 (.cons d1094 (.cons d1095 (.cons d1096 (.cons d1097 (.cons d1098 (.cons d1099 (.cons d1100 (.cons d1101 (.cons d1102 (.cons d1103 (.cons d1104 (.cons d1105 (.cons d1106 (.cons d1107 (.cons d1108 (.cons d1109 (.cons d1110 (.cons d1111 (.cons d1112 (.cons d1113 (.cons d1114 (.cons d1115 (.cons d1116 (.cons d1117 (.cons d1118 (.single d1119)))))))))))))))))))))))))))))))))))))))), u1119.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soF8, so130, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv1081, hv1082, hv1083, hv1084, hv1085, hv1086, hv1087, hv1088, hv1089, hv1090, hv1091, hv1092, hv1093, hv1094, hv1096, hv1097, hv1098, hv1099, hv1100, hv1101, hv1102, hv1103, hv1104, hv1105, hv1106, hv1107, hv1108, hv1109, hv1110, hv1111, hv1112, hv1113, hv1114, hv1115, hv1116, hv1117, hv1118, hv1119⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g34 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v226 v274 v280 v314 v355 v384 v386 v470 v523 v700 v747 v827 v843 v946 v992 v1037 v1059 v1074 v1089 v1096 v1100 v1104 v1108 v1110 v1111 v1112 v1116 v1118 v1119 : Word}
    (s : St Mi B n 0xD66 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v314)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v747)
    (q6 : reg n (6 : Fin 32) = v992)
    (q7 : reg n (7 : Fin 32) = v1037)
    (q8 : reg n (8 : Fin 32) = v1100)
    (q9 : reg n (9 : Fin 32) = v1104)
    (q10 : reg n a0 = v1118)
    (q11 : reg n a1 = v1119)
    (q12 : reg n a2 = v1116)
    (q13 : reg n a3 = v1108)
    (q14 : reg n a4 = v1112)
    (q15 : reg n a5 = v1111)
    (q16 : reg n a6 = v386)
    (q17 : reg n a7 = v1096)
    (q18 : reg n (18 : Fin 32) = v1089)
    (q19 : reg n (19 : Fin 32) = v827)
    (q20 : reg n (20 : Fin 32) = v946)
    (q21 : reg n (21 : Fin 32) = v470)
    (q22 : reg n (22 : Fin 32) = v384)
    (q23 : reg n (23 : Fin 32) = v355)
    (q24 : reg n (24 : Fin 32) = v274)
    (q25 : reg n (25 : Fin 32) = v280)
    (q26 : reg n (26 : Fin 32) = v523)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v1059)
    (q29 : reg n (29 : Fin 32) = v1074)
    (q30 : reg n (30 : Fin 32) = v1110)
    (q31 : reg n (31 : Fin 32) = v843)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl130 : memLoad32 Mi (F + 0x130) = v226)
    (sl15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C))
    (sl160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160))
    (sl164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164))
    (sl168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168))
    (sl16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C))
    (sl170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170))
    (sl174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174))
    (sl178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178))
    (sl17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C))
    (sl180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180))
    (sl184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184))
    (sl188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188))
    (sl18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v1120 v1121 v1123 v1124 v1125 v1126 v1127 v1128 v1129 v1130 v1131 v1132 v1133 : Word),
      Steps n n' ∧
      St M' B n' 0xD94 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v314 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v1127 ∧
      reg n' (6 : Fin 32) = v992 ∧
      reg n' (7 : Fin 32) = v1037 ∧
      reg n' (8 : Fin 32) = v226 ∧
      reg n' (9 : Fin 32) = v1129 ∧
      reg n' a0 = v1133 ∧
      reg n' a1 = v1131 ∧
      reg n' a2 = v1123 ∧
      reg n' a3 = v1124 ∧
      reg n' a4 = v1125 ∧
      reg n' a5 = v1126 ∧
      reg n' a6 = v1128 ∧
      reg n' a7 = v1130 ∧
      reg n' (18 : Fin 32) = v1089 ∧
      reg n' (19 : Fin 32) = v827 ∧
      reg n' (20 : Fin 32) = v946 ∧
      reg n' (21 : Fin 32) = v470 ∧
      reg n' (22 : Fin 32) = v384 ∧
      reg n' (23 : Fin 32) = v355 ∧
      reg n' (24 : Fin 32) = v274 ∧
      reg n' (25 : Fin 32) = v280 ∧
      reg n' (26 : Fin 32) = v523 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v1059 ∧
      reg n' (29 : Fin 32) = v1074 ∧
      reg n' (30 : Fin 32) = v1110 ∧
      reg n' (31 : Fin 32) = v843 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x15C) = memLoad32 M0 (F + 0x15C) ∧
      memLoad32 M' (F + 0x160) = memLoad32 M0 (F + 0x160) ∧
      memLoad32 M' (F + 0x164) = memLoad32 M0 (F + 0x164) ∧
      memLoad32 M' (F + 0x168) = memLoad32 M0 (F + 0x168) ∧
      memLoad32 M' (F + 0x16C) = memLoad32 M0 (F + 0x16C) ∧
      memLoad32 M' (F + 0x170) = memLoad32 M0 (F + 0x170) ∧
      memLoad32 M' (F + 0x174) = memLoad32 M0 (F + 0x174) ∧
      memLoad32 M' (F + 0x178) = memLoad32 M0 (F + 0x178) ∧
      memLoad32 M' (F + 0x17C) = memLoad32 M0 (F + 0x17C) ∧
      memLoad32 M' (F + 0x180) = memLoad32 M0 (F + 0x180) ∧
      memLoad32 M' (F + 0x184) = memLoad32 M0 (F + 0x184) ∧
      memLoad32 M' (F + 0x188) = memLoad32 M0 (F + 0x188) ∧
      memLoad32 M' (F + 0x18C) = memLoad32 M0 (F + 0x18C) ∧
      aluEval .sltu v1118 v1111 = v1120 ∧
      aluEval .add v1119 v1120 = v1121 ∧
      aluEval .and v946 v226 = v1123 ∧
      aluEval .and v992 v226 = v1124 ∧
      aluEval .and v1037 v226 = v1125 ∧
      aluEval .and v1059 v226 = v1126 ∧
      aluEval .and v1074 v226 = v1127 ∧
      aluEval .and v1089 v226 = v1128 ∧
      aluEval .and v1104 v226 = v1129 ∧
      aluEval .and v1118 v226 = v1130 ∧
      aluEval .sll v1121 0x3 = v1131 ∧
      aluEval .srl v1118 0x1D = v1132 ∧
      aluEval .or v1132 v1131 = v1133 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n1120, v1120, d1120, hv1120, u1120⟩ := s.aluG hc smm_at_d66 (off' := 0xD6A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1120
  obtain ⟨n1121, v1121, d1121, hv1121, u1121⟩ := u1120.aluG hc smm_at_d6a (off' := 0xD6C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1121
  obtain ⟨n1122, d1122, u1122⟩ := u1121.lwE hc smm_at_d6c (off' := 0xD70) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 304) (by decide)) (v := v226)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl130])
  obtain ⟨n1123, v1123, d1123, hv1123, u1123⟩ := u1122.aluG hc smm_at_d70 (off' := 0xD74) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1123
  obtain ⟨n1124, v1124, d1124, hv1124, u1124⟩ := u1123.aluG hc smm_at_d74 (off' := 0xD78) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1124
  obtain ⟨n1125, v1125, d1125, hv1125, u1125⟩ := u1124.aluG hc smm_at_d78 (off' := 0xD7C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1125
  obtain ⟨n1126, v1126, d1126, hv1126, u1126⟩ := u1125.aluG hc smm_at_d7c (off' := 0xD80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1126
  obtain ⟨n1127, v1127, d1127, hv1127, u1127⟩ := u1126.aluG hc smm_at_d80 (off' := 0xD84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1127
  obtain ⟨n1128, v1128, d1128, hv1128, u1128⟩ := u1127.aluG hc smm_at_d84 (off' := 0xD88) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1128
  obtain ⟨n1129, v1129, d1129, hv1129, u1129⟩ := u1128.aluG hc smm_at_d88 (off' := 0xD8A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1129
  obtain ⟨n1130, v1130, d1130, hv1130, u1130⟩ := u1129.aluG hc smm_at_d8a (off' := 0xD8E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1130
  obtain ⟨n1131, v1131, d1131, hv1131, u1131⟩ := u1130.aluImmG hc smm_at_d8e (off' := 0xD90) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1131
  obtain ⟨n1132, v1132, d1132, hv1132, u1132⟩ := u1131.aluImmG hc smm_at_d90 (off' := 0xD92) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1132
  obtain ⟨n1133, v1133, d1133, hv1133, u1133⟩ := u1132.aluG hc smm_at_d92 (off' := 0xD94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv1133
  have qo1 : reg n1133 ra = v314 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n1133 sp = F := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n1133 (3 : Fin 32) = G3 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n1133 (4 : Fin 32) = G4 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n1133 (5 : Fin 32) = v1127 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n1133 (6 : Fin 32) = v992 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n1133 (7 : Fin 32) = v1037 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n1133 (8 : Fin 32) = v226 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n1133 (9 : Fin 32) = v1129 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n1133 a0 = v1133 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n1133 a1 = v1131 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n1133 a2 = v1123 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n1133 a3 = v1124 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n1133 a4 = v1125 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n1133 a5 = v1126 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n1133 a6 = v1128 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n1133 a7 = v1130 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n1133 (18 : Fin 32) = v1089 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n1133 (19 : Fin 32) = v827 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n1133 (20 : Fin 32) = v946 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n1133 (21 : Fin 32) = v470 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n1133 (22 : Fin 32) = v384 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n1133 (23 : Fin 32) = v355 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n1133 (24 : Fin 32) = v274 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n1133 (25 : Fin 32) = v280 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n1133 (26 : Fin 32) = v523 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n1133 (27 : Fin 32) = v700 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n1133 (28 : Fin 32) = v1059 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n1133 (29 : Fin 32) = v1074 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n1133 (30 : Fin 32) = v1110 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n1133 (31 : Fin 32) = v843 := by rw [u1133.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soF8 : memLoad32 Mi (F + 0xF8) = outp := by
    rw [slF8]
  have so15C : memLoad32 Mi (F + 0x15C) = memLoad32 M0 (F + 0x15C) := by
    rw [sl15C]
  have so160 : memLoad32 Mi (F + 0x160) = memLoad32 M0 (F + 0x160) := by
    rw [sl160]
  have so164 : memLoad32 Mi (F + 0x164) = memLoad32 M0 (F + 0x164) := by
    rw [sl164]
  have so168 : memLoad32 Mi (F + 0x168) = memLoad32 M0 (F + 0x168) := by
    rw [sl168]
  have so16C : memLoad32 Mi (F + 0x16C) = memLoad32 M0 (F + 0x16C) := by
    rw [sl16C]
  have so170 : memLoad32 Mi (F + 0x170) = memLoad32 M0 (F + 0x170) := by
    rw [sl170]
  have so174 : memLoad32 Mi (F + 0x174) = memLoad32 M0 (F + 0x174) := by
    rw [sl174]
  have so178 : memLoad32 Mi (F + 0x178) = memLoad32 M0 (F + 0x178) := by
    rw [sl178]
  have so17C : memLoad32 Mi (F + 0x17C) = memLoad32 M0 (F + 0x17C) := by
    rw [sl17C]
  have so180 : memLoad32 Mi (F + 0x180) = memLoad32 M0 (F + 0x180) := by
    rw [sl180]
  have so184 : memLoad32 Mi (F + 0x184) = memLoad32 M0 (F + 0x184) := by
    rw [sl184]
  have so188 : memLoad32 Mi (F + 0x188) = memLoad32 M0 (F + 0x188) := by
    rw [sl188]
  have so18C : memLoad32 Mi (F + 0x18C) = memLoad32 M0 (F + 0x18C) := by
    rw [sl18C]
  exact ⟨n1133, Mi, v1120, v1121, v1123, v1124, v1125, v1126, v1127, v1128, v1129, v1130, v1131, v1132, v1133, (.cons d1120 (.cons d1121 (.cons d1122 (.cons d1123 (.cons d1124 (.cons d1125 (.cons d1126 (.cons d1127 (.cons d1128 (.cons d1129 (.cons d1130 (.cons d1131 (.cons d1132 (.single d1133)))))))))))))), u1133.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soF8, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv1120, hv1121, hv1123, hv1124, hv1125, hv1126, hv1127, hv1128, hv1129, hv1130, hv1131, hv1132, hv1133⟩

end C3.RV32
