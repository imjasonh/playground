import C3BootProofs.Proofs.ScalarMontFacts

/-! # `montgomery_mul`'s body, segments 27 to 30

Each theorem steps 40 instructions. `scripts/gen-scalar-mont.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g27 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v122 v139 v141 v147 v169 v186 v212 v226 v228 v234 v239 v266 v272 v274 v278 v280 v285 v293 v314 v316 v322 v341 v355 v382 v384 v386 v401 v455 v470 v507 v523 v578 v589 v591 v593 v595 v601 v604 v608 v610 v612 v616 v618 v620 v622 v624 v636 v638 v641 v645 v647 v651 v653 v662 v663 v700 v733 v739 v747 v802 v807 v817 v823 v825 v827 v830 v831 v834 v837 v838 v839 : Word}
    (s : St Mi B n 0xA44 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v228)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v747)
    (q6 : reg n (6 : Fin 32) = v823)
    (q7 : reg n (7 : Fin 32) = v825)
    (q8 : reg n (8 : Fin 32) = v807)
    (q9 : reg n (9 : Fin 32) = v839)
    (q10 : reg n a0 = v831)
    (q11 : reg n a1 = v578)
    (q12 : reg n a2 = v834)
    (q13 : reg n a3 = v837)
    (q14 : reg n a4 = v817)
    (q15 : reg n a5 = v838)
    (q16 : reg n a6 = v802)
    (q17 : reg n a7 = v278)
    (q18 : reg n (18 : Fin 32) = v662)
    (q19 : reg n (19 : Fin 32) = v827)
    (q20 : reg n (20 : Fin 32) = v239)
    (q21 : reg n (21 : Fin 32) = v470)
    (q22 : reg n (22 : Fin 32) = v293)
    (q23 : reg n (23 : Fin 32) = v355)
    (q24 : reg n (24 : Fin 32) = v226)
    (q25 : reg n (25 : Fin 32) = v663)
    (q26 : reg n (26 : Fin 32) = v523)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v830)
    (q29 : reg n (29 : Fin 32) = v272)
    (q30 : reg n (30 : Fin 32) = v234)
    (q31 : reg n (31 : Fin 32) = v212)
    (sl5C : memLoad32 Mi (F + 0x5C) = v616)
    (sl64 : memLoad32 Mi (F + 0x64) = v612)
    (sl68 : memLoad32 Mi (F + 0x68) = v604)
    (sl6C : memLoad32 Mi (F + 0x6C) = v591)
    (sl70 : memLoad32 Mi (F + 0x70) = v589)
    (sl74 : memLoad32 Mi (F + 0x74) = v601)
    (sl78 : memLoad32 Mi (F + 0x78) = v638)
    (sl7C : memLoad32 Mi (F + 0x7C) = v636)
    (sl84 : memLoad32 Mi (F + 0x84) = v608)
    (sl88 : memLoad32 Mi (F + 0x88) = v610)
    (sl8C : memLoad32 Mi (F + 0x8C) = v620)
    (sl90 : memLoad32 Mi (F + 0x90) = v618)
    (sl94 : memLoad32 Mi (F + 0x94) = v595)
    (sl98 : memLoad32 Mi (F + 0x98) = v593)
    (sl9C : memLoad32 Mi (F + 0x9C) = v651)
    (slA0 : memLoad32 Mi (F + 0xA0) = v285)
    (slA4 : memLoad32 Mi (F + 0xA4) = v647)
    (slA8 : memLoad32 Mi (F + 0xA8) = v624)
    (slAC : memLoad32 Mi (F + 0xAC) = v341)
    (slB8 : memLoad32 Mi (F + 0xB8) = v641)
    (slC0 : memLoad32 Mi (F + 0xC0) = v653)
    (slC8 : memLoad32 Mi (F + 0xC8) = v507)
    (slD0 : memLoad32 Mi (F + 0xD0) = v266)
    (slD4 : memLoad32 Mi (F + 0xD4) = v455)
    (slD8 : memLoad32 Mi (F + 0xD8) = v280)
    (slDC : memLoad32 Mi (F + 0xDC) = v274)
    (slE0 : memLoad32 Mi (F + 0xE0) = v386)
    (slE4 : memLoad32 Mi (F + 0xE4) = v322)
    (slE8 : memLoad32 Mi (F + 0xE8) = v384)
    (slEC : memLoad32 Mi (F + 0xEC) = v382)
    (slF0 : memLoad32 Mi (F + 0xF0) = v316)
    (slF4 : memLoad32 Mi (F + 0xF4) = v314)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v401)
    (sl104 : memLoad32 Mi (F + 0x104) = v122)
    (sl10C : memLoad32 Mi (F + 0x10C) = v622)
    (sl110 : memLoad32 Mi (F + 0x110) = v645)
    (sl118 : memLoad32 Mi (F + 0x118) = v739)
    (sl11C : memLoad32 Mi (F + 0x11C) = v733)
    (sl120 : memLoad32 Mi (F + 0x120) = v139)
    (sl124 : memLoad32 Mi (F + 0x124) = v141)
    (sl128 : memLoad32 Mi (F + 0x128) = v186)
    (sl12C : memLoad32 Mi (F + 0x12C) = v169)
    (sl130 : memLoad32 Mi (F + 0x130) = v226)
    (sl134 : memLoad32 Mi (F + 0x134) = v147)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v840 v841 v842 v843 v844 v846 v847 v848 v850 v851 v853 v855 v856 v857 v858 v859 v860 v861 v863 v865 v866 v868 v870 v871 v872 v874 v875 v876 v878 v879 : Word),
      Steps n n' ∧
      St M' B n' 0xAAC (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v228 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v747 ∧
      reg n' (6 : Fin 32) = v823 ∧
      reg n' (7 : Fin 32) = v825 ∧
      reg n' (8 : Fin 32) = v868 ∧
      reg n' (9 : Fin 32) = v879 ∧
      reg n' a0 = v860 ∧
      reg n' a1 = v604 ∧
      reg n' a2 = v875 ∧
      reg n' a3 = v878 ∧
      reg n' a4 = v139 ∧
      reg n' a5 = v858 ∧
      reg n' a6 = v876 ∧
      reg n' a7 = v278 ∧
      reg n' (18 : Fin 32) = v662 ∧
      reg n' (19 : Fin 32) = v827 ∧
      reg n' (20 : Fin 32) = v239 ∧
      reg n' (21 : Fin 32) = v470 ∧
      reg n' (22 : Fin 32) = v293 ∧
      reg n' (23 : Fin 32) = v355 ∧
      reg n' (24 : Fin 32) = v226 ∧
      reg n' (25 : Fin 32) = v663 ∧
      reg n' (26 : Fin 32) = v523 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v830 ∧
      reg n' (29 : Fin 32) = v272 ∧
      reg n' (30 : Fin 32) = v234 ∧
      reg n' (31 : Fin 32) = v843 ∧
      memLoad32 M' (F + 0x78) = v638 ∧
      memLoad32 M' (F + 0x7C) = v636 ∧
      memLoad32 M' (F + 0x84) = v608 ∧
      memLoad32 M' (F + 0x88) = v610 ∧
      memLoad32 M' (F + 0x8C) = v620 ∧
      memLoad32 M' (F + 0x90) = v618 ∧
      memLoad32 M' (F + 0x94) = v595 ∧
      memLoad32 M' (F + 0x98) = v593 ∧
      memLoad32 M' (F + 0x9C) = v651 ∧
      memLoad32 M' (F + 0xA4) = v647 ∧
      memLoad32 M' (F + 0xA8) = v624 ∧
      memLoad32 M' (F + 0xAC) = v341 ∧
      memLoad32 M' (F + 0xB8) = v641 ∧
      memLoad32 M' (F + 0xC0) = v653 ∧
      memLoad32 M' (F + 0xC8) = v507 ∧
      memLoad32 M' (F + 0xD4) = v455 ∧
      memLoad32 M' (F + 0xD8) = v280 ∧
      memLoad32 M' (F + 0xDC) = v274 ∧
      memLoad32 M' (F + 0xE0) = v386 ∧
      memLoad32 M' (F + 0xE4) = v322 ∧
      memLoad32 M' (F + 0xE8) = v384 ∧
      memLoad32 M' (F + 0xEC) = v382 ∧
      memLoad32 M' (F + 0xF0) = v316 ∧
      memLoad32 M' (F + 0xF4) = v314 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v401 ∧
      memLoad32 M' (F + 0x10C) = v622 ∧
      memLoad32 M' (F + 0x110) = v645 ∧
      memLoad32 M' (F + 0x118) = v739 ∧
      memLoad32 M' (F + 0x11C) = v733 ∧
      memLoad32 M' (F + 0x124) = v141 ∧
      memLoad32 M' (F + 0x128) = v186 ∧
      memLoad32 M' (F + 0x12C) = v169 ∧
      memLoad32 M' (F + 0x130) = v226 ∧
      memLoad32 M' (F + 0x134) = v147 ∧
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
      aluEval .add v831 v838 = v840 ∧
      aluEval .add v834 v839 = v841 ∧
      aluEval .sltu v825 v823 = v842 ∧
      aluEval .and v827 v226 = v843 ∧
      aluEval .mulhu v843 v228 = v844 ∧
      aluEval .sltu v837 v122 = v846 ∧
      aluEval .add v840 v842 = v847 ∧
      aluEval .sub v841 v846 = v848 ∧
      aluEval .sub v848 v139 = v850 ∧
      aluEval .sub v837 v122 = v851 ∧
      aluEval .srl v285 0xC = v853 ∧
      aluEval .sll v266 0x14 = v855 ∧
      aluEval .add v850 v853 = v856 ∧
      aluEval .add v855 v851 = v857 ∧
      aluEval .mul v843 v228 = v858 ∧
      aluEval .sltu v857 v851 = v859 ∧
      aluEval .add v847 v844 = v860 ∧
      aluEval .add v856 v859 = v861 ∧
      aluEval .add v861 v612 = v863 ∧
      aluEval .add v616 v857 = v865 ∧
      aluEval .sltu v865 v857 = v866 ∧
      aluEval .add v589 v865 = v868 ∧
      aluEval .add v866 v591 = v870 ∧
      aluEval .sltu v868 v865 = v871 ∧
      aluEval .add v863 v870 = v872 ∧
      aluEval .add v871 v604 = v874 ∧
      aluEval .add v872 v874 = v875 ∧
      aluEval .add v858 v825 = v876 ∧
      aluEval .add v601 v868 = v878 ∧
      aluEval .mulhu v523 v700 = v879 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n840, v840, d840, hv840, u840⟩ := s.aluG hc smm_at_a44 (off' := 0xA46) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv840
  obtain ⟨n841, v841, d841, hv841, u841⟩ := u840.aluG hc smm_at_a46 (off' := 0xA48) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv841
  obtain ⟨n842, v842, d842, hv842, u842⟩ := u841.aluG hc smm_at_a48 (off' := 0xA4C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv842
  obtain ⟨n843, v843, d843, hv843, u843⟩ := u842.aluG hc smm_at_a4c (off' := 0xA50) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv843
  obtain ⟨n844, v844, d844, hv844, u844⟩ := u843.aluG hc smm_at_a50 (off' := 0xA54) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv844
  obtain ⟨n845, d845, u845⟩ := u844.lwE hc smm_at_a54 (off' := 0xA58) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 260) (by decide)) (v := v122)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl104])
  obtain ⟨n846, v846, d846, hv846, u846⟩ := u845.aluG hc smm_at_a58 (off' := 0xA5C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv846
  obtain ⟨n847, v847, d847, hv847, u847⟩ := u846.aluG hc smm_at_a5c (off' := 0xA5E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv847
  obtain ⟨n848, v848, d848, hv848, u848⟩ := u847.aluG hc smm_at_a5e (off' := 0xA60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv848
  obtain ⟨n849, d849, u849⟩ := u848.lwE hc smm_at_a60 (off' := 0xA64) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 288) (by decide)) (v := v139)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl120])
  obtain ⟨n850, v850, d850, hv850, u850⟩ := u849.aluG hc smm_at_a64 (off' := 0xA66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv850
  obtain ⟨n851, v851, d851, hv851, u851⟩ := u850.aluG hc smm_at_a66 (off' := 0xA68) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv851
  obtain ⟨n852, d852, u852⟩ := u851.lwE hc smm_at_a68 (off' := 0xA6A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 160) (by decide)) (v := v285)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slA0])
  obtain ⟨n853, v853, d853, hv853, u853⟩ := u852.aluImmG hc smm_at_a6a (off' := 0xA6C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv853
  obtain ⟨n854, d854, u854⟩ := u853.lwE hc smm_at_a6c (off' := 0xA6E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 208) (by decide)) (v := v266)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slD0])
  obtain ⟨n855, v855, d855, hv855, u855⟩ := u854.aluImmG hc smm_at_a6e (off' := 0xA70) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv855
  obtain ⟨n856, v856, d856, hv856, u856⟩ := u855.aluG hc smm_at_a70 (off' := 0xA72) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv856
  obtain ⟨n857, v857, d857, hv857, u857⟩ := u856.aluG hc smm_at_a72 (off' := 0xA74) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv857
  obtain ⟨n858, v858, d858, hv858, u858⟩ := u857.aluG hc smm_at_a74 (off' := 0xA78) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv858
  obtain ⟨n859, v859, d859, hv859, u859⟩ := u858.aluG hc smm_at_a78 (off' := 0xA7C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv859
  obtain ⟨n860, v860, d860, hv860, u860⟩ := u859.aluG hc smm_at_a7c (off' := 0xA7E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv860
  obtain ⟨n861, v861, d861, hv861, u861⟩ := u860.aluG hc smm_at_a7e (off' := 0xA80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv861
  obtain ⟨n862, d862, u862⟩ := u861.lwE hc smm_at_a80 (off' := 0xA82) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 100) (by decide)) (v := v612)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl64])
  obtain ⟨n863, v863, d863, hv863, u863⟩ := u862.aluG hc smm_at_a82 (off' := 0xA84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv863
  obtain ⟨n864, d864, u864⟩ := u863.lwE hc smm_at_a84 (off' := 0xA86) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 92) (by decide)) (v := v616)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl5C])
  obtain ⟨n865, v865, d865, hv865, u865⟩ := u864.aluG hc smm_at_a86 (off' := 0xA88) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv865
  obtain ⟨n866, v866, d866, hv866, u866⟩ := u865.aluG hc smm_at_a88 (off' := 0xA8C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv866
  obtain ⟨n867, d867, u867⟩ := u866.lwE hc smm_at_a8c (off' := 0xA8E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 112) (by decide)) (v := v589)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl70])
  obtain ⟨n868, v868, d868, hv868, u868⟩ := u867.aluG hc smm_at_a8e (off' := 0xA90) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv868
  obtain ⟨n869, d869, u869⟩ := u868.lwE hc smm_at_a90 (off' := 0xA92) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 108) (by decide)) (v := v591)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl6C])
  obtain ⟨n870, v870, d870, hv870, u870⟩ := u869.aluG hc smm_at_a92 (off' := 0xA94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv870
  obtain ⟨n871, v871, d871, hv871, u871⟩ := u870.aluG hc smm_at_a94 (off' := 0xA98) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv871
  obtain ⟨n872, v872, d872, hv872, u872⟩ := u871.aluG hc smm_at_a98 (off' := 0xA9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv872
  obtain ⟨n873, d873, u873⟩ := u872.lwE hc smm_at_a9a (off' := 0xA9C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 104) (by decide)) (v := v604)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl68])
  obtain ⟨n874, v874, d874, hv874, u874⟩ := u873.aluG hc smm_at_a9c (off' := 0xA9E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv874
  obtain ⟨n875, v875, d875, hv875, u875⟩ := u874.aluG hc smm_at_a9e (off' := 0xAA0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv875
  obtain ⟨n876, v876, d876, hv876, u876⟩ := u875.aluG hc smm_at_aa0 (off' := 0xAA4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv876
  obtain ⟨n877, d877, u877⟩ := u876.lwE hc smm_at_aa4 (off' := 0xAA6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 116) (by decide)) (v := v601)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl74])
  obtain ⟨n878, v878, d878, hv878, u878⟩ := u877.aluG hc smm_at_aa6 (off' := 0xAA8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv878
  obtain ⟨n879, v879, d879, hv879, u879⟩ := u878.aluG hc smm_at_aa8 (off' := 0xAAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv879
  have qo1 : reg n879 ra = v228 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n879 sp = F := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n879 (3 : Fin 32) = G3 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n879 (4 : Fin 32) = G4 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n879 (5 : Fin 32) = v747 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n879 (6 : Fin 32) = v823 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n879 (7 : Fin 32) = v825 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n879 (8 : Fin 32) = v868 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n879 (9 : Fin 32) = v879 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n879 a0 = v860 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n879 a1 = v604 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n879 a2 = v875 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n879 a3 = v878 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n879 a4 = v139 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n879 a5 = v858 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n879 a6 = v876 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n879 a7 = v278 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n879 (18 : Fin 32) = v662 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n879 (19 : Fin 32) = v827 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n879 (20 : Fin 32) = v239 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n879 (21 : Fin 32) = v470 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n879 (22 : Fin 32) = v293 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n879 (23 : Fin 32) = v355 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n879 (24 : Fin 32) = v226 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n879 (25 : Fin 32) = v663 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n879 (26 : Fin 32) = v523 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n879 (27 : Fin 32) = v700 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n879 (28 : Fin 32) = v830 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n879 (29 : Fin 32) = v272 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n879 (30 : Fin 32) = v234 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n879 (31 : Fin 32) = v843 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so78 : memLoad32 Mi (F + 0x78) = v638 := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = v636 := by
    rw [sl7C]
  have so84 : memLoad32 Mi (F + 0x84) = v608 := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = v610 := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = v620 := by
    rw [sl8C]
  have so90 : memLoad32 Mi (F + 0x90) = v618 := by
    rw [sl90]
  have so94 : memLoad32 Mi (F + 0x94) = v595 := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = v593 := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = v651 := by
    rw [sl9C]
  have soA4 : memLoad32 Mi (F + 0xA4) = v647 := by
    rw [slA4]
  have soA8 : memLoad32 Mi (F + 0xA8) = v624 := by
    rw [slA8]
  have soAC : memLoad32 Mi (F + 0xAC) = v341 := by
    rw [slAC]
  have soB8 : memLoad32 Mi (F + 0xB8) = v641 := by
    rw [slB8]
  have soC0 : memLoad32 Mi (F + 0xC0) = v653 := by
    rw [slC0]
  have soC8 : memLoad32 Mi (F + 0xC8) = v507 := by
    rw [slC8]
  have soD4 : memLoad32 Mi (F + 0xD4) = v455 := by
    rw [slD4]
  have soD8 : memLoad32 Mi (F + 0xD8) = v280 := by
    rw [slD8]
  have soDC : memLoad32 Mi (F + 0xDC) = v274 := by
    rw [slDC]
  have soE0 : memLoad32 Mi (F + 0xE0) = v386 := by
    rw [slE0]
  have soE4 : memLoad32 Mi (F + 0xE4) = v322 := by
    rw [slE4]
  have soE8 : memLoad32 Mi (F + 0xE8) = v384 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v382 := by
    rw [slEC]
  have soF0 : memLoad32 Mi (F + 0xF0) = v316 := by
    rw [slF0]
  have soF4 : memLoad32 Mi (F + 0xF4) = v314 := by
    rw [slF4]
  have soF8 : memLoad32 Mi (F + 0xF8) = outp := by
    rw [slF8]
  have so100 : memLoad32 Mi (F + 0x100) = v401 := by
    rw [sl100]
  have so10C : memLoad32 Mi (F + 0x10C) = v622 := by
    rw [sl10C]
  have so110 : memLoad32 Mi (F + 0x110) = v645 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v739 := by
    rw [sl118]
  have so11C : memLoad32 Mi (F + 0x11C) = v733 := by
    rw [sl11C]
  have so124 : memLoad32 Mi (F + 0x124) = v141 := by
    rw [sl124]
  have so128 : memLoad32 Mi (F + 0x128) = v186 := by
    rw [sl128]
  have so12C : memLoad32 Mi (F + 0x12C) = v169 := by
    rw [sl12C]
  have so130 : memLoad32 Mi (F + 0x130) = v226 := by
    rw [sl130]
  have so134 : memLoad32 Mi (F + 0x134) = v147 := by
    rw [sl134]
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
  exact ⟨n879, Mi, v840, v841, v842, v843, v844, v846, v847, v848, v850, v851, v853, v855, v856, v857, v858, v859, v860, v861, v863, v865, v866, v868, v870, v871, v872, v874, v875, v876, v878, v879, (.cons d840 (.cons d841 (.cons d842 (.cons d843 (.cons d844 (.cons d845 (.cons d846 (.cons d847 (.cons d848 (.cons d849 (.cons d850 (.cons d851 (.cons d852 (.cons d853 (.cons d854 (.cons d855 (.cons d856 (.cons d857 (.cons d858 (.cons d859 (.cons d860 (.cons d861 (.cons d862 (.cons d863 (.cons d864 (.cons d865 (.cons d866 (.cons d867 (.cons d868 (.cons d869 (.cons d870 (.cons d871 (.cons d872 (.cons d873 (.cons d874 (.cons d875 (.cons d876 (.cons d877 (.cons d878 (.single d879)))))))))))))))))))))))))))))))))))))))), u879.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so78, so7C, so84, so88, so8C, so90, so94, so98, so9C, soA4, soA8, soAC, soB8, soC0, soC8, soD4, soD8, soDC, soE0, soE4, soE8, soEC, soF0, soF4, soF8, so100, so10C, so110, so118, so11C, so124, so128, so12C, so130, so134, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv840, hv841, hv842, hv843, hv844, hv846, hv847, hv848, hv850, hv851, hv853, hv855, hv856, hv857, hv858, hv859, hv860, hv861, hv863, hv865, hv866, hv868, hv870, hv871, hv872, hv874, hv875, hv876, hv878, hv879⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g28 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v139 v141 v147 v169 v186 v226 v228 v234 v239 v272 v274 v278 v280 v293 v314 v316 v322 v341 v355 v382 v384 v386 v401 v455 v470 v507 v523 v593 v595 v604 v608 v610 v618 v620 v622 v624 v636 v638 v641 v645 v647 v651 v653 v662 v663 v700 v733 v739 v747 v823 v825 v827 v830 v843 v858 v860 v868 v875 v876 v878 v879 : Word}
    (s : St Mi B n 0xAAC (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v228)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v747)
    (q6 : reg n (6 : Fin 32) = v823)
    (q7 : reg n (7 : Fin 32) = v825)
    (q8 : reg n (8 : Fin 32) = v868)
    (q9 : reg n (9 : Fin 32) = v879)
    (q10 : reg n a0 = v860)
    (q11 : reg n a1 = v604)
    (q12 : reg n a2 = v875)
    (q13 : reg n a3 = v878)
    (q14 : reg n a4 = v139)
    (q15 : reg n a5 = v858)
    (q16 : reg n a6 = v876)
    (q17 : reg n a7 = v278)
    (q18 : reg n (18 : Fin 32) = v662)
    (q19 : reg n (19 : Fin 32) = v827)
    (q20 : reg n (20 : Fin 32) = v239)
    (q21 : reg n (21 : Fin 32) = v470)
    (q22 : reg n (22 : Fin 32) = v293)
    (q23 : reg n (23 : Fin 32) = v355)
    (q24 : reg n (24 : Fin 32) = v226)
    (q25 : reg n (25 : Fin 32) = v663)
    (q26 : reg n (26 : Fin 32) = v523)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v830)
    (q29 : reg n (29 : Fin 32) = v272)
    (q30 : reg n (30 : Fin 32) = v234)
    (q31 : reg n (31 : Fin 32) = v843)
    (sl78 : memLoad32 Mi (F + 0x78) = v638)
    (sl7C : memLoad32 Mi (F + 0x7C) = v636)
    (sl84 : memLoad32 Mi (F + 0x84) = v608)
    (sl88 : memLoad32 Mi (F + 0x88) = v610)
    (sl8C : memLoad32 Mi (F + 0x8C) = v620)
    (sl90 : memLoad32 Mi (F + 0x90) = v618)
    (sl94 : memLoad32 Mi (F + 0x94) = v595)
    (sl98 : memLoad32 Mi (F + 0x98) = v593)
    (sl9C : memLoad32 Mi (F + 0x9C) = v651)
    (slA4 : memLoad32 Mi (F + 0xA4) = v647)
    (slA8 : memLoad32 Mi (F + 0xA8) = v624)
    (slAC : memLoad32 Mi (F + 0xAC) = v341)
    (slB8 : memLoad32 Mi (F + 0xB8) = v641)
    (slC0 : memLoad32 Mi (F + 0xC0) = v653)
    (slC8 : memLoad32 Mi (F + 0xC8) = v507)
    (slD4 : memLoad32 Mi (F + 0xD4) = v455)
    (slD8 : memLoad32 Mi (F + 0xD8) = v280)
    (slDC : memLoad32 Mi (F + 0xDC) = v274)
    (slE0 : memLoad32 Mi (F + 0xE0) = v386)
    (slE4 : memLoad32 Mi (F + 0xE4) = v322)
    (slE8 : memLoad32 Mi (F + 0xE8) = v384)
    (slEC : memLoad32 Mi (F + 0xEC) = v382)
    (slF0 : memLoad32 Mi (F + 0xF0) = v316)
    (slF4 : memLoad32 Mi (F + 0xF4) = v314)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v401)
    (sl10C : memLoad32 Mi (F + 0x10C) = v622)
    (sl110 : memLoad32 Mi (F + 0x110) = v645)
    (sl118 : memLoad32 Mi (F + 0x118) = v739)
    (sl11C : memLoad32 Mi (F + 0x11C) = v733)
    (sl124 : memLoad32 Mi (F + 0x124) = v141)
    (sl128 : memLoad32 Mi (F + 0x128) = v186)
    (sl12C : memLoad32 Mi (F + 0x12C) = v169)
    (sl130 : memLoad32 Mi (F + 0x130) = v226)
    (sl134 : memLoad32 Mi (F + 0x134) = v147)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v880 v881 v883 v884 v885 v886 v887 v889 v890 v891 v892 v893 v894 v895 v896 v897 v898 v899 v900 v901 v902 v903 v904 v905 v906 v907 v908 v909 v910 v911 v912 v913 v914 v915 v916 v917 : Word),
      Steps n n' ∧
      St M' B n' 0xB22 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v228 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v747 ∧
      reg n' (6 : Fin 32) = v909 ∧
      reg n' (7 : Fin 32) = v898 ∧
      reg n' (8 : Fin 32) = v891 ∧
      reg n' (9 : Fin 32) = v905 ∧
      reg n' a0 = v917 ∧
      reg n' a1 = v912 ∧
      reg n' a2 = v916 ∧
      reg n' a3 = v147 ∧
      reg n' a4 = v608 ∧
      reg n' a5 = v901 ∧
      reg n' a6 = v876 ∧
      reg n' a7 = v278 ∧
      reg n' (18 : Fin 32) = v662 ∧
      reg n' (19 : Fin 32) = v827 ∧
      reg n' (20 : Fin 32) = v239 ∧
      reg n' (21 : Fin 32) = v470 ∧
      reg n' (22 : Fin 32) = v293 ∧
      reg n' (23 : Fin 32) = v355 ∧
      reg n' (24 : Fin 32) = v274 ∧
      reg n' (25 : Fin 32) = v280 ∧
      reg n' (26 : Fin 32) = v523 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v830 ∧
      reg n' (29 : Fin 32) = v272 ∧
      reg n' (30 : Fin 32) = v234 ∧
      reg n' (31 : Fin 32) = v843 ∧
      memLoad32 M' (F + 0x78) = v638 ∧
      memLoad32 M' (F + 0x7C) = v636 ∧
      memLoad32 M' (F + 0x88) = v610 ∧
      memLoad32 M' (F + 0x8C) = v620 ∧
      memLoad32 M' (F + 0x90) = v618 ∧
      memLoad32 M' (F + 0x94) = v595 ∧
      memLoad32 M' (F + 0x98) = v593 ∧
      memLoad32 M' (F + 0x9C) = v651 ∧
      memLoad32 M' (F + 0xA4) = v647 ∧
      memLoad32 M' (F + 0xA8) = v624 ∧
      memLoad32 M' (F + 0xAC) = v341 ∧
      memLoad32 M' (F + 0xB8) = v641 ∧
      memLoad32 M' (F + 0xC0) = v653 ∧
      memLoad32 M' (F + 0xC8) = v507 ∧
      memLoad32 M' (F + 0xD4) = v455 ∧
      memLoad32 M' (F + 0xE0) = v386 ∧
      memLoad32 M' (F + 0xE4) = v322 ∧
      memLoad32 M' (F + 0xE8) = v384 ∧
      memLoad32 M' (F + 0xEC) = v382 ∧
      memLoad32 M' (F + 0xF0) = v316 ∧
      memLoad32 M' (F + 0xF4) = v314 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v401 ∧
      memLoad32 M' (F + 0x10C) = v622 ∧
      memLoad32 M' (F + 0x110) = v645 ∧
      memLoad32 M' (F + 0x118) = v739 ∧
      memLoad32 M' (F + 0x11C) = v733 ∧
      memLoad32 M' (F + 0x124) = v141 ∧
      memLoad32 M' (F + 0x128) = v186 ∧
      memLoad32 M' (F + 0x12C) = v169 ∧
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
      aluEval .sltu v876 v858 = v880 ∧
      aluEval .sltu v878 v868 = v881 ∧
      aluEval .sub v881 v280 = v883 ∧
      aluEval .mul v523 v700 = v884 ∧
      aluEval .add v860 v880 = v885 ∧
      aluEval .add v875 v883 = v886 ∧
      aluEval .mul v662 v355 = v887 ∧
      aluEval .sltu v878 v274 = v889 ∧
      aluEval .sub v886 v889 = v890 ∧
      aluEval .mulhu v662 v355 = v891 ∧
      aluEval .add v890 v879 = v892 ∧
      aluEval .mul v747 v293 = v893 ∧
      aluEval .sub v878 v274 = v894 ∧
      aluEval .mulhu v747 v293 = v895 ∧
      aluEval .add v884 v894 = v896 ∧
      aluEval .mul v843 v239 = v897 ∧
      aluEval .mulhu v843 v239 = v898 ∧
      aluEval .sltu v896 v894 = v899 ∧
      aluEval .add v892 v899 = v900 ∧
      aluEval .add v887 v896 = v901 ∧
      aluEval .add v900 v891 = v902 ∧
      aluEval .sltu v901 v896 = v903 ∧
      aluEval .add v902 v903 = v904 ∧
      aluEval .add v893 v901 = v905 ∧
      aluEval .add v895 v904 = v906 ∧
      aluEval .sltu v905 v901 = v907 ∧
      aluEval .add v906 v907 = v908 ∧
      aluEval .add v897 v905 = v909 ∧
      aluEval .add v908 v898 = v910 ∧
      aluEval .sltu v909 v905 = v911 ∧
      aluEval .add v910 v911 = v912 ∧
      aluEval .srl v876 0x1D = v913 ∧
      aluEval .sll v885 0x3 = v914 ∧
      aluEval .srl v885 0x1D = v915 ∧
      aluEval .or v913 v914 = v916 ∧
      aluEval .add v915 v912 = v917 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n880, v880, d880, hv880, u880⟩ := s.aluG hc smm_at_aac (off' := 0xAB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv880
  obtain ⟨n881, v881, d881, hv881, u881⟩ := u880.aluG hc smm_at_ab0 (off' := 0xAB4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv881
  obtain ⟨n882, d882, u882⟩ := u881.lwE hc smm_at_ab4 (off' := 0xAB6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 216) (by decide)) (v := v280)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slD8])
  obtain ⟨n883, v883, d883, hv883, u883⟩ := u882.aluG hc smm_at_ab6 (off' := 0xABA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv883
  obtain ⟨n884, v884, d884, hv884, u884⟩ := u883.aluG hc smm_at_aba (off' := 0xABE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv884
  obtain ⟨n885, v885, d885, hv885, u885⟩ := u884.aluG hc smm_at_abe (off' := 0xAC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv885
  obtain ⟨n886, v886, d886, hv886, u886⟩ := u885.aluG hc smm_at_ac0 (off' := 0xAC2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv886
  obtain ⟨n887, v887, d887, hv887, u887⟩ := u886.aluG hc smm_at_ac2 (off' := 0xAC6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv887
  obtain ⟨n888, d888, u888⟩ := u887.lwE hc smm_at_ac6 (off' := 0xAC8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 220) (by decide)) (v := v274)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slDC])
  obtain ⟨n889, v889, d889, hv889, u889⟩ := u888.aluG hc smm_at_ac8 (off' := 0xACC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv889
  obtain ⟨n890, v890, d890, hv890, u890⟩ := u889.aluG hc smm_at_acc (off' := 0xACE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv890
  obtain ⟨n891, v891, d891, hv891, u891⟩ := u890.aluG hc smm_at_ace (off' := 0xAD2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv891
  obtain ⟨n892, v892, d892, hv892, u892⟩ := u891.aluG hc smm_at_ad2 (off' := 0xAD4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv892
  obtain ⟨n893, v893, d893, hv893, u893⟩ := u892.aluG hc smm_at_ad4 (off' := 0xAD8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv893
  obtain ⟨n894, v894, d894, hv894, u894⟩ := u893.aluG hc smm_at_ad8 (off' := 0xADC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv894
  obtain ⟨n895, v895, d895, hv895, u895⟩ := u894.aluG hc smm_at_adc (off' := 0xAE0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv895
  obtain ⟨n896, v896, d896, hv896, u896⟩ := u895.aluG hc smm_at_ae0 (off' := 0xAE2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv896
  obtain ⟨n897, v897, d897, hv897, u897⟩ := u896.aluG hc smm_at_ae2 (off' := 0xAE6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv897
  obtain ⟨n898, v898, d898, hv898, u898⟩ := u897.aluG hc smm_at_ae6 (off' := 0xAEA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv898
  obtain ⟨n899, v899, d899, hv899, u899⟩ := u898.aluG hc smm_at_aea (off' := 0xAEE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv899
  obtain ⟨n900, v900, d900, hv900, u900⟩ := u899.aluG hc smm_at_aee (off' := 0xAF0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv900
  obtain ⟨n901, v901, d901, hv901, u901⟩ := u900.aluG hc smm_at_af0 (off' := 0xAF2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv901
  obtain ⟨n902, v902, d902, hv902, u902⟩ := u901.aluG hc smm_at_af2 (off' := 0xAF4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv902
  obtain ⟨n903, v903, d903, hv903, u903⟩ := u902.aluG hc smm_at_af4 (off' := 0xAF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv903
  obtain ⟨n904, v904, d904, hv904, u904⟩ := u903.aluG hc smm_at_af8 (off' := 0xAFA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv904
  obtain ⟨n905, v905, d905, hv905, u905⟩ := u904.aluG hc smm_at_afa (off' := 0xAFC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv905
  obtain ⟨n906, v906, d906, hv906, u906⟩ := u905.aluG hc smm_at_afc (off' := 0xAFE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv906
  obtain ⟨n907, v907, d907, hv907, u907⟩ := u906.aluG hc smm_at_afe (off' := 0xB02) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv907
  obtain ⟨n908, v908, d908, hv908, u908⟩ := u907.aluG hc smm_at_b02 (off' := 0xB04) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv908
  obtain ⟨n909, v909, d909, hv909, u909⟩ := u908.aluG hc smm_at_b04 (off' := 0xB06) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv909
  obtain ⟨n910, v910, d910, hv910, u910⟩ := u909.aluG hc smm_at_b06 (off' := 0xB08) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv910
  obtain ⟨n911, v911, d911, hv911, u911⟩ := u910.aluG hc smm_at_b08 (off' := 0xB0C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv911
  obtain ⟨n912, v912, d912, hv912, u912⟩ := u911.aluG hc smm_at_b0c (off' := 0xB0E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv912
  obtain ⟨n913, v913, d913, hv913, u913⟩ := u912.aluImmG hc smm_at_b0e (off' := 0xB12) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv913
  obtain ⟨n914, v914, d914, hv914, u914⟩ := u913.aluImmG hc smm_at_b12 (off' := 0xB16) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv914
  obtain ⟨n915, v915, d915, hv915, u915⟩ := u914.aluImmG hc smm_at_b16 (off' := 0xB18) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv915
  obtain ⟨n916, v916, d916, hv916, u916⟩ := u915.aluG hc smm_at_b18 (off' := 0xB1A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv916
  obtain ⟨n917, v917, d917, hv917, u917⟩ := u916.aluG hc smm_at_b1a (off' := 0xB1C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv917
  obtain ⟨n918, d918, u918⟩ := u917.lwE hc smm_at_b1c (off' := 0xB20) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 308) (by decide)) (v := v147)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl134])
  obtain ⟨n919, d919, u919⟩ := u918.lwE hc smm_at_b20 (off' := 0xB22) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 132) (by decide)) (v := v608)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl84])
  have qo1 : reg n919 ra = v228 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n919 sp = F := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n919 (3 : Fin 32) = G3 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n919 (4 : Fin 32) = G4 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n919 (5 : Fin 32) = v747 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n919 (6 : Fin 32) = v909 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n919 (7 : Fin 32) = v898 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n919 (8 : Fin 32) = v891 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n919 (9 : Fin 32) = v905 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n919 a0 = v917 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n919 a1 = v912 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n919 a2 = v916 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n919 a3 = v147 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n919 a4 = v608 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n919 a5 = v901 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n919 a6 = v876 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n919 a7 = v278 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n919 (18 : Fin 32) = v662 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n919 (19 : Fin 32) = v827 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n919 (20 : Fin 32) = v239 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n919 (21 : Fin 32) = v470 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n919 (22 : Fin 32) = v293 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n919 (23 : Fin 32) = v355 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n919 (24 : Fin 32) = v274 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n919 (25 : Fin 32) = v280 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n919 (26 : Fin 32) = v523 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n919 (27 : Fin 32) = v700 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n919 (28 : Fin 32) = v830 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n919 (29 : Fin 32) = v272 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n919 (30 : Fin 32) = v234 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n919 (31 : Fin 32) = v843 := by rw [u919.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so78 : memLoad32 Mi (F + 0x78) = v638 := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = v636 := by
    rw [sl7C]
  have so88 : memLoad32 Mi (F + 0x88) = v610 := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = v620 := by
    rw [sl8C]
  have so90 : memLoad32 Mi (F + 0x90) = v618 := by
    rw [sl90]
  have so94 : memLoad32 Mi (F + 0x94) = v595 := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = v593 := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = v651 := by
    rw [sl9C]
  have soA4 : memLoad32 Mi (F + 0xA4) = v647 := by
    rw [slA4]
  have soA8 : memLoad32 Mi (F + 0xA8) = v624 := by
    rw [slA8]
  have soAC : memLoad32 Mi (F + 0xAC) = v341 := by
    rw [slAC]
  have soB8 : memLoad32 Mi (F + 0xB8) = v641 := by
    rw [slB8]
  have soC0 : memLoad32 Mi (F + 0xC0) = v653 := by
    rw [slC0]
  have soC8 : memLoad32 Mi (F + 0xC8) = v507 := by
    rw [slC8]
  have soD4 : memLoad32 Mi (F + 0xD4) = v455 := by
    rw [slD4]
  have soE0 : memLoad32 Mi (F + 0xE0) = v386 := by
    rw [slE0]
  have soE4 : memLoad32 Mi (F + 0xE4) = v322 := by
    rw [slE4]
  have soE8 : memLoad32 Mi (F + 0xE8) = v384 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v382 := by
    rw [slEC]
  have soF0 : memLoad32 Mi (F + 0xF0) = v316 := by
    rw [slF0]
  have soF4 : memLoad32 Mi (F + 0xF4) = v314 := by
    rw [slF4]
  have soF8 : memLoad32 Mi (F + 0xF8) = outp := by
    rw [slF8]
  have so100 : memLoad32 Mi (F + 0x100) = v401 := by
    rw [sl100]
  have so10C : memLoad32 Mi (F + 0x10C) = v622 := by
    rw [sl10C]
  have so110 : memLoad32 Mi (F + 0x110) = v645 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v739 := by
    rw [sl118]
  have so11C : memLoad32 Mi (F + 0x11C) = v733 := by
    rw [sl11C]
  have so124 : memLoad32 Mi (F + 0x124) = v141 := by
    rw [sl124]
  have so128 : memLoad32 Mi (F + 0x128) = v186 := by
    rw [sl128]
  have so12C : memLoad32 Mi (F + 0x12C) = v169 := by
    rw [sl12C]
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
  exact ⟨n919, Mi, v880, v881, v883, v884, v885, v886, v887, v889, v890, v891, v892, v893, v894, v895, v896, v897, v898, v899, v900, v901, v902, v903, v904, v905, v906, v907, v908, v909, v910, v911, v912, v913, v914, v915, v916, v917, (.cons d880 (.cons d881 (.cons d882 (.cons d883 (.cons d884 (.cons d885 (.cons d886 (.cons d887 (.cons d888 (.cons d889 (.cons d890 (.cons d891 (.cons d892 (.cons d893 (.cons d894 (.cons d895 (.cons d896 (.cons d897 (.cons d898 (.cons d899 (.cons d900 (.cons d901 (.cons d902 (.cons d903 (.cons d904 (.cons d905 (.cons d906 (.cons d907 (.cons d908 (.cons d909 (.cons d910 (.cons d911 (.cons d912 (.cons d913 (.cons d914 (.cons d915 (.cons d916 (.cons d917 (.cons d918 (.single d919)))))))))))))))))))))))))))))))))))))))), u919.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so78, so7C, so88, so8C, so90, so94, so98, so9C, soA4, soA8, soAC, soB8, soC0, soC8, soD4, soE0, soE4, soE8, soEC, soF0, soF4, soF8, so100, so10C, so110, so118, so11C, so124, so128, so12C, so130, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv880, hv881, hv883, hv884, hv885, hv886, hv887, hv889, hv890, hv891, hv892, hv893, hv894, hv895, hv896, hv897, hv898, hv899, hv900, hv901, hv902, hv903, hv904, hv905, hv906, hv907, hv908, hv909, hv910, hv911, hv912, hv913, hv914, hv915, hv916, hv917⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g29 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v141 v147 v169 v186 v226 v228 v234 v239 v272 v274 v278 v280 v293 v314 v316 v322 v341 v355 v382 v384 v386 v401 v455 v470 v507 v523 v593 v595 v608 v610 v618 v620 v622 v624 v636 v638 v641 v645 v647 v651 v653 v662 v700 v733 v739 v747 v827 v830 v843 v876 v891 v898 v901 v905 v909 v912 v916 v917 : Word}
    (s : St Mi B n 0xB22 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v228)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v747)
    (q6 : reg n (6 : Fin 32) = v909)
    (q7 : reg n (7 : Fin 32) = v898)
    (q8 : reg n (8 : Fin 32) = v891)
    (q9 : reg n (9 : Fin 32) = v905)
    (q10 : reg n a0 = v917)
    (q11 : reg n a1 = v912)
    (q12 : reg n a2 = v916)
    (q13 : reg n a3 = v147)
    (q14 : reg n a4 = v608)
    (q15 : reg n a5 = v901)
    (q16 : reg n a6 = v876)
    (q17 : reg n a7 = v278)
    (q18 : reg n (18 : Fin 32) = v662)
    (q19 : reg n (19 : Fin 32) = v827)
    (q20 : reg n (20 : Fin 32) = v239)
    (q21 : reg n (21 : Fin 32) = v470)
    (q22 : reg n (22 : Fin 32) = v293)
    (q23 : reg n (23 : Fin 32) = v355)
    (q24 : reg n (24 : Fin 32) = v274)
    (q25 : reg n (25 : Fin 32) = v280)
    (q26 : reg n (26 : Fin 32) = v523)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v830)
    (q29 : reg n (29 : Fin 32) = v272)
    (q30 : reg n (30 : Fin 32) = v234)
    (q31 : reg n (31 : Fin 32) = v843)
    (sl78 : memLoad32 Mi (F + 0x78) = v638)
    (sl7C : memLoad32 Mi (F + 0x7C) = v636)
    (sl88 : memLoad32 Mi (F + 0x88) = v610)
    (sl8C : memLoad32 Mi (F + 0x8C) = v620)
    (sl90 : memLoad32 Mi (F + 0x90) = v618)
    (sl94 : memLoad32 Mi (F + 0x94) = v595)
    (sl98 : memLoad32 Mi (F + 0x98) = v593)
    (sl9C : memLoad32 Mi (F + 0x9C) = v651)
    (slA4 : memLoad32 Mi (F + 0xA4) = v647)
    (slA8 : memLoad32 Mi (F + 0xA8) = v624)
    (slAC : memLoad32 Mi (F + 0xAC) = v341)
    (slB8 : memLoad32 Mi (F + 0xB8) = v641)
    (slC0 : memLoad32 Mi (F + 0xC0) = v653)
    (slC8 : memLoad32 Mi (F + 0xC8) = v507)
    (slD4 : memLoad32 Mi (F + 0xD4) = v455)
    (slE0 : memLoad32 Mi (F + 0xE0) = v386)
    (slE4 : memLoad32 Mi (F + 0xE4) = v322)
    (slE8 : memLoad32 Mi (F + 0xE8) = v384)
    (slEC : memLoad32 Mi (F + 0xEC) = v382)
    (slF0 : memLoad32 Mi (F + 0xF0) = v316)
    (slF4 : memLoad32 Mi (F + 0xF4) = v314)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v401)
    (sl10C : memLoad32 Mi (F + 0x10C) = v622)
    (sl110 : memLoad32 Mi (F + 0x110) = v645)
    (sl118 : memLoad32 Mi (F + 0x118) = v739)
    (sl11C : memLoad32 Mi (F + 0x11C) = v733)
    (sl124 : memLoad32 Mi (F + 0x124) = v141)
    (sl128 : memLoad32 Mi (F + 0x128) = v186)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v920 v921 v923 v925 v927 v928 v930 v932 v933 v935 v936 v938 v940 v941 v942 v944 v945 v946 v947 v949 v950 v951 v953 v954 v955 v956 v958 v959 : Word),
      Steps n n' ∧
      St M' B n' 0xB90 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v314 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v747 ∧
      reg n' (6 : Fin 32) = v950 ∧
      reg n' (7 : Fin 32) = v898 ∧
      reg n' (8 : Fin 32) = v891 ∧
      reg n' (9 : Fin 32) = v959 ∧
      reg n' a0 = v917 ∧
      reg n' a1 = v955 ∧
      reg n' a2 = v956 ∧
      reg n' a3 = v954 ∧
      reg n' a4 = v958 ∧
      reg n' a5 = v938 ∧
      reg n' a6 = v876 ∧
      reg n' a7 = v278 ∧
      reg n' (18 : Fin 32) = v662 ∧
      reg n' (19 : Fin 32) = v827 ∧
      reg n' (20 : Fin 32) = v946 ∧
      reg n' (21 : Fin 32) = v470 ∧
      reg n' (22 : Fin 32) = v293 ∧
      reg n' (23 : Fin 32) = v355 ∧
      reg n' (24 : Fin 32) = v274 ∧
      reg n' (25 : Fin 32) = v280 ∧
      reg n' (26 : Fin 32) = v523 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v830 ∧
      reg n' (29 : Fin 32) = v272 ∧
      reg n' (30 : Fin 32) = v322 ∧
      reg n' (31 : Fin 32) = v843 ∧
      memLoad32 M' (F + 0x9C) = v651 ∧
      memLoad32 M' (F + 0xA4) = v647 ∧
      memLoad32 M' (F + 0xA8) = v624 ∧
      memLoad32 M' (F + 0xB8) = v641 ∧
      memLoad32 M' (F + 0xC0) = v653 ∧
      memLoad32 M' (F + 0xC8) = v507 ∧
      memLoad32 M' (F + 0xD4) = v455 ∧
      memLoad32 M' (F + 0xE0) = v386 ∧
      memLoad32 M' (F + 0xE8) = v384 ∧
      memLoad32 M' (F + 0xEC) = v382 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v401 ∧
      memLoad32 M' (F + 0x10C) = v622 ∧
      memLoad32 M' (F + 0x110) = v645 ∧
      memLoad32 M' (F + 0x118) = v739 ∧
      memLoad32 M' (F + 0x11C) = v733 ∧
      memLoad32 M' (F + 0x128) = v186 ∧
      memLoad32 M' (F + 0x12C) = v169 ∧
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
      aluEval .sltu v608 v147 = v920 ∧
      aluEval .sub v608 v147 = v921 ∧
      aluEval .sub v610 v920 = v923 ∧
      aluEval .add v593 v921 = v925 ∧
      aluEval .add v923 v595 = v927 ∧
      aluEval .sltu v925 v921 = v928 ∧
      aluEval .sub v927 v141 = v930 ∧
      aluEval .add v928 v620 = v932 ∧
      aluEval .add v930 v932 = v933 ∧
      aluEval .add v618 v925 = v935 ∧
      aluEval .sltu v935 v925 = v936 ∧
      aluEval .add v638 v935 = v938 ∧
      aluEval .add v636 v936 = v940 ∧
      aluEval .sltu v938 v935 = v941 ∧
      aluEval .add v933 v940 = v942 ∧
      aluEval .sub v941 v322 = v944 ∧
      aluEval .add v942 v944 = v945 ∧
      aluEval .add v909 v916 = v946 ∧
      aluEval .sltu v946 v909 = v947 ∧
      aluEval .sltu v938 v314 = v949 ∧
      aluEval .add v917 v947 = v950 ∧
      aluEval .sub v945 v949 = v951 ∧
      aluEval .srl v341 0xC = v953 ∧
      aluEval .mul v662 v700 = v954 ∧
      aluEval .add v951 v953 = v955 ∧
      aluEval .mulhu v662 v700 = v956 ∧
      aluEval .sll v316 0x14 = v958 ∧
      aluEval .mul v747 v355 = v959 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n920, v920, d920, hv920, u920⟩ := s.aluG hc smm_at_b22 (off' := 0xB26) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv920
  obtain ⟨n921, v921, d921, hv921, u921⟩ := u920.aluG hc smm_at_b26 (off' := 0xB2A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv921
  obtain ⟨n922, d922, u922⟩ := u921.lwE hc smm_at_b2a (off' := 0xB2C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 136) (by decide)) (v := v610)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl88])
  obtain ⟨n923, v923, d923, hv923, u923⟩ := u922.aluG hc smm_at_b2c (off' := 0xB30) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv923
  obtain ⟨n924, d924, u924⟩ := u923.lwE hc smm_at_b30 (off' := 0xB32) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 152) (by decide)) (v := v593)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl98])
  obtain ⟨n925, v925, d925, hv925, u925⟩ := u924.aluG hc smm_at_b32 (off' := 0xB34) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv925
  obtain ⟨n926, d926, u926⟩ := u925.lwE hc smm_at_b34 (off' := 0xB36) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 148) (by decide)) (v := v595)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl94])
  obtain ⟨n927, v927, d927, hv927, u927⟩ := u926.aluG hc smm_at_b36 (off' := 0xB38) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv927
  obtain ⟨n928, v928, d928, hv928, u928⟩ := u927.aluG hc smm_at_b38 (off' := 0xB3C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv928
  obtain ⟨n929, d929, u929⟩ := u928.lwE hc smm_at_b3c (off' := 0xB40) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 292) (by decide)) (v := v141)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl124])
  obtain ⟨n930, v930, d930, hv930, u930⟩ := u929.aluG hc smm_at_b40 (off' := 0xB42) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv930
  obtain ⟨n931, d931, u931⟩ := u930.lwE hc smm_at_b42 (off' := 0xB44) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 140) (by decide)) (v := v620)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl8C])
  obtain ⟨n932, v932, d932, hv932, u932⟩ := u931.aluG hc smm_at_b44 (off' := 0xB46) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv932
  obtain ⟨n933, v933, d933, hv933, u933⟩ := u932.aluG hc smm_at_b46 (off' := 0xB48) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv933
  obtain ⟨n934, d934, u934⟩ := u933.lwE hc smm_at_b48 (off' := 0xB4A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 144) (by decide)) (v := v618)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl90])
  obtain ⟨n935, v935, d935, hv935, u935⟩ := u934.aluG hc smm_at_b4a (off' := 0xB4C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv935
  obtain ⟨n936, v936, d936, hv936, u936⟩ := u935.aluG hc smm_at_b4c (off' := 0xB50) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv936
  obtain ⟨n937, d937, u937⟩ := u936.lwE hc smm_at_b50 (off' := 0xB52) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 120) (by decide)) (v := v638)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl78])
  obtain ⟨n938, v938, d938, hv938, u938⟩ := u937.aluG hc smm_at_b52 (off' := 0xB54) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv938
  obtain ⟨n939, d939, u939⟩ := u938.lwE hc smm_at_b54 (off' := 0xB56) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 124) (by decide)) (v := v636)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl7C])
  obtain ⟨n940, v940, d940, hv940, u940⟩ := u939.aluG hc smm_at_b56 (off' := 0xB58) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv940
  obtain ⟨n941, v941, d941, hv941, u941⟩ := u940.aluG hc smm_at_b58 (off' := 0xB5C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv941
  obtain ⟨n942, v942, d942, hv942, u942⟩ := u941.aluG hc smm_at_b5c (off' := 0xB5E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv942
  obtain ⟨n943, d943, u943⟩ := u942.lwE hc smm_at_b5e (off' := 0xB60) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 228) (by decide)) (v := v322)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slE4])
  obtain ⟨n944, v944, d944, hv944, u944⟩ := u943.aluG hc smm_at_b60 (off' := 0xB64) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv944
  obtain ⟨n945, v945, d945, hv945, u945⟩ := u944.aluG hc smm_at_b64 (off' := 0xB66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv945
  obtain ⟨n946, v946, d946, hv946, u946⟩ := u945.aluG hc smm_at_b66 (off' := 0xB6A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv946
  obtain ⟨n947, v947, d947, hv947, u947⟩ := u946.aluG hc smm_at_b6a (off' := 0xB6E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv947
  obtain ⟨n948, d948, u948⟩ := u947.lwE hc smm_at_b6e (off' := 0xB70) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 244) (by decide)) (v := v314)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slF4])
  obtain ⟨n949, v949, d949, hv949, u949⟩ := u948.aluG hc smm_at_b70 (off' := 0xB74) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv949
  obtain ⟨n950, v950, d950, hv950, u950⟩ := u949.aluG hc smm_at_b74 (off' := 0xB78) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv950
  obtain ⟨n951, v951, d951, hv951, u951⟩ := u950.aluG hc smm_at_b78 (off' := 0xB7A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv951
  obtain ⟨n952, d952, u952⟩ := u951.lwE hc smm_at_b7a (off' := 0xB7C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 172) (by decide)) (v := v341)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slAC])
  obtain ⟨n953, v953, d953, hv953, u953⟩ := u952.aluImmG hc smm_at_b7c (off' := 0xB7E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv953
  obtain ⟨n954, v954, d954, hv954, u954⟩ := u953.aluG hc smm_at_b7e (off' := 0xB82) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv954
  obtain ⟨n955, v955, d955, hv955, u955⟩ := u954.aluG hc smm_at_b82 (off' := 0xB84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv955
  obtain ⟨n956, v956, d956, hv956, u956⟩ := u955.aluG hc smm_at_b84 (off' := 0xB88) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv956
  obtain ⟨n957, d957, u957⟩ := u956.lwE hc smm_at_b88 (off' := 0xB8A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 240) (by decide)) (v := v316)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slF0])
  obtain ⟨n958, v958, d958, hv958, u958⟩ := u957.aluImmG hc smm_at_b8a (off' := 0xB8C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv958
  obtain ⟨n959, v959, d959, hv959, u959⟩ := u958.aluG hc smm_at_b8c (off' := 0xB90) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv959
  have qo1 : reg n959 ra = v314 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n959 sp = F := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n959 (3 : Fin 32) = G3 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n959 (4 : Fin 32) = G4 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n959 (5 : Fin 32) = v747 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n959 (6 : Fin 32) = v950 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n959 (7 : Fin 32) = v898 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n959 (8 : Fin 32) = v891 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n959 (9 : Fin 32) = v959 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n959 a0 = v917 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n959 a1 = v955 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n959 a2 = v956 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n959 a3 = v954 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n959 a4 = v958 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n959 a5 = v938 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n959 a6 = v876 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n959 a7 = v278 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n959 (18 : Fin 32) = v662 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n959 (19 : Fin 32) = v827 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n959 (20 : Fin 32) = v946 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n959 (21 : Fin 32) = v470 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n959 (22 : Fin 32) = v293 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n959 (23 : Fin 32) = v355 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n959 (24 : Fin 32) = v274 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n959 (25 : Fin 32) = v280 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n959 (26 : Fin 32) = v523 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n959 (27 : Fin 32) = v700 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n959 (28 : Fin 32) = v830 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n959 (29 : Fin 32) = v272 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n959 (30 : Fin 32) = v322 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n959 (31 : Fin 32) = v843 := by rw [u959.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so9C : memLoad32 Mi (F + 0x9C) = v651 := by
    rw [sl9C]
  have soA4 : memLoad32 Mi (F + 0xA4) = v647 := by
    rw [slA4]
  have soA8 : memLoad32 Mi (F + 0xA8) = v624 := by
    rw [slA8]
  have soB8 : memLoad32 Mi (F + 0xB8) = v641 := by
    rw [slB8]
  have soC0 : memLoad32 Mi (F + 0xC0) = v653 := by
    rw [slC0]
  have soC8 : memLoad32 Mi (F + 0xC8) = v507 := by
    rw [slC8]
  have soD4 : memLoad32 Mi (F + 0xD4) = v455 := by
    rw [slD4]
  have soE0 : memLoad32 Mi (F + 0xE0) = v386 := by
    rw [slE0]
  have soE8 : memLoad32 Mi (F + 0xE8) = v384 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v382 := by
    rw [slEC]
  have soF8 : memLoad32 Mi (F + 0xF8) = outp := by
    rw [slF8]
  have so100 : memLoad32 Mi (F + 0x100) = v401 := by
    rw [sl100]
  have so10C : memLoad32 Mi (F + 0x10C) = v622 := by
    rw [sl10C]
  have so110 : memLoad32 Mi (F + 0x110) = v645 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v739 := by
    rw [sl118]
  have so11C : memLoad32 Mi (F + 0x11C) = v733 := by
    rw [sl11C]
  have so128 : memLoad32 Mi (F + 0x128) = v186 := by
    rw [sl128]
  have so12C : memLoad32 Mi (F + 0x12C) = v169 := by
    rw [sl12C]
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
  exact ⟨n959, Mi, v920, v921, v923, v925, v927, v928, v930, v932, v933, v935, v936, v938, v940, v941, v942, v944, v945, v946, v947, v949, v950, v951, v953, v954, v955, v956, v958, v959, (.cons d920 (.cons d921 (.cons d922 (.cons d923 (.cons d924 (.cons d925 (.cons d926 (.cons d927 (.cons d928 (.cons d929 (.cons d930 (.cons d931 (.cons d932 (.cons d933 (.cons d934 (.cons d935 (.cons d936 (.cons d937 (.cons d938 (.cons d939 (.cons d940 (.cons d941 (.cons d942 (.cons d943 (.cons d944 (.cons d945 (.cons d946 (.cons d947 (.cons d948 (.cons d949 (.cons d950 (.cons d951 (.cons d952 (.cons d953 (.cons d954 (.cons d955 (.cons d956 (.cons d957 (.cons d958 (.single d959)))))))))))))))))))))))))))))))))))))))), u959.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so9C, soA4, soA8, soB8, soC0, soC8, soD4, soE0, soE8, soEC, soF8, so100, so10C, so110, so118, so11C, so128, so12C, so130, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv920, hv921, hv923, hv925, hv927, hv928, hv930, hv932, hv933, hv935, hv936, hv938, hv940, hv941, hv942, hv944, hv945, hv946, hv947, hv949, hv950, hv951, hv953, hv954, hv955, hv956, hv958, hv959⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem smm_g30 {M0 Mi : Word → BitVec 8} {B F outp xp yp G3 G4 : Word} {n : Machine} {v169 v186 v226 v272 v274 v278 v280 v293 v314 v322 v355 v382 v384 v386 v401 v455 v470 v507 v523 v622 v624 v641 v645 v647 v651 v653 v662 v700 v733 v739 v747 v827 v830 v843 v876 v891 v898 v917 v938 v946 v950 v954 v955 v956 v958 v959 : Word}
    (s : St Mi B n 0xB90 (reg n)) (hc : CodeIn Mi B scalar29MontMulCode)
    (fr : ∀ x, Sep F 0x190 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hx : xp.toNat % 4 = 0) (hy : yp.toNat % 4 = 0)
    (sFC : Sep F 0x190 B scalar29MontMulCode.length) (sXF : Sep xp 36 F 0x190) (sYF : Sep yp 36 F 0x190)
    (q1 : reg n ra = v314)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v747)
    (q6 : reg n (6 : Fin 32) = v950)
    (q7 : reg n (7 : Fin 32) = v898)
    (q8 : reg n (8 : Fin 32) = v891)
    (q9 : reg n (9 : Fin 32) = v959)
    (q10 : reg n a0 = v917)
    (q11 : reg n a1 = v955)
    (q12 : reg n a2 = v956)
    (q13 : reg n a3 = v954)
    (q14 : reg n a4 = v958)
    (q15 : reg n a5 = v938)
    (q16 : reg n a6 = v876)
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
    (sl9C : memLoad32 Mi (F + 0x9C) = v651)
    (slA4 : memLoad32 Mi (F + 0xA4) = v647)
    (slA8 : memLoad32 Mi (F + 0xA8) = v624)
    (slB8 : memLoad32 Mi (F + 0xB8) = v641)
    (slC0 : memLoad32 Mi (F + 0xC0) = v653)
    (slC8 : memLoad32 Mi (F + 0xC8) = v507)
    (slD4 : memLoad32 Mi (F + 0xD4) = v455)
    (slE0 : memLoad32 Mi (F + 0xE0) = v386)
    (slE8 : memLoad32 Mi (F + 0xE8) = v384)
    (slEC : memLoad32 Mi (F + 0xEC) = v382)
    (slF8 : memLoad32 Mi (F + 0xF8) = outp)
    (sl100 : memLoad32 Mi (F + 0x100) = v401)
    (sl10C : memLoad32 Mi (F + 0x10C) = v622)
    (sl110 : memLoad32 Mi (F + 0x110) = v645)
    (sl118 : memLoad32 Mi (F + 0x118) = v739)
    (sl11C : memLoad32 Mi (F + 0x11C) = v733)
    (sl128 : memLoad32 Mi (F + 0x128) = v186)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v960 v961 v962 v963 v964 v965 v966 v967 v968 v969 v970 v971 v972 v973 v974 v975 v976 v977 v978 v979 v980 v981 v984 v987 v988 v989 v990 v991 v992 v995 v996 v997 v998 v999 : Word),
      Steps n n' ∧
      St M' B n' 0xC06 (reg n') ∧
      CodeIn M' B scalar29MontMulCode ∧
      (∀ x, Sep F 0x190 x 1 → M' x = M0 x) ∧
      reg n' ra = v314 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v747 ∧
      reg n' (6 : Fin 32) = v992 ∧
      reg n' (7 : Fin 32) = v998 ∧
      reg n' (8 : Fin 32) = v961 ∧
      reg n' (9 : Fin 32) = v997 ∧
      reg n' a0 = v996 ∧
      reg n' a1 = v186 ∧
      reg n' a2 = v999 ∧
      reg n' a3 = v995 ∧
      reg n' a4 = v987 ∧
      reg n' a5 = v990 ∧
      reg n' a6 = v386 ∧
      reg n' a7 = v278 ∧
      reg n' (18 : Fin 32) = v662 ∧
      reg n' (19 : Fin 32) = v827 ∧
      reg n' (20 : Fin 32) = v946 ∧
      reg n' (21 : Fin 32) = v470 ∧
      reg n' (22 : Fin 32) = v293 ∧
      reg n' (23 : Fin 32) = v355 ∧
      reg n' (24 : Fin 32) = v274 ∧
      reg n' (25 : Fin 32) = v280 ∧
      reg n' (26 : Fin 32) = v523 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v830 ∧
      reg n' (29 : Fin 32) = v272 ∧
      reg n' (30 : Fin 32) = v322 ∧
      reg n' (31 : Fin 32) = v843 ∧
      memLoad32 M' (F + 0xA4) = v647 ∧
      memLoad32 M' (F + 0xB8) = v641 ∧
      memLoad32 M' (F + 0xC8) = v507 ∧
      memLoad32 M' (F + 0xD4) = v455 ∧
      memLoad32 M' (F + 0xE8) = v384 ∧
      memLoad32 M' (F + 0xEC) = v382 ∧
      memLoad32 M' (F + 0xF8) = outp ∧
      memLoad32 M' (F + 0x100) = v401 ∧
      memLoad32 M' (F + 0x110) = v645 ∧
      memLoad32 M' (F + 0x118) = v739 ∧
      memLoad32 M' (F + 0x11C) = v733 ∧
      memLoad32 M' (F + 0x12C) = v169 ∧
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
      aluEval .sub v938 v314 = v960 ∧
      aluEval .mulhu v747 v355 = v961 ∧
      aluEval .add v958 v960 = v962 ∧
      aluEval .mul v843 v293 = v963 ∧
      aluEval .mulhu v843 v293 = v964 ∧
      aluEval .sltu v962 v960 = v965 ∧
      aluEval .add v955 v965 = v966 ∧
      aluEval .add v954 v962 = v967 ∧
      aluEval .add v966 v956 = v968 ∧
      aluEval .sltu v967 v962 = v969 ∧
      aluEval .add v968 v969 = v970 ∧
      aluEval .add v959 v967 = v971 ∧
      aluEval .add v970 v961 = v972 ∧
      aluEval .sltu v971 v967 = v973 ∧
      aluEval .add v972 v973 = v974 ∧
      aluEval .add v963 v971 = v975 ∧
      aluEval .add v974 v964 = v976 ∧
      aluEval .sltu v975 v971 = v977 ∧
      aluEval .sll v950 0x3 = v978 ∧
      aluEval .srl v946 0x1D = v979 ∧
      aluEval .or v978 v979 = v980 ∧
      aluEval .add v976 v977 = v981 ∧
      aluEval .add v624 v653 = v984 ∧
      aluEval .add v622 v651 = v987 ∧
      aluEval .srl v950 0x1D = v988 ∧
      aluEval .sltu v987 v651 = v989 ∧
      aluEval .add v988 v981 = v990 ∧
      aluEval .add v984 v989 = v991 ∧
      aluEval .add v975 v980 = v992 ∧
      aluEval .add v186 v386 = v995 ∧
      aluEval .sltu v992 v975 = v996 ∧
      aluEval .sltu v987 v995 = v997 ∧
      aluEval .add v990 v996 = v998 ∧
      aluEval .sub v991 v997 = v999 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n960, v960, d960, hv960, u960⟩ := s.aluG hc smm_at_b90 (off' := 0xB94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv960
  obtain ⟨n961, v961, d961, hv961, u961⟩ := u960.aluG hc smm_at_b94 (off' := 0xB98) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv961
  obtain ⟨n962, v962, d962, hv962, u962⟩ := u961.aluG hc smm_at_b98 (off' := 0xB9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv962
  obtain ⟨n963, v963, d963, hv963, u963⟩ := u962.aluG hc smm_at_b9a (off' := 0xB9E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv963
  obtain ⟨n964, v964, d964, hv964, u964⟩ := u963.aluG hc smm_at_b9e (off' := 0xBA2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv964
  obtain ⟨n965, v965, d965, hv965, u965⟩ := u964.aluG hc smm_at_ba2 (off' := 0xBA6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv965
  obtain ⟨n966, v966, d966, hv966, u966⟩ := u965.aluG hc smm_at_ba6 (off' := 0xBA8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv966
  obtain ⟨n967, v967, d967, hv967, u967⟩ := u966.aluG hc smm_at_ba8 (off' := 0xBAA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv967
  obtain ⟨n968, v968, d968, hv968, u968⟩ := u967.aluG hc smm_at_baa (off' := 0xBAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv968
  obtain ⟨n969, v969, d969, hv969, u969⟩ := u968.aluG hc smm_at_bac (off' := 0xBB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv969
  obtain ⟨n970, v970, d970, hv970, u970⟩ := u969.aluG hc smm_at_bb0 (off' := 0xBB2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv970
  obtain ⟨n971, v971, d971, hv971, u971⟩ := u970.aluG hc smm_at_bb2 (off' := 0xBB4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv971
  obtain ⟨n972, v972, d972, hv972, u972⟩ := u971.aluG hc smm_at_bb4 (off' := 0xBB6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv972
  obtain ⟨n973, v973, d973, hv973, u973⟩ := u972.aluG hc smm_at_bb6 (off' := 0xBBA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv973
  obtain ⟨n974, v974, d974, hv974, u974⟩ := u973.aluG hc smm_at_bba (off' := 0xBBC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv974
  obtain ⟨n975, v975, d975, hv975, u975⟩ := u974.aluG hc smm_at_bbc (off' := 0xBBE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv975
  obtain ⟨n976, v976, d976, hv976, u976⟩ := u975.aluG hc smm_at_bbe (off' := 0xBC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv976
  obtain ⟨n977, v977, d977, hv977, u977⟩ := u976.aluG hc smm_at_bc0 (off' := 0xBC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv977
  obtain ⟨n978, v978, d978, hv978, u978⟩ := u977.aluImmG hc smm_at_bc4 (off' := 0xBC8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv978
  obtain ⟨n979, v979, d979, hv979, u979⟩ := u978.aluImmG hc smm_at_bc8 (off' := 0xBCC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv979
  obtain ⟨n980, v980, d980, hv980, u980⟩ := u979.aluG hc smm_at_bcc (off' := 0xBCE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv980
  obtain ⟨n981, v981, d981, hv981, u981⟩ := u980.aluG hc smm_at_bce (off' := 0xBD0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv981
  obtain ⟨n982, d982, u982⟩ := u981.lwE hc smm_at_bd0 (off' := 0xBD2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 168) (by decide)) (v := v624)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slA8])
  obtain ⟨n983, d983, u983⟩ := u982.lwE hc smm_at_bd2 (off' := 0xBD4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 192) (by decide)) (v := v653)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slC0])
  obtain ⟨n984, v984, d984, hv984, u984⟩ := u983.aluG hc smm_at_bd4 (off' := 0xBD6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv984
  obtain ⟨n985, d985, u985⟩ := u984.lwE hc smm_at_bd6 (off' := 0xBDA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 268) (by decide)) (v := v622)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl10C])
  obtain ⟨n986, d986, u986⟩ := u985.lwE hc smm_at_bda (off' := 0xBDC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 156) (by decide)) (v := v651)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl9C])
  obtain ⟨n987, v987, d987, hv987, u987⟩ := u986.aluG hc smm_at_bdc (off' := 0xBDE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv987
  obtain ⟨n988, v988, d988, hv988, u988⟩ := u987.aluImmG hc smm_at_bde (off' := 0xBE2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv988
  obtain ⟨n989, v989, d989, hv989, u989⟩ := u988.aluG hc smm_at_be2 (off' := 0xBE6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv989
  obtain ⟨n990, v990, d990, hv990, u990⟩ := u989.aluG hc smm_at_be6 (off' := 0xBE8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv990
  obtain ⟨n991, v991, d991, hv991, u991⟩ := u990.aluG hc smm_at_be8 (off' := 0xBEA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv991
  obtain ⟨n992, v992, d992, hv992, u992⟩ := u991.aluG hc smm_at_bea (off' := 0xBEE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv992
  obtain ⟨n993, d993, u993⟩ := u992.lwE hc smm_at_bee (off' := 0xBF2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 296) (by decide)) (v := v186)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl128])
  obtain ⟨n994, d994, u994⟩ := u993.lwE hc smm_at_bf2 (off' := 0xBF4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 224) (by decide)) (v := v386)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slE0])
  obtain ⟨n995, v995, d995, hv995, u995⟩ := u994.aluG hc smm_at_bf4 (off' := 0xBF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv995
  obtain ⟨n996, v996, d996, hv996, u996⟩ := u995.aluG hc smm_at_bf8 (off' := 0xBFC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv996
  obtain ⟨n997, v997, d997, hv997, u997⟩ := u996.aluG hc smm_at_bfc (off' := 0xC00) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv997
  obtain ⟨n998, v998, d998, hv998, u998⟩ := u997.aluG hc smm_at_c00 (off' := 0xC04) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv998
  obtain ⟨n999, v999, d999, hv999, u999⟩ := u998.aluG hc smm_at_c04 (off' := 0xC06) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv999
  have qo1 : reg n999 ra = v314 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n999 sp = F := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n999 (3 : Fin 32) = G3 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n999 (4 : Fin 32) = G4 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n999 (5 : Fin 32) = v747 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n999 (6 : Fin 32) = v992 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n999 (7 : Fin 32) = v998 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n999 (8 : Fin 32) = v961 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n999 (9 : Fin 32) = v997 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n999 a0 = v996 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n999 a1 = v186 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n999 a2 = v999 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n999 a3 = v995 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n999 a4 = v987 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n999 a5 = v990 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n999 a6 = v386 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n999 a7 = v278 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n999 (18 : Fin 32) = v662 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n999 (19 : Fin 32) = v827 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n999 (20 : Fin 32) = v946 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n999 (21 : Fin 32) = v470 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n999 (22 : Fin 32) = v293 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n999 (23 : Fin 32) = v355 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n999 (24 : Fin 32) = v274 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n999 (25 : Fin 32) = v280 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n999 (26 : Fin 32) = v523 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n999 (27 : Fin 32) = v700 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n999 (28 : Fin 32) = v830 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n999 (29 : Fin 32) = v272 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n999 (30 : Fin 32) = v322 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n999 (31 : Fin 32) = v843 := by rw [u999.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soA4 : memLoad32 Mi (F + 0xA4) = v647 := by
    rw [slA4]
  have soB8 : memLoad32 Mi (F + 0xB8) = v641 := by
    rw [slB8]
  have soC8 : memLoad32 Mi (F + 0xC8) = v507 := by
    rw [slC8]
  have soD4 : memLoad32 Mi (F + 0xD4) = v455 := by
    rw [slD4]
  have soE8 : memLoad32 Mi (F + 0xE8) = v384 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v382 := by
    rw [slEC]
  have soF8 : memLoad32 Mi (F + 0xF8) = outp := by
    rw [slF8]
  have so100 : memLoad32 Mi (F + 0x100) = v401 := by
    rw [sl100]
  have so110 : memLoad32 Mi (F + 0x110) = v645 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v739 := by
    rw [sl118]
  have so11C : memLoad32 Mi (F + 0x11C) = v733 := by
    rw [sl11C]
  have so12C : memLoad32 Mi (F + 0x12C) = v169 := by
    rw [sl12C]
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
  exact ⟨n999, Mi, v960, v961, v962, v963, v964, v965, v966, v967, v968, v969, v970, v971, v972, v973, v974, v975, v976, v977, v978, v979, v980, v981, v984, v987, v988, v989, v990, v991, v992, v995, v996, v997, v998, v999, (.cons d960 (.cons d961 (.cons d962 (.cons d963 (.cons d964 (.cons d965 (.cons d966 (.cons d967 (.cons d968 (.cons d969 (.cons d970 (.cons d971 (.cons d972 (.cons d973 (.cons d974 (.cons d975 (.cons d976 (.cons d977 (.cons d978 (.cons d979 (.cons d980 (.cons d981 (.cons d982 (.cons d983 (.cons d984 (.cons d985 (.cons d986 (.cons d987 (.cons d988 (.cons d989 (.cons d990 (.cons d991 (.cons d992 (.cons d993 (.cons d994 (.cons d995 (.cons d996 (.cons d997 (.cons d998 (.single d999)))))))))))))))))))))))))))))))))))))))), u999.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soA4, soB8, soC8, soD4, soE8, soEC, soF8, so100, so110, so118, so11C, so12C, so130, so15C, so160, so164, so168, so16C, so170, so174, so178, so17C, so180, so184, so188, so18C, hv960, hv961, hv962, hv963, hv964, hv965, hv966, hv967, hv968, hv969, hv970, hv971, hv972, hv973, hv974, hv975, hv976, hv977, hv978, hv979, hv980, hv981, hv984, hv987, hv988, hv989, hv990, hv991, hv992, hv995, hv996, hv997, hv998, hv999⟩

end C3.RV32
