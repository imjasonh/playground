import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, segments 16 to 18

Each theorem steps 40 instructions. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g16 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v7 v17 v465 v488 v494 v500 v506 v509 v510 v516 v522 v525 v541 v544 v572 v591 v603 v608 v615 v618 v623 v628 v629 v630 v632 v633 v634 v635 v636 v638 v639 : Word}
    (s : St Mi B n 0x85A (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v572)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v603)
    (q6 : reg n (6 : Fin 32) = v525)
    (q7 : reg n (7 : Fin 32) = v506)
    (q8 : reg n (8 : Fin 32) = v635)
    (q9 : reg n (9 : Fin 32) = v629)
    (q10 : reg n a0 = v633)
    (q11 : reg n a1 = v618)
    (q12 : reg n a2 = v632)
    (q13 : reg n a3 = v638)
    (q14 : reg n a4 = v623)
    (q15 : reg n a5 = v636)
    (q16 : reg n a6 = v541)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v628)
    (q19 : reg n (19 : Fin 32) = v465)
    (q20 : reg n (20 : Fin 32) = v488)
    (q21 : reg n (21 : Fin 32) = v516)
    (q22 : reg n (22 : Fin 32) = v522)
    (q23 : reg n (23 : Fin 32) = v510)
    (q24 : reg n (24 : Fin 32) = v509)
    (q25 : reg n (25 : Fin 32) = v630)
    (q26 : reg n (26 : Fin 32) = v634)
    (q27 : reg n (27 : Fin 32) = v639)
    (q28 : reg n (28 : Fin 32) = v500)
    (q29 : reg n (29 : Fin 32) = v494)
    (q30 : reg n (30 : Fin 32) = v615)
    (q31 : reg n (31 : Fin 32) = v608)
    (sl14 : memLoad32 Mi (F + 0x14) = v636)
    (sl18 : memLoad32 Mi (F + 0x18) = v591)
    (sl1C : memLoad32 Mi (F + 0x1C) = v544)
    (sl20 : memLoad32 Mi (F + 0x20) = v7)
    (sl24 : memLoad32 Mi (F + 0x24) = v0)
    (sl28 : memLoad32 Mi (F + 0x28) = outp)
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (sl50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50))
    (sl54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54))
    (sl58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58))
    (sl5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C))
    (sl60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60))
    (sl64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64))
    (sl68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68))
    (sl6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C))
    (sl70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70))
    (sl74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74))
    (sl78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78))
    (sl7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C))
    (sl80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80))
    (sl84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84))
    (sl88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88))
    (sl8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C))
    (sl90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90))
    (sl94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94))
    (sl98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98))
    (sl9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v640 v641 v642 v643 v644 v645 v646 v647 v648 v649 v650 v651 v652 v653 v654 v655 v656 v657 v658 v659 v660 v661 v662 v663 v664 v665 v666 v667 v668 v669 v670 v671 v672 v674 v675 v676 v677 v678 v679 : Word),
      Steps n n' ∧
      St M' B n' 0x8D6 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v640 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v603 ∧
      reg n' (6 : Fin 32) = v525 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v667 ∧
      reg n' (9 : Fin 32) = v674 ∧
      reg n' a0 = v668 ∧
      reg n' a1 = v662 ∧
      reg n' a2 = v669 ∧
      reg n' a3 = v677 ∧
      reg n' a4 = v666 ∧
      reg n' a5 = v679 ∧
      reg n' a6 = v541 ∧
      reg n' a7 = v671 ∧
      reg n' (18 : Fin 32) = v672 ∧
      reg n' (19 : Fin 32) = v465 ∧
      reg n' (20 : Fin 32) = v488 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v522 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v676 ∧
      reg n' (26 : Fin 32) = v665 ∧
      reg n' (27 : Fin 32) = v651 ∧
      reg n' (28 : Fin 32) = v500 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v615 ∧
      reg n' (31 : Fin 32) = v670 ∧
      memLoad32 M' (F + 0x10) = v672 ∧
      memLoad32 M' (F + 0x14) = v636 ∧
      memLoad32 M' (F + 0x18) = v591 ∧
      memLoad32 M' (F + 0x1C) = v544 ∧
      memLoad32 M' (F + 0x20) = v7 ∧
      memLoad32 M' (F + 0x24) = v0 ∧
      memLoad32 M' (F + 0x28) = outp ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (F + 0x50) = memLoad32 M0 (F + 0x50) ∧
      memLoad32 M' (F + 0x54) = memLoad32 M0 (F + 0x54) ∧
      memLoad32 M' (F + 0x58) = memLoad32 M0 (F + 0x58) ∧
      memLoad32 M' (F + 0x5C) = memLoad32 M0 (F + 0x5C) ∧
      memLoad32 M' (F + 0x60) = memLoad32 M0 (F + 0x60) ∧
      memLoad32 M' (F + 0x64) = memLoad32 M0 (F + 0x64) ∧
      memLoad32 M' (F + 0x68) = memLoad32 M0 (F + 0x68) ∧
      memLoad32 M' (F + 0x6C) = memLoad32 M0 (F + 0x6C) ∧
      memLoad32 M' (F + 0x70) = memLoad32 M0 (F + 0x70) ∧
      memLoad32 M' (F + 0x74) = memLoad32 M0 (F + 0x74) ∧
      memLoad32 M' (F + 0x78) = memLoad32 M0 (F + 0x78) ∧
      memLoad32 M' (F + 0x7C) = memLoad32 M0 (F + 0x7C) ∧
      memLoad32 M' (F + 0x80) = memLoad32 M0 (F + 0x80) ∧
      memLoad32 M' (F + 0x84) = memLoad32 M0 (F + 0x84) ∧
      memLoad32 M' (F + 0x88) = memLoad32 M0 (F + 0x88) ∧
      memLoad32 M' (F + 0x8C) = memLoad32 M0 (F + 0x8C) ∧
      memLoad32 M' (F + 0x90) = memLoad32 M0 (F + 0x90) ∧
      memLoad32 M' (F + 0x94) = memLoad32 M0 (F + 0x94) ∧
      memLoad32 M' (F + 0x98) = memLoad32 M0 (F + 0x98) ∧
      memLoad32 M' (F + 0x9C) = memLoad32 M0 (F + 0x9C) ∧
      aluEval .add v632 v635 = v640 ∧
      aluEval .add v638 v628 = v641 ∧
      aluEval .add v630 v608 = v642 ∧
      aluEval .mulhu v488 v516 = v643 ∧
      aluEval .sltu v642 v608 = v644 ∧
      aluEval .mul v488 v522 = v645 ∧
      aluEval .add v644 v634 = v646 ∧
      aluEval .add v641 v642 = v647 ∧
      aluEval .sltu v647 v642 = v648 ∧
      aluEval .mulhu v488 v522 = v649 ∧
      aluEval .add v648 v646 = v650 ∧
      aluEval .add v639 v618 = v651 ∧
      aluEval .sltu v651 v618 = v652 ∧
      aluEval .add v650 v651 = v653 ∧
      aluEval .add v652 v643 = v654 ∧
      aluEval .sltu v653 v651 = v655 ∧
      aluEval .add v654 v655 = v656 ∧
      aluEval .add v645 v623 = v657 ∧
      aluEval .sltu v657 v623 = v658 ∧
      aluEval .mulhu v488 v17 = v659 ∧
      aluEval .add v649 v658 = v660 ∧
      aluEval .mul v494 v509 = v661 ∧
      aluEval .add v656 v657 = v662 ∧
      aluEval .mul v494 v510 = v663 ∧
      aluEval .sltu v662 v657 = v664 ∧
      aluEval .mulhu v494 v509 = v665 ∧
      aluEval .sub v633 v488 = v666 ∧
      aluEval .mulhu v494 v510 = v667 ∧
      aluEval .sltu v666 v633 = v668 ∧
      aluEval .mul v494 v516 = v669 ∧
      aluEval .add v660 v664 = v670 ∧
      aluEval .add v659 v668 = v671 ∧
      aluEval .add v661 v647 = v672 ∧
      aluEval .mulhu v494 v516 = v674 ∧
      aluEval .sltu v672 v647 = v675 ∧
      aluEval .add v663 v653 = v676 ∧
      aluEval .add v675 v665 = v677 ∧
      aluEval .sltu v676 v653 = v678 ∧
      aluEval .add v678 v667 = v679 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n640, v640, d640, hv640, u640⟩ := s.aluG hc psm_at_85a (off' := 0x85E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv640
  obtain ⟨n641, v641, d641, hv641, u641⟩ := u640.aluG hc psm_at_85e (off' := 0x860) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv641
  obtain ⟨n642, v642, d642, hv642, u642⟩ := u641.aluG hc psm_at_860 (off' := 0x862) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv642
  obtain ⟨n643, v643, d643, hv643, u643⟩ := u642.aluG hc psm_at_862 (off' := 0x866) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv643
  obtain ⟨n644, v644, d644, hv644, u644⟩ := u643.aluG hc psm_at_866 (off' := 0x86A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv644
  obtain ⟨n645, v645, d645, hv645, u645⟩ := u644.aluG hc psm_at_86a (off' := 0x86E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv645
  obtain ⟨n646, v646, d646, hv646, u646⟩ := u645.aluG hc psm_at_86e (off' := 0x870) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv646
  obtain ⟨n647, v647, d647, hv647, u647⟩ := u646.aluG hc psm_at_870 (off' := 0x872) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv647
  obtain ⟨n648, v648, d648, hv648, u648⟩ := u647.aluG hc psm_at_872 (off' := 0x876) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv648
  obtain ⟨n649, v649, d649, hv649, u649⟩ := u648.aluG hc psm_at_876 (off' := 0x87A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv649
  obtain ⟨n650, v650, d650, hv650, u650⟩ := u649.aluG hc psm_at_87a (off' := 0x87C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv650
  obtain ⟨n651, v651, d651, hv651, u651⟩ := u650.aluG hc psm_at_87c (off' := 0x87E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv651
  obtain ⟨n652, v652, d652, hv652, u652⟩ := u651.aluG hc psm_at_87e (off' := 0x882) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv652
  obtain ⟨n653, v653, d653, hv653, u653⟩ := u652.aluG hc psm_at_882 (off' := 0x884) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv653
  obtain ⟨n654, v654, d654, hv654, u654⟩ := u653.aluG hc psm_at_884 (off' := 0x886) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv654
  obtain ⟨n655, v655, d655, hv655, u655⟩ := u654.aluG hc psm_at_886 (off' := 0x88A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv655
  obtain ⟨n656, v656, d656, hv656, u656⟩ := u655.aluG hc psm_at_88a (off' := 0x88C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv656
  obtain ⟨n657, v657, d657, hv657, u657⟩ := u656.aluG hc psm_at_88c (off' := 0x88E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv657
  obtain ⟨n658, v658, d658, hv658, u658⟩ := u657.aluG hc psm_at_88e (off' := 0x892) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv658
  obtain ⟨n659, v659, d659, hv659, u659⟩ := u658.aluG hc psm_at_892 (off' := 0x896) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv659
  obtain ⟨n660, v660, d660, hv660, u660⟩ := u659.aluG hc psm_at_896 (off' := 0x89A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv660
  obtain ⟨n661, v661, d661, hv661, u661⟩ := u660.aluG hc psm_at_89a (off' := 0x89E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv661
  obtain ⟨n662, v662, d662, hv662, u662⟩ := u661.aluG hc psm_at_89e (off' := 0x8A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv662
  obtain ⟨n663, v663, d663, hv663, u663⟩ := u662.aluG hc psm_at_8a0 (off' := 0x8A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv663
  obtain ⟨n664, v664, d664, hv664, u664⟩ := u663.aluG hc psm_at_8a4 (off' := 0x8A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv664
  obtain ⟨n665, v665, d665, hv665, u665⟩ := u664.aluG hc psm_at_8a8 (off' := 0x8AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv665
  obtain ⟨n666, v666, d666, hv666, u666⟩ := u665.aluG hc psm_at_8ac (off' := 0x8B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv666
  obtain ⟨n667, v667, d667, hv667, u667⟩ := u666.aluG hc psm_at_8b0 (off' := 0x8B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv667
  obtain ⟨n668, v668, d668, hv668, u668⟩ := u667.aluG hc psm_at_8b4 (off' := 0x8B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv668
  obtain ⟨n669, v669, d669, hv669, u669⟩ := u668.aluG hc psm_at_8b8 (off' := 0x8BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv669
  obtain ⟨n670, v670, d670, hv670, u670⟩ := u669.aluG hc psm_at_8bc (off' := 0x8BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv670
  obtain ⟨n671, v671, d671, hv671, u671⟩ := u670.aluG hc psm_at_8be (off' := 0x8C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv671
  obtain ⟨n672, v672, d672, hv672, u672⟩ := u671.aluG hc psm_at_8c0 (off' := 0x8C2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv672
  obtain ⟨n673, d673, u673⟩ := u672.swG hc psm_at_8c2 (off' := 0x8C4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 16) (by decide)) (a := F + 0x10) (v := v672)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M673, hM673⟩ : ∃ M', memStore32 Mi (F + 0x10) v672 = M' := ⟨_, rfl⟩
  rw [hM673] at u673
  have hc673 : CodeIn M673 B p256ScalarMulCode := by rw [← hM673]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr673 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M673 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM673, memStore32_get_sep (frm_sep' hx1 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n674, v674, d674, hv674, u674⟩ := u673.aluG hc673 psm_at_8c4 (off' := 0x8C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv674
  obtain ⟨n675, v675, d675, hv675, u675⟩ := u674.aluG hc673 psm_at_8c8 (off' := 0x8CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv675
  obtain ⟨n676, v676, d676, hv676, u676⟩ := u675.aluG hc673 psm_at_8cc (off' := 0x8CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv676
  obtain ⟨n677, v677, d677, hv677, u677⟩ := u676.aluG hc673 psm_at_8ce (off' := 0x8D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv677
  obtain ⟨n678, v678, d678, hv678, u678⟩ := u677.aluG hc673 psm_at_8d0 (off' := 0x8D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv678
  obtain ⟨n679, v679, d679, hv679, u679⟩ := u678.aluG hc673 psm_at_8d4 (off' := 0x8D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv679
  have qo1 : reg n679 ra = v640 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n679 sp = F := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n679 (3 : Fin 32) = G3 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n679 (4 : Fin 32) = G4 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n679 (5 : Fin 32) = v603 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n679 (6 : Fin 32) = v525 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n679 (7 : Fin 32) = v506 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n679 (8 : Fin 32) = v667 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n679 (9 : Fin 32) = v674 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n679 a0 = v668 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n679 a1 = v662 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n679 a2 = v669 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n679 a3 = v677 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n679 a4 = v666 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n679 a5 = v679 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n679 a6 = v541 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n679 a7 = v671 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n679 (18 : Fin 32) = v672 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n679 (19 : Fin 32) = v465 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n679 (20 : Fin 32) = v488 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n679 (21 : Fin 32) = v516 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n679 (22 : Fin 32) = v522 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n679 (23 : Fin 32) = v510 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n679 (24 : Fin 32) = v509 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n679 (25 : Fin 32) = v676 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n679 (26 : Fin 32) = v665 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n679 (27 : Fin 32) = v651 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n679 (28 : Fin 32) = v500 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n679 (29 : Fin 32) = v494 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n679 (30 : Fin 32) = v615 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n679 (31 : Fin 32) = v670 := by rw [u679.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so10 : memLoad32 M673 (F + 0x10) = v672 := by
    rw [← hM673, memLoad32_store32_same]
  have so14 : memLoad32 M673 (F + 0x14) = v636 := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x14) 4 from sep_offsets F (c := 16) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), sl14]
  have so18 : memLoad32 M673 (F + 0x18) = v591 := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x18) 4 from sep_offsets F (c := 16) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), sl18]
  have so1C : memLoad32 M673 (F + 0x1C) = v544 := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x1C) 4 from sep_offsets F (c := 16) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), sl1C]
  have so20 : memLoad32 M673 (F + 0x20) = v7 := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x20) 4 from sep_offsets F (c := 16) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), sl20]
  have so24 : memLoad32 M673 (F + 0x24) = v0 := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x24) 4 from sep_offsets F (c := 16) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), sl24]
  have so28 : memLoad32 M673 (F + 0x28) = outp := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x28) 4 from sep_offsets F (c := 16) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M673 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x2C) 4 from sep_offsets F (c := 16) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M673 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x30) 4 from sep_offsets F (c := 16) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M673 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x34) 4 from sep_offsets F (c := 16) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M673 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x38) 4 from sep_offsets F (c := 16) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M673 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x3C) 4 from sep_offsets F (c := 16) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M673 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x40) 4 from sep_offsets F (c := 16) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M673 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x44) 4 from sep_offsets F (c := 16) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M673 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x48) 4 from sep_offsets F (c := 16) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M673 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x4C) 4 from sep_offsets F (c := 16) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 M673 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x50) 4 from sep_offsets F (c := 16) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 M673 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x54) 4 from sep_offsets F (c := 16) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 M673 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x58) 4 from sep_offsets F (c := 16) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 M673 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x5C) 4 from sep_offsets F (c := 16) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 M673 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x60) 4 from sep_offsets F (c := 16) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 M673 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x64) 4 from sep_offsets F (c := 16) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 M673 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x68) 4 from sep_offsets F (c := 16) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 M673 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x6C) 4 from sep_offsets F (c := 16) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 M673 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x70) 4 from sep_offsets F (c := 16) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 M673 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x74) 4 from sep_offsets F (c := 16) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 M673 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x78) 4 from sep_offsets F (c := 16) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 M673 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x7C) 4 from sep_offsets F (c := 16) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 M673 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x80) 4 from sep_offsets F (c := 16) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 M673 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x84) 4 from sep_offsets F (c := 16) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 M673 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x88) 4 from sep_offsets F (c := 16) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 M673 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x8C) 4 from sep_offsets F (c := 16) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 M673 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x90) 4 from sep_offsets F (c := 16) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 M673 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x94) 4 from sep_offsets F (c := 16) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 M673 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x98) 4 from sep_offsets F (c := 16) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 M673 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM673, memLoad32_store32_sep (show Sep (F + 0x10) 4 (F + 0x9C) 4 from sep_offsets F (c := 16) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  exact ⟨n679, M673, v640, v641, v642, v643, v644, v645, v646, v647, v648, v649, v650, v651, v652, v653, v654, v655, v656, v657, v658, v659, v660, v661, v662, v663, v664, v665, v666, v667, v668, v669, v670, v671, v672, v674, v675, v676, v677, v678, v679, (.cons d640 (.cons d641 (.cons d642 (.cons d643 (.cons d644 (.cons d645 (.cons d646 (.cons d647 (.cons d648 (.cons d649 (.cons d650 (.cons d651 (.cons d652 (.cons d653 (.cons d654 (.cons d655 (.cons d656 (.cons d657 (.cons d658 (.cons d659 (.cons d660 (.cons d661 (.cons d662 (.cons d663 (.cons d664 (.cons d665 (.cons d666 (.cons d667 (.cons d668 (.cons d669 (.cons d670 (.cons d671 (.cons d672 (.cons d673 (.cons d674 (.cons d675 (.cons d676 (.cons d677 (.cons d678 (.single d679)))))))))))))))))))))))))))))))))))))))), u679.self, hc673, fr673, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so10, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv640, hv641, hv642, hv643, hv644, hv645, hv646, hv647, hv648, hv649, hv650, hv651, hv652, hv653, hv654, hv655, hv656, hv657, hv658, hv659, hv660, hv661, hv662, hv663, hv664, hv665, hv666, hv667, hv668, hv669, hv670, hv671, hv672, hv674, hv675, hv676, hv677, hv678, hv679⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g17 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v7 v465 v488 v494 v500 v506 v509 v510 v516 v522 v525 v541 v544 v591 v603 v615 v636 v640 v651 v662 v665 v666 v667 v668 v669 v670 v671 v672 v674 v676 v677 v679 : Word}
    (s : St Mi B n 0x8D6 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v640)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v603)
    (q6 : reg n (6 : Fin 32) = v525)
    (q7 : reg n (7 : Fin 32) = v506)
    (q8 : reg n (8 : Fin 32) = v667)
    (q9 : reg n (9 : Fin 32) = v674)
    (q10 : reg n a0 = v668)
    (q11 : reg n a1 = v662)
    (q12 : reg n a2 = v669)
    (q13 : reg n a3 = v677)
    (q14 : reg n a4 = v666)
    (q15 : reg n a5 = v679)
    (q16 : reg n a6 = v541)
    (q17 : reg n a7 = v671)
    (q18 : reg n (18 : Fin 32) = v672)
    (q19 : reg n (19 : Fin 32) = v465)
    (q20 : reg n (20 : Fin 32) = v488)
    (q21 : reg n (21 : Fin 32) = v516)
    (q22 : reg n (22 : Fin 32) = v522)
    (q23 : reg n (23 : Fin 32) = v510)
    (q24 : reg n (24 : Fin 32) = v509)
    (q25 : reg n (25 : Fin 32) = v676)
    (q26 : reg n (26 : Fin 32) = v665)
    (q27 : reg n (27 : Fin 32) = v651)
    (q28 : reg n (28 : Fin 32) = v500)
    (q29 : reg n (29 : Fin 32) = v494)
    (q30 : reg n (30 : Fin 32) = v615)
    (q31 : reg n (31 : Fin 32) = v670)
    (sl10 : memLoad32 Mi (F + 0x10) = v672)
    (sl14 : memLoad32 Mi (F + 0x14) = v636)
    (sl18 : memLoad32 Mi (F + 0x18) = v591)
    (sl1C : memLoad32 Mi (F + 0x1C) = v544)
    (sl20 : memLoad32 Mi (F + 0x20) = v7)
    (sl24 : memLoad32 Mi (F + 0x24) = v0)
    (sl28 : memLoad32 Mi (F + 0x28) = outp)
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (sl50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50))
    (sl54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54))
    (sl58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58))
    (sl5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C))
    (sl60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60))
    (sl64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64))
    (sl68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68))
    (sl6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C))
    (sl70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70))
    (sl74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74))
    (sl78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78))
    (sl7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C))
    (sl80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80))
    (sl84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84))
    (sl88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88))
    (sl8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C))
    (sl90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90))
    (sl94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94))
    (sl98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98))
    (sl9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v680 v681 v682 v683 v684 v685 v686 v687 v688 v689 v690 v691 v692 v693 v694 v695 v696 v697 v698 v699 v700 v701 v702 v703 v704 v706 v707 v708 v709 v710 v711 v712 v713 v714 v715 v716 v717 v718 v719 : Word),
      Steps n n' ∧
      St M' B n' 0x94E (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v640 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v603 ∧
      reg n' (6 : Fin 32) = v525 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v709 ∧
      reg n' (9 : Fin 32) = v700 ∧
      reg n' a0 = v703 ∧
      reg n' a1 = v717 ∧
      reg n' a2 = v715 ∧
      reg n' a3 = v713 ∧
      reg n' a4 = v718 ∧
      reg n' a5 = v714 ∧
      reg n' a6 = v541 ∧
      reg n' a7 = v693 ∧
      reg n' (18 : Fin 32) = v719 ∧
      reg n' (19 : Fin 32) = v465 ∧
      reg n' (20 : Fin 32) = v488 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v522 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v708 ∧
      reg n' (26 : Fin 32) = v665 ∧
      reg n' (27 : Fin 32) = v651 ∧
      reg n' (28 : Fin 32) = v500 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v615 ∧
      reg n' (31 : Fin 32) = v706 ∧
      memLoad32 M' (F + 0xC) = v704 ∧
      memLoad32 M' (F + 0x10) = v672 ∧
      memLoad32 M' (F + 0x14) = v636 ∧
      memLoad32 M' (F + 0x18) = v591 ∧
      memLoad32 M' (F + 0x1C) = v544 ∧
      memLoad32 M' (F + 0x20) = v7 ∧
      memLoad32 M' (F + 0x24) = v0 ∧
      memLoad32 M' (F + 0x28) = outp ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (F + 0x50) = memLoad32 M0 (F + 0x50) ∧
      memLoad32 M' (F + 0x54) = memLoad32 M0 (F + 0x54) ∧
      memLoad32 M' (F + 0x58) = memLoad32 M0 (F + 0x58) ∧
      memLoad32 M' (F + 0x5C) = memLoad32 M0 (F + 0x5C) ∧
      memLoad32 M' (F + 0x60) = memLoad32 M0 (F + 0x60) ∧
      memLoad32 M' (F + 0x64) = memLoad32 M0 (F + 0x64) ∧
      memLoad32 M' (F + 0x68) = memLoad32 M0 (F + 0x68) ∧
      memLoad32 M' (F + 0x6C) = memLoad32 M0 (F + 0x6C) ∧
      memLoad32 M' (F + 0x70) = memLoad32 M0 (F + 0x70) ∧
      memLoad32 M' (F + 0x74) = memLoad32 M0 (F + 0x74) ∧
      memLoad32 M' (F + 0x78) = memLoad32 M0 (F + 0x78) ∧
      memLoad32 M' (F + 0x7C) = memLoad32 M0 (F + 0x7C) ∧
      memLoad32 M' (F + 0x80) = memLoad32 M0 (F + 0x80) ∧
      memLoad32 M' (F + 0x84) = memLoad32 M0 (F + 0x84) ∧
      memLoad32 M' (F + 0x88) = memLoad32 M0 (F + 0x88) ∧
      memLoad32 M' (F + 0x8C) = memLoad32 M0 (F + 0x8C) ∧
      memLoad32 M' (F + 0x90) = memLoad32 M0 (F + 0x90) ∧
      memLoad32 M' (F + 0x94) = memLoad32 M0 (F + 0x94) ∧
      memLoad32 M' (F + 0x98) = memLoad32 M0 (F + 0x98) ∧
      memLoad32 M' (F + 0x9C) = memLoad32 M0 (F + 0x9C) ∧
      aluEval .add v677 v676 = v680 ∧
      aluEval .sltu v680 v676 = v681 ∧
      aluEval .add v669 v662 = v682 ∧
      aluEval .sltu v682 v662 = v683 ∧
      aluEval .mul v494 v522 = v684 ∧
      aluEval .add v679 v681 = v685 ∧
      aluEval .add v683 v674 = v686 ∧
      aluEval .add v670 v666 = v687 ∧
      aluEval .mulhu v494 v522 = v688 ∧
      aluEval .sltu v687 v666 = v689 ∧
      aluEval .add v685 v682 = v690 ∧
      aluEval .sltu v690 v682 = v691 ∧
      aluEval .mul v500 v509 = v692 ∧
      aluEval .add v671 v689 = v693 ∧
      aluEval .add v686 v691 = v694 ∧
      aluEval .add v684 v687 = v695 ∧
      aluEval .mul v500 v510 = v696 ∧
      aluEval .sltu v695 v687 = v697 ∧
      aluEval .mulhu v500 v509 = v698 ∧
      aluEval .add v688 v697 = v699 ∧
      aluEval .mulhu v500 v510 = v700 ∧
      aluEval .add v694 v695 = v701 ∧
      aluEval .mul v500 v516 = v702 ∧
      aluEval .sltu v701 v695 = v703 ∧
      aluEval .add v692 v680 = v704 ∧
      aluEval .add v699 v703 = v706 ∧
      aluEval .sltu v704 v680 = v707 ∧
      aluEval .add v696 v690 = v708 ∧
      aluEval .mulhu v500 v516 = v709 ∧
      aluEval .add v707 v698 = v710 ∧
      aluEval .sltu v708 v690 = v711 ∧
      aluEval .add v711 v700 = v712 ∧
      aluEval .add v710 v708 = v713 ∧
      aluEval .sltu v713 v708 = v714 ∧
      aluEval .add v702 v701 = v715 ∧
      aluEval .add v712 v714 = v716 ∧
      aluEval .sltu v715 v701 = v717 ∧
      aluEval .add v716 v715 = v718 ∧
      aluEval .mul v506 v509 = v719 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n680, v680, d680, hv680, u680⟩ := s.aluG hc psm_at_8d6 (off' := 0x8D8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv680
  obtain ⟨n681, v681, d681, hv681, u681⟩ := u680.aluG hc psm_at_8d8 (off' := 0x8DC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv681
  obtain ⟨n682, v682, d682, hv682, u682⟩ := u681.aluG hc psm_at_8dc (off' := 0x8DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv682
  obtain ⟨n683, v683, d683, hv683, u683⟩ := u682.aluG hc psm_at_8de (off' := 0x8E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv683
  obtain ⟨n684, v684, d684, hv684, u684⟩ := u683.aluG hc psm_at_8e2 (off' := 0x8E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv684
  obtain ⟨n685, v685, d685, hv685, u685⟩ := u684.aluG hc psm_at_8e6 (off' := 0x8E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv685
  obtain ⟨n686, v686, d686, hv686, u686⟩ := u685.aluG hc psm_at_8e8 (off' := 0x8EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv686
  obtain ⟨n687, v687, d687, hv687, u687⟩ := u686.aluG hc psm_at_8ea (off' := 0x8EC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv687
  obtain ⟨n688, v688, d688, hv688, u688⟩ := u687.aluG hc psm_at_8ec (off' := 0x8F0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv688
  obtain ⟨n689, v689, d689, hv689, u689⟩ := u688.aluG hc psm_at_8f0 (off' := 0x8F4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv689
  obtain ⟨n690, v690, d690, hv690, u690⟩ := u689.aluG hc psm_at_8f4 (off' := 0x8F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv690
  obtain ⟨n691, v691, d691, hv691, u691⟩ := u690.aluG hc psm_at_8f6 (off' := 0x8FA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv691
  obtain ⟨n692, v692, d692, hv692, u692⟩ := u691.aluG hc psm_at_8fa (off' := 0x8FE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv692
  obtain ⟨n693, v693, d693, hv693, u693⟩ := u692.aluG hc psm_at_8fe (off' := 0x900) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv693
  obtain ⟨n694, v694, d694, hv694, u694⟩ := u693.aluG hc psm_at_900 (off' := 0x902) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv694
  obtain ⟨n695, v695, d695, hv695, u695⟩ := u694.aluG hc psm_at_902 (off' := 0x904) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv695
  obtain ⟨n696, v696, d696, hv696, u696⟩ := u695.aluG hc psm_at_904 (off' := 0x908) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv696
  obtain ⟨n697, v697, d697, hv697, u697⟩ := u696.aluG hc psm_at_908 (off' := 0x90C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv697
  obtain ⟨n698, v698, d698, hv698, u698⟩ := u697.aluG hc psm_at_90c (off' := 0x910) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv698
  obtain ⟨n699, v699, d699, hv699, u699⟩ := u698.aluG hc psm_at_910 (off' := 0x912) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv699
  obtain ⟨n700, v700, d700, hv700, u700⟩ := u699.aluG hc psm_at_912 (off' := 0x916) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv700
  obtain ⟨n701, v701, d701, hv701, u701⟩ := u700.aluG hc psm_at_916 (off' := 0x918) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv701
  obtain ⟨n702, v702, d702, hv702, u702⟩ := u701.aluG hc psm_at_918 (off' := 0x91C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv702
  obtain ⟨n703, v703, d703, hv703, u703⟩ := u702.aluG hc psm_at_91c (off' := 0x920) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv703
  obtain ⟨n704, v704, d704, hv704, u704⟩ := u703.aluG hc psm_at_920 (off' := 0x922) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv704
  obtain ⟨n705, d705, u705⟩ := u704.swG hc psm_at_922 (off' := 0x924) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 12) (by decide)) (a := F + 0xC) (v := v704)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M705, hM705⟩ : ∃ M', memStore32 Mi (F + 0xC) v704 = M' := ⟨_, rfl⟩
  rw [hM705] at u705
  have hc705 : CodeIn M705 B p256ScalarMulCode := by rw [← hM705]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr705 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M705 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM705, memStore32_get_sep (frm_sep' hx1 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n706, v706, d706, hv706, u706⟩ := u705.aluG hc705 psm_at_924 (off' := 0x928) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv706
  obtain ⟨n707, v707, d707, hv707, u707⟩ := u706.aluG hc705 psm_at_928 (off' := 0x92C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv707
  obtain ⟨n708, v708, d708, hv708, u708⟩ := u707.aluG hc705 psm_at_92c (off' := 0x92E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv708
  obtain ⟨n709, v709, d709, hv709, u709⟩ := u708.aluG hc705 psm_at_92e (off' := 0x932) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv709
  obtain ⟨n710, v710, d710, hv710, u710⟩ := u709.aluG hc705 psm_at_932 (off' := 0x934) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv710
  obtain ⟨n711, v711, d711, hv711, u711⟩ := u710.aluG hc705 psm_at_934 (off' := 0x938) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv711
  obtain ⟨n712, v712, d712, hv712, u712⟩ := u711.aluG hc705 psm_at_938 (off' := 0x93A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv712
  obtain ⟨n713, v713, d713, hv713, u713⟩ := u712.aluG hc705 psm_at_93a (off' := 0x93C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv713
  obtain ⟨n714, v714, d714, hv714, u714⟩ := u713.aluG hc705 psm_at_93c (off' := 0x940) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv714
  obtain ⟨n715, v715, d715, hv715, u715⟩ := u714.aluG hc705 psm_at_940 (off' := 0x942) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv715
  obtain ⟨n716, v716, d716, hv716, u716⟩ := u715.aluG hc705 psm_at_942 (off' := 0x944) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv716
  obtain ⟨n717, v717, d717, hv717, u717⟩ := u716.aluG hc705 psm_at_944 (off' := 0x948) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv717
  obtain ⟨n718, v718, d718, hv718, u718⟩ := u717.aluG hc705 psm_at_948 (off' := 0x94A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv718
  obtain ⟨n719, v719, d719, hv719, u719⟩ := u718.aluG hc705 psm_at_94a (off' := 0x94E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv719
  have qo1 : reg n719 ra = v640 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n719 sp = F := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n719 (3 : Fin 32) = G3 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n719 (4 : Fin 32) = G4 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n719 (5 : Fin 32) = v603 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n719 (6 : Fin 32) = v525 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n719 (7 : Fin 32) = v506 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n719 (8 : Fin 32) = v709 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n719 (9 : Fin 32) = v700 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n719 a0 = v703 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n719 a1 = v717 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n719 a2 = v715 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n719 a3 = v713 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n719 a4 = v718 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n719 a5 = v714 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n719 a6 = v541 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n719 a7 = v693 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n719 (18 : Fin 32) = v719 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n719 (19 : Fin 32) = v465 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n719 (20 : Fin 32) = v488 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n719 (21 : Fin 32) = v516 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n719 (22 : Fin 32) = v522 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n719 (23 : Fin 32) = v510 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n719 (24 : Fin 32) = v509 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n719 (25 : Fin 32) = v708 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n719 (26 : Fin 32) = v665 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n719 (27 : Fin 32) = v651 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n719 (28 : Fin 32) = v500 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n719 (29 : Fin 32) = v494 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n719 (30 : Fin 32) = v615 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n719 (31 : Fin 32) = v706 := by rw [u719.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 M705 (F + 0xC) = v704 := by
    rw [← hM705, memLoad32_store32_same]
  have so10 : memLoad32 M705 (F + 0x10) = v672 := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x10) 4 from sep_offsets F (c := 12) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so14 : memLoad32 M705 (F + 0x14) = v636 := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x14) 4 from sep_offsets F (c := 12) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), sl14]
  have so18 : memLoad32 M705 (F + 0x18) = v591 := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x18) 4 from sep_offsets F (c := 12) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), sl18]
  have so1C : memLoad32 M705 (F + 0x1C) = v544 := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x1C) 4 from sep_offsets F (c := 12) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), sl1C]
  have so20 : memLoad32 M705 (F + 0x20) = v7 := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x20) 4 from sep_offsets F (c := 12) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), sl20]
  have so24 : memLoad32 M705 (F + 0x24) = v0 := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x24) 4 from sep_offsets F (c := 12) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), sl24]
  have so28 : memLoad32 M705 (F + 0x28) = outp := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x28) 4 from sep_offsets F (c := 12) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M705 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x2C) 4 from sep_offsets F (c := 12) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M705 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x30) 4 from sep_offsets F (c := 12) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M705 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x34) 4 from sep_offsets F (c := 12) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M705 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x38) 4 from sep_offsets F (c := 12) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M705 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x3C) 4 from sep_offsets F (c := 12) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M705 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x40) 4 from sep_offsets F (c := 12) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M705 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x44) 4 from sep_offsets F (c := 12) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M705 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x48) 4 from sep_offsets F (c := 12) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M705 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x4C) 4 from sep_offsets F (c := 12) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 M705 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x50) 4 from sep_offsets F (c := 12) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 M705 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x54) 4 from sep_offsets F (c := 12) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 M705 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x58) 4 from sep_offsets F (c := 12) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 M705 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x5C) 4 from sep_offsets F (c := 12) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 M705 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x60) 4 from sep_offsets F (c := 12) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 M705 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x64) 4 from sep_offsets F (c := 12) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 M705 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x68) 4 from sep_offsets F (c := 12) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 M705 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x6C) 4 from sep_offsets F (c := 12) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 M705 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x70) 4 from sep_offsets F (c := 12) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 M705 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x74) 4 from sep_offsets F (c := 12) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 M705 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x78) 4 from sep_offsets F (c := 12) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 M705 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x7C) 4 from sep_offsets F (c := 12) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 M705 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x80) 4 from sep_offsets F (c := 12) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 M705 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x84) 4 from sep_offsets F (c := 12) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 M705 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x88) 4 from sep_offsets F (c := 12) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 M705 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x8C) 4 from sep_offsets F (c := 12) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 M705 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x90) 4 from sep_offsets F (c := 12) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 M705 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x94) 4 from sep_offsets F (c := 12) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 M705 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x98) 4 from sep_offsets F (c := 12) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 M705 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM705, memLoad32_store32_sep (show Sep (F + 0xC) 4 (F + 0x9C) 4 from sep_offsets F (c := 12) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  exact ⟨n719, M705, v680, v681, v682, v683, v684, v685, v686, v687, v688, v689, v690, v691, v692, v693, v694, v695, v696, v697, v698, v699, v700, v701, v702, v703, v704, v706, v707, v708, v709, v710, v711, v712, v713, v714, v715, v716, v717, v718, v719, (.cons d680 (.cons d681 (.cons d682 (.cons d683 (.cons d684 (.cons d685 (.cons d686 (.cons d687 (.cons d688 (.cons d689 (.cons d690 (.cons d691 (.cons d692 (.cons d693 (.cons d694 (.cons d695 (.cons d696 (.cons d697 (.cons d698 (.cons d699 (.cons d700 (.cons d701 (.cons d702 (.cons d703 (.cons d704 (.cons d705 (.cons d706 (.cons d707 (.cons d708 (.cons d709 (.cons d710 (.cons d711 (.cons d712 (.cons d713 (.cons d714 (.cons d715 (.cons d716 (.cons d717 (.cons d718 (.single d719)))))))))))))))))))))))))))))))))))))))), u719.self, hc705, fr705, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv680, hv681, hv682, hv683, hv684, hv685, hv686, hv687, hv688, hv689, hv690, hv691, hv692, hv693, hv694, hv695, hv696, hv697, hv698, hv699, hv700, hv701, hv702, hv703, hv704, hv706, hv707, hv708, hv709, hv710, hv711, hv712, hv713, hv714, hv715, hv716, hv717, hv718, hv719⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g18 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v7 v465 v488 v494 v500 v506 v509 v510 v516 v522 v525 v541 v544 v591 v603 v615 v636 v640 v651 v665 v672 v693 v700 v703 v704 v706 v708 v709 v713 v714 v715 v717 v718 v719 : Word}
    (s : St Mi B n 0x94E (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v640)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v603)
    (q6 : reg n (6 : Fin 32) = v525)
    (q7 : reg n (7 : Fin 32) = v506)
    (q8 : reg n (8 : Fin 32) = v709)
    (q9 : reg n (9 : Fin 32) = v700)
    (q10 : reg n a0 = v703)
    (q11 : reg n a1 = v717)
    (q12 : reg n a2 = v715)
    (q13 : reg n a3 = v713)
    (q14 : reg n a4 = v718)
    (q15 : reg n a5 = v714)
    (q16 : reg n a6 = v541)
    (q17 : reg n a7 = v693)
    (q18 : reg n (18 : Fin 32) = v719)
    (q19 : reg n (19 : Fin 32) = v465)
    (q20 : reg n (20 : Fin 32) = v488)
    (q21 : reg n (21 : Fin 32) = v516)
    (q22 : reg n (22 : Fin 32) = v522)
    (q23 : reg n (23 : Fin 32) = v510)
    (q24 : reg n (24 : Fin 32) = v509)
    (q25 : reg n (25 : Fin 32) = v708)
    (q26 : reg n (26 : Fin 32) = v665)
    (q27 : reg n (27 : Fin 32) = v651)
    (q28 : reg n (28 : Fin 32) = v500)
    (q29 : reg n (29 : Fin 32) = v494)
    (q30 : reg n (30 : Fin 32) = v615)
    (q31 : reg n (31 : Fin 32) = v706)
    (slC : memLoad32 Mi (F + 0xC) = v704)
    (sl10 : memLoad32 Mi (F + 0x10) = v672)
    (sl14 : memLoad32 Mi (F + 0x14) = v636)
    (sl18 : memLoad32 Mi (F + 0x18) = v591)
    (sl1C : memLoad32 Mi (F + 0x1C) = v544)
    (sl20 : memLoad32 Mi (F + 0x20) = v7)
    (sl24 : memLoad32 Mi (F + 0x24) = v0)
    (sl28 : memLoad32 Mi (F + 0x28) = outp)
    (sl2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C))
    (sl30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30))
    (sl34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34))
    (sl38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38))
    (sl3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C))
    (sl40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40))
    (sl44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44))
    (sl48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48))
    (sl4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C))
    (sl50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50))
    (sl54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54))
    (sl58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58))
    (sl5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C))
    (sl60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60))
    (sl64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64))
    (sl68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68))
    (sl6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C))
    (sl70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70))
    (sl74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74))
    (sl78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78))
    (sl7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C))
    (sl80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80))
    (sl84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84))
    (sl88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88))
    (sl8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C))
    (sl90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90))
    (sl94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94))
    (sl98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98))
    (sl9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C))
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v720 v721 v722 v723 v724 v725 v726 v727 v728 v729 v730 v731 v732 v733 v734 v735 v736 v737 v738 v739 v740 v741 v742 v743 v744 v746 v747 v748 v749 v750 v751 v752 v753 v754 v755 v756 v757 v758 v759 : Word),
      Steps n n' ∧
      St M' B n' 0x9C0 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v640 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v603 ∧
      reg n' (6 : Fin 32) = v525 ∧
      reg n' (7 : Fin 32) = v506 ∧
      reg n' (8 : Fin 32) = v758 ∧
      reg n' (9 : Fin 32) = v757 ∧
      reg n' a0 = v756 ∧
      reg n' a1 = v749 ∧
      reg n' a2 = v753 ∧
      reg n' a3 = v746 ∧
      reg n' a4 = v750 ∧
      reg n' a5 = v751 ∧
      reg n' a6 = v541 ∧
      reg n' a7 = v693 ∧
      reg n' (18 : Fin 32) = v731 ∧
      reg n' (19 : Fin 32) = v759 ∧
      reg n' (20 : Fin 32) = v488 ∧
      reg n' (21 : Fin 32) = v516 ∧
      reg n' (22 : Fin 32) = v522 ∧
      reg n' (23 : Fin 32) = v510 ∧
      reg n' (24 : Fin 32) = v509 ∧
      reg n' (25 : Fin 32) = v748 ∧
      reg n' (26 : Fin 32) = v742 ∧
      reg n' (27 : Fin 32) = v743 ∧
      reg n' (28 : Fin 32) = v726 ∧
      reg n' (29 : Fin 32) = v494 ∧
      reg n' (30 : Fin 32) = v615 ∧
      reg n' (31 : Fin 32) = v755 ∧
      memLoad32 M' (F + 0x8) = v744 ∧
      memLoad32 M' (F + 0xC) = v704 ∧
      memLoad32 M' (F + 0x10) = v672 ∧
      memLoad32 M' (F + 0x14) = v636 ∧
      memLoad32 M' (F + 0x18) = v591 ∧
      memLoad32 M' (F + 0x1C) = v544 ∧
      memLoad32 M' (F + 0x20) = v7 ∧
      memLoad32 M' (F + 0x24) = v0 ∧
      memLoad32 M' (F + 0x28) = outp ∧
      memLoad32 M' (F + 0x2C) = memLoad32 M0 (F + 0x2C) ∧
      memLoad32 M' (F + 0x30) = memLoad32 M0 (F + 0x30) ∧
      memLoad32 M' (F + 0x34) = memLoad32 M0 (F + 0x34) ∧
      memLoad32 M' (F + 0x38) = memLoad32 M0 (F + 0x38) ∧
      memLoad32 M' (F + 0x3C) = memLoad32 M0 (F + 0x3C) ∧
      memLoad32 M' (F + 0x40) = memLoad32 M0 (F + 0x40) ∧
      memLoad32 M' (F + 0x44) = memLoad32 M0 (F + 0x44) ∧
      memLoad32 M' (F + 0x48) = memLoad32 M0 (F + 0x48) ∧
      memLoad32 M' (F + 0x4C) = memLoad32 M0 (F + 0x4C) ∧
      memLoad32 M' (F + 0x50) = memLoad32 M0 (F + 0x50) ∧
      memLoad32 M' (F + 0x54) = memLoad32 M0 (F + 0x54) ∧
      memLoad32 M' (F + 0x58) = memLoad32 M0 (F + 0x58) ∧
      memLoad32 M' (F + 0x5C) = memLoad32 M0 (F + 0x5C) ∧
      memLoad32 M' (F + 0x60) = memLoad32 M0 (F + 0x60) ∧
      memLoad32 M' (F + 0x64) = memLoad32 M0 (F + 0x64) ∧
      memLoad32 M' (F + 0x68) = memLoad32 M0 (F + 0x68) ∧
      memLoad32 M' (F + 0x6C) = memLoad32 M0 (F + 0x6C) ∧
      memLoad32 M' (F + 0x70) = memLoad32 M0 (F + 0x70) ∧
      memLoad32 M' (F + 0x74) = memLoad32 M0 (F + 0x74) ∧
      memLoad32 M' (F + 0x78) = memLoad32 M0 (F + 0x78) ∧
      memLoad32 M' (F + 0x7C) = memLoad32 M0 (F + 0x7C) ∧
      memLoad32 M' (F + 0x80) = memLoad32 M0 (F + 0x80) ∧
      memLoad32 M' (F + 0x84) = memLoad32 M0 (F + 0x84) ∧
      memLoad32 M' (F + 0x88) = memLoad32 M0 (F + 0x88) ∧
      memLoad32 M' (F + 0x8C) = memLoad32 M0 (F + 0x8C) ∧
      memLoad32 M' (F + 0x90) = memLoad32 M0 (F + 0x90) ∧
      memLoad32 M' (F + 0x94) = memLoad32 M0 (F + 0x94) ∧
      memLoad32 M' (F + 0x98) = memLoad32 M0 (F + 0x98) ∧
      memLoad32 M' (F + 0x9C) = memLoad32 M0 (F + 0x9C) ∧
      aluEval .add v717 v709 = v720 ∧
      aluEval .sltu v718 v715 = v721 ∧
      aluEval .mul v500 v522 = v722 ∧
      aluEval .mulhu v506 v509 = v723 ∧
      aluEval .mul v506 v510 = v724 ∧
      aluEval .mul v506 v516 = v725 ∧
      aluEval .add v720 v721 = v726 ∧
      aluEval .mul v525 v510 = v727 ∧
      aluEval .mulhu v506 v510 = v728 ∧
      aluEval .mul v541 v509 = v729 ∧
      aluEval .sub v603 v488 = v730 ∧
      aluEval .add v719 v713 = v731 ∧
      aluEval .sub v730 v494 = v732 ∧
      aluEval .sltu v731 v713 = v733 ∧
      aluEval .add v733 v723 = v734 ∧
      aluEval .add v732 v722 = v735 ∧
      aluEval .add v725 v735 = v736 ∧
      aluEval .add v724 v718 = v737 ∧
      aluEval .sltu v737 v718 = v738 ∧
      aluEval .add v736 v727 = v739 ∧
      aluEval .add v728 v738 = v740 ∧
      aluEval .add v739 v729 = v741 ∧
      memLoad32 M0 (F + 0x3C) = v742 ∧
      memLoad32 M0 (F + 0x40) = v743 ∧
      memLoad32 M0 (F + 0x44) = v744 ∧
      aluEval .add v734 v737 = v746 ∧
      aluEval .add v741 v615 = v747 ∧
      aluEval .mul v525 v509 = v748 ∧
      aluEval .mul v465 v509 = v749 ∧
      aluEval .sltu v746 v737 = v750 ∧
      aluEval .mulhu v525 v509 = v751 ∧
      aluEval .add v747 v640 = v752 ∧
      aluEval .add v740 v750 = v753 ∧
      aluEval .add v752 v693 = v754 ∧
      aluEval .add v706 v754 = v755 ∧
      memLoad32 M0 (F + 0x2C) = v756 ∧
      memLoad32 M0 (F + 0x30) = v757 ∧
      memLoad32 M0 (F + 0x34) = v758 ∧
      memLoad32 M0 (F + 0x38) = v759 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n720, v720, d720, hv720, u720⟩ := s.aluG hc psm_at_94e (off' := 0x950) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv720
  obtain ⟨n721, v721, d721, hv721, u721⟩ := u720.aluG hc psm_at_950 (off' := 0x954) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv721
  obtain ⟨n722, v722, d722, hv722, u722⟩ := u721.aluG hc psm_at_954 (off' := 0x958) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv722
  obtain ⟨n723, v723, d723, hv723, u723⟩ := u722.aluG hc psm_at_958 (off' := 0x95C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv723
  obtain ⟨n724, v724, d724, hv724, u724⟩ := u723.aluG hc psm_at_95c (off' := 0x960) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv724
  obtain ⟨n725, v725, d725, hv725, u725⟩ := u724.aluG hc psm_at_960 (off' := 0x964) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv725
  obtain ⟨n726, v726, d726, hv726, u726⟩ := u725.aluG hc psm_at_964 (off' := 0x968) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv726
  obtain ⟨n727, v727, d727, hv727, u727⟩ := u726.aluG hc psm_at_968 (off' := 0x96C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv727
  obtain ⟨n728, v728, d728, hv728, u728⟩ := u727.aluG hc psm_at_96c (off' := 0x970) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv728
  obtain ⟨n729, v729, d729, hv729, u729⟩ := u728.aluG hc psm_at_970 (off' := 0x974) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv729
  obtain ⟨n730, v730, d730, hv730, u730⟩ := u729.aluG hc psm_at_974 (off' := 0x978) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv730
  obtain ⟨n731, v731, d731, hv731, u731⟩ := u730.aluG hc psm_at_978 (off' := 0x97A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv731
  obtain ⟨n732, v732, d732, hv732, u732⟩ := u731.aluG hc psm_at_97a (off' := 0x97E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv732
  obtain ⟨n733, v733, d733, hv733, u733⟩ := u732.aluG hc psm_at_97e (off' := 0x982) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv733
  obtain ⟨n734, v734, d734, hv734, u734⟩ := u733.aluG hc psm_at_982 (off' := 0x984) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv734
  obtain ⟨n735, v735, d735, hv735, u735⟩ := u734.aluG hc psm_at_984 (off' := 0x986) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv735
  obtain ⟨n736, v736, d736, hv736, u736⟩ := u735.aluG hc psm_at_986 (off' := 0x988) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv736
  obtain ⟨n737, v737, d737, hv737, u737⟩ := u736.aluG hc psm_at_988 (off' := 0x98A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv737
  obtain ⟨n738, v738, d738, hv738, u738⟩ := u737.aluG hc psm_at_98a (off' := 0x98E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv738
  obtain ⟨n739, v739, d739, hv739, u739⟩ := u738.aluG hc psm_at_98e (off' := 0x990) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv739
  obtain ⟨n740, v740, d740, hv740, u740⟩ := u739.aluG hc psm_at_990 (off' := 0x992) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv740
  obtain ⟨n741, v741, d741, hv741, u741⟩ := u740.aluG hc psm_at_992 (off' := 0x994) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv741
  obtain ⟨n742, v742, d742, hv742, u742⟩ := u741.lwG hc psm_at_994 (off' := 0x996) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 60) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv742
  rw [sl3C] at hv742
  obtain ⟨n743, v743, d743, hv743, u743⟩ := u742.lwG hc psm_at_996 (off' := 0x998) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 64) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv743
  rw [sl40] at hv743
  obtain ⟨n744, v744, d744, hv744, u744⟩ := u743.lwG hc psm_at_998 (off' := 0x99A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 68) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv744
  rw [sl44] at hv744
  obtain ⟨n745, d745, u745⟩ := u744.swG hc psm_at_99a (off' := 0x99C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 8) (by decide)) (a := F + 0x8) (v := v744)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨M745, hM745⟩ : ∃ M', memStore32 Mi (F + 0x8) v744 = M' := ⟨_, rfl⟩
  rw [hM745] at u745
  have hc745 : CodeIn M745 B p256ScalarMulCode := by rw [← hM745]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr745 : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M745 x = M0 x := fun x hx1 hx2 hx3 => by
    rw [← hM745, memStore32_get_sep (frm_sep' hx1 (by decide)), fr x hx1 hx2 hx3]
  obtain ⟨n746, v746, d746, hv746, u746⟩ := u745.aluG hc745 psm_at_99c (off' := 0x99E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv746
  obtain ⟨n747, v747, d747, hv747, u747⟩ := u746.aluG hc745 psm_at_99e (off' := 0x9A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv747
  obtain ⟨n748, v748, d748, hv748, u748⟩ := u747.aluG hc745 psm_at_9a0 (off' := 0x9A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv748
  obtain ⟨n749, v749, d749, hv749, u749⟩ := u748.aluG hc745 psm_at_9a4 (off' := 0x9A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv749
  obtain ⟨n750, v750, d750, hv750, u750⟩ := u749.aluG hc745 psm_at_9a8 (off' := 0x9AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv750
  obtain ⟨n751, v751, d751, hv751, u751⟩ := u750.aluG hc745 psm_at_9ac (off' := 0x9B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv751
  obtain ⟨n752, v752, d752, hv752, u752⟩ := u751.aluG hc745 psm_at_9b0 (off' := 0x9B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv752
  obtain ⟨n753, v753, d753, hv753, u753⟩ := u752.aluG hc745 psm_at_9b2 (off' := 0x9B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv753
  obtain ⟨n754, v754, d754, hv754, u754⟩ := u753.aluG hc745 psm_at_9b4 (off' := 0x9B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv754
  obtain ⟨n755, v755, d755, hv755, u755⟩ := u754.aluG hc745 psm_at_9b6 (off' := 0x9B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv755
  obtain ⟨n756, v756, d756, hv756, u756⟩ := u755.lwG hc745 psm_at_9b8 (off' := 0x9BA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 44) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv756
  rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x2C) 4 from sep_offsets F (c := 8) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C] at hv756
  obtain ⟨n757, v757, d757, hv757, u757⟩ := u756.lwG hc745 psm_at_9ba (off' := 0x9BC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 48) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv757
  rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x30) 4 from sep_offsets F (c := 8) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30] at hv757
  obtain ⟨n758, v758, d758, hv758, u758⟩ := u757.lwG hc745 psm_at_9bc (off' := 0x9BE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 52) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv758
  rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x34) 4 from sep_offsets F (c := 8) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34] at hv758
  obtain ⟨n759, v759, d759, hv759, u759⟩ := u758.lwG hc745 psm_at_9be (off' := 0x9C0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 56) (by decide))
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv759
  rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x38) 4 from sep_offsets F (c := 8) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38] at hv759
  have qo1 : reg n759 ra = v640 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n759 sp = F := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n759 (3 : Fin 32) = G3 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n759 (4 : Fin 32) = G4 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n759 (5 : Fin 32) = v603 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n759 (6 : Fin 32) = v525 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n759 (7 : Fin 32) = v506 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n759 (8 : Fin 32) = v758 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n759 (9 : Fin 32) = v757 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n759 a0 = v756 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n759 a1 = v749 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n759 a2 = v753 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n759 a3 = v746 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n759 a4 = v750 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n759 a5 = v751 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n759 a6 = v541 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n759 a7 = v693 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n759 (18 : Fin 32) = v731 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n759 (19 : Fin 32) = v759 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n759 (20 : Fin 32) = v488 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n759 (21 : Fin 32) = v516 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n759 (22 : Fin 32) = v522 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n759 (23 : Fin 32) = v510 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n759 (24 : Fin 32) = v509 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n759 (25 : Fin 32) = v748 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n759 (26 : Fin 32) = v742 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n759 (27 : Fin 32) = v743 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n759 (28 : Fin 32) = v726 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n759 (29 : Fin 32) = v494 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n759 (30 : Fin 32) = v615 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n759 (31 : Fin 32) = v755 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so8 : memLoad32 M745 (F + 0x8) = v744 := by
    rw [← hM745, memLoad32_store32_same]
  have soC : memLoad32 M745 (F + 0xC) = v704 := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0xC) 4 from sep_offsets F (c := 8) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 M745 (F + 0x10) = v672 := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x10) 4 from sep_offsets F (c := 8) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so14 : memLoad32 M745 (F + 0x14) = v636 := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x14) 4 from sep_offsets F (c := 8) (n := 4) (d := 20) (k := 4) (by decide) (by decide) (by decide)), sl14]
  have so18 : memLoad32 M745 (F + 0x18) = v591 := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x18) 4 from sep_offsets F (c := 8) (n := 4) (d := 24) (k := 4) (by decide) (by decide) (by decide)), sl18]
  have so1C : memLoad32 M745 (F + 0x1C) = v544 := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x1C) 4 from sep_offsets F (c := 8) (n := 4) (d := 28) (k := 4) (by decide) (by decide) (by decide)), sl1C]
  have so20 : memLoad32 M745 (F + 0x20) = v7 := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x20) 4 from sep_offsets F (c := 8) (n := 4) (d := 32) (k := 4) (by decide) (by decide) (by decide)), sl20]
  have so24 : memLoad32 M745 (F + 0x24) = v0 := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x24) 4 from sep_offsets F (c := 8) (n := 4) (d := 36) (k := 4) (by decide) (by decide) (by decide)), sl24]
  have so28 : memLoad32 M745 (F + 0x28) = outp := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x28) 4 from sep_offsets F (c := 8) (n := 4) (d := 40) (k := 4) (by decide) (by decide) (by decide)), sl28]
  have so2C : memLoad32 M745 (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x2C) 4 from sep_offsets F (c := 8) (n := 4) (d := 44) (k := 4) (by decide) (by decide) (by decide)), sl2C]
  have so30 : memLoad32 M745 (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x30) 4 from sep_offsets F (c := 8) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so34 : memLoad32 M745 (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x34) 4 from sep_offsets F (c := 8) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34]
  have so38 : memLoad32 M745 (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x38) 4 from sep_offsets F (c := 8) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38]
  have so3C : memLoad32 M745 (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x3C) 4 from sep_offsets F (c := 8) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 M745 (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x40) 4 from sep_offsets F (c := 8) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 M745 (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x44) 4 from sep_offsets F (c := 8) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 M745 (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x48) 4 from sep_offsets F (c := 8) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 M745 (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x4C) 4 from sep_offsets F (c := 8) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 M745 (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x50) 4 from sep_offsets F (c := 8) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 M745 (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x54) 4 from sep_offsets F (c := 8) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 M745 (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x58) 4 from sep_offsets F (c := 8) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 M745 (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x5C) 4 from sep_offsets F (c := 8) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 M745 (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x60) 4 from sep_offsets F (c := 8) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 M745 (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x64) 4 from sep_offsets F (c := 8) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 M745 (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x68) 4 from sep_offsets F (c := 8) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 M745 (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x6C) 4 from sep_offsets F (c := 8) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 M745 (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x70) 4 from sep_offsets F (c := 8) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 M745 (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x74) 4 from sep_offsets F (c := 8) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 M745 (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x78) 4 from sep_offsets F (c := 8) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 M745 (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x7C) 4 from sep_offsets F (c := 8) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 M745 (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x80) 4 from sep_offsets F (c := 8) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 M745 (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x84) 4 from sep_offsets F (c := 8) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 M745 (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x88) 4 from sep_offsets F (c := 8) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 M745 (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x8C) 4 from sep_offsets F (c := 8) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 M745 (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x90) 4 from sep_offsets F (c := 8) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 M745 (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x94) 4 from sep_offsets F (c := 8) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 M745 (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x98) 4 from sep_offsets F (c := 8) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 M745 (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [← hM745, memLoad32_store32_sep (show Sep (F + 0x8) 4 (F + 0x9C) 4 from sep_offsets F (c := 8) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  exact ⟨n759, M745, v720, v721, v722, v723, v724, v725, v726, v727, v728, v729, v730, v731, v732, v733, v734, v735, v736, v737, v738, v739, v740, v741, v742, v743, v744, v746, v747, v748, v749, v750, v751, v752, v753, v754, v755, v756, v757, v758, v759, (.cons d720 (.cons d721 (.cons d722 (.cons d723 (.cons d724 (.cons d725 (.cons d726 (.cons d727 (.cons d728 (.cons d729 (.cons d730 (.cons d731 (.cons d732 (.cons d733 (.cons d734 (.cons d735 (.cons d736 (.cons d737 (.cons d738 (.cons d739 (.cons d740 (.cons d741 (.cons d742 (.cons d743 (.cons d744 (.cons d745 (.cons d746 (.cons d747 (.cons d748 (.cons d749 (.cons d750 (.cons d751 (.cons d752 (.cons d753 (.cons d754 (.cons d755 (.cons d756 (.cons d757 (.cons d758 (.single d759)))))))))))))))))))))))))))))))))))))))), u759.self, hc745, fr745, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so8, soC, so10, so14, so18, so1C, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv720, hv721, hv722, hv723, hv724, hv725, hv726, hv727, hv728, hv729, hv730, hv731, hv732, hv733, hv734, hv735, hv736, hv737, hv738, hv739, hv740, hv741, hv742, hv743, hv744, hv746, hv747, hv748, hv749, hv750, hv751, hv752, hv753, hv754, hv755, hv756, hv757, hv758, hv759⟩

end C3.RV32
