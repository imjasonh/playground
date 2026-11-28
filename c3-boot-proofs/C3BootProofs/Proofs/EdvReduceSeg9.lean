import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce` in `ed25519_verify`, segments 24 to 27

Each theorem steps 40 instructions. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g24 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v87 v111 v116 v122 v124 v133 v136 v150 v151 v174 v199 v203 v206 v219 v231 v239 v254 v264 v274 v279 v284 v297 v302 v310 v335 v341 v352 v357 v405 v419 v467 v476 v480 v481 v485 v540 v545 v557 v559 v572 v576 v579 v582 v592 v593 v638 v639 v640 v642 v645 v647 v649 v651 v654 v656 v658 v660 v662 v665 v667 v669 v671 v673 v676 v678 v680 v682 v684 v685 v687 v689 v691 v693 v695 v697 v698 v699 v700 v702 v704 v705 v706 v708 v710 v712 v713 v715 v717 v719 : Word}
    (s : St Mi B n 0xA4C (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v673)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v576)
    (q6 : reg n (6 : Fin 32) = v699)
    (q7 : reg n (7 : Fin 32) = v592)
    (q8 : reg n (8 : Fin 32) = v697)
    (q9 : reg n (9 : Fin 32) = v87)
    (q10 : reg n a0 = v639)
    (q11 : reg n a1 = v717)
    (q12 : reg n a2 = v698)
    (q13 : reg n a3 = v715)
    (q14 : reg n a4 = v702)
    (q15 : reg n a5 = v684)
    (q16 : reg n a6 = v719)
    (q17 : reg n a7 = v712)
    (q18 : reg n (18 : Fin 32) = v705)
    (q19 : reg n (19 : Fin 32) = v593)
    (q20 : reg n (20 : Fin 32) = v310)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v476)
    (q25 : reg n (25 : Fin 32) = v174)
    (q26 : reg n (26 : Fin 32) = v480)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v254)
    (q29 : reg n (29 : Fin 32) = v638)
    (q30 : reg n (30 : Fin 32) = v133)
    (q31 : reg n (31 : Fin 32) = v704)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl14 : memLoad32 Mi (F + 0x14) = v671)
    (sl18 : memLoad32 Mi (F + 0x18) = v660)
    (sl1C : memLoad32 Mi (F + 0x1C) = v658)
    (sl20 : memLoad32 Mi (F + 0x20) = v642)
    (sl24 : memLoad32 Mi (F + 0x24) = v640)
    (sl28 : memLoad32 Mi (F + 0x28) = v651)
    (sl2C : memLoad32 Mi (F + 0x2C) = v649)
    (sl30 : memLoad32 Mi (F + 0x30) = v687)
    (sl34 : memLoad32 Mi (F + 0x34) = v654)
    (sl38 : memLoad32 Mi (F + 0x38) = v656)
    (sl3C : memLoad32 Mi (F + 0x3C) = v685)
    (sl40 : memLoad32 Mi (F + 0x40) = v665)
    (sl44 : memLoad32 Mi (F + 0x44) = v662)
    (sl48 : memLoad32 Mi (F + 0x48) = v647)
    (sl4C : memLoad32 Mi (F + 0x4C) = v678)
    (sl50 : memLoad32 Mi (F + 0x50) = v676)
    (sl54 : memLoad32 Mi (F + 0x54) = v645)
    (sl58 : memLoad32 Mi (F + 0x58) = v708)
    (sl5C : memLoad32 Mi (F + 0x5C) = v706)
    (sl60 : memLoad32 Mi (F + 0x60) = v680)
    (sl64 : memLoad32 Mi (F + 0x64) = v682)
    (sl68 : memLoad32 Mi (F + 0x68) = v689)
    (sl6C : memLoad32 Mi (F + 0x6C) = v691)
    (sl70 : memLoad32 Mi (F + 0x70) = v669)
    (sl74 : memLoad32 Mi (F + 0x74) = v667)
    (sl78 : memLoad32 Mi (F + 0x78) = v545)
    (sl7C : memLoad32 Mi (F + 0x7C) = v717)
    (sl80 : memLoad32 Mi (F + 0x80) = v715)
    (sl84 : memLoad32 Mi (F + 0x84) = v572)
    (sl88 : memLoad32 Mi (F + 0x88) = v695)
    (sl8C : memLoad32 Mi (F + 0x8C) = v559)
    (sl90 : memLoad32 Mi (F + 0x90) = v151)
    (sl94 : memLoad32 Mi (F + 0x94) = v481)
    (sl98 : memLoad32 Mi (F + 0x98) = v352)
    (sl9C : memLoad32 Mi (F + 0x9C) = v713)
    (slA4 : memLoad32 Mi (F + 0xA4) = v357)
    (slA8 : memLoad32 Mi (F + 0xA8) = v279)
    (slAC : memLoad32 Mi (F + 0xAC) = v219)
    (slB0 : memLoad32 Mi (F + 0xB0) = v693)
    (slB4 : memLoad32 Mi (F + 0xB4) = v582)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slD4 : memLoad32 Mi (F + 0xD4) = v239)
    (slDC : memLoad32 Mi (F + 0xDC) = v150)
    (slE4 : memLoad32 Mi (F + 0xE4) = v7)
    (slE8 : memLoad32 Mi (F + 0xE8) = v419)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slF4 : memLoad32 Mi (F + 0xF4) = v297)
    (slF8 : memLoad32 Mi (F + 0xF8) = v284)
    (slFC : memLoad32 Mi (F + 0xFC) = v579)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v710)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v720 v722 v724 v725 v726 v727 v728 v729 v730 v731 v732 v733 v734 v735 v736 v737 v738 v740 v741 v742 v743 v744 v745 v747 v748 v750 v752 v753 v754 v755 v757 v759 : Word),
      Steps n n' ∧
      St M' B n' 0xAC4 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v673 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v734 ∧
      reg n' (6 : Fin 32) = v699 ∧
      reg n' (7 : Fin 32) = v741 ∧
      reg n' (8 : Fin 32) = v697 ∧
      reg n' (9 : Fin 32) = v742 ∧
      reg n' a0 = v642 ∧
      reg n' a1 = v754 ∧
      reg n' a2 = v743 ∧
      reg n' a3 = v757 ∧
      reg n' a4 = v753 ∧
      reg n' a5 = v759 ∧
      reg n' a6 = v745 ∧
      reg n' a7 = v712 ∧
      reg n' (18 : Fin 32) = v705 ∧
      reg n' (19 : Fin 32) = v593 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v150 ∧
      reg n' (25 : Fin 32) = v174 ∧
      reg n' (26 : Fin 32) = v726 ∧
      reg n' (27 : Fin 32) = v700 ∧
      reg n' (28 : Fin 32) = v7 ∧
      reg n' (29 : Fin 32) = v638 ∧
      reg n' (30 : Fin 32) = v133 ∧
      reg n' (31 : Fin 32) = v704 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x14) = v671 ∧
      memLoad32 M' (F + 0x18) = v660 ∧
      memLoad32 M' (F + 0x1C) = v658 ∧
      memLoad32 M' (F + 0x28) = v651 ∧
      memLoad32 M' (F + 0x2C) = v649 ∧
      memLoad32 M' (F + 0x30) = v687 ∧
      memLoad32 M' (F + 0x34) = v654 ∧
      memLoad32 M' (F + 0x38) = v656 ∧
      memLoad32 M' (F + 0x3C) = v685 ∧
      memLoad32 M' (F + 0x40) = v665 ∧
      memLoad32 M' (F + 0x44) = v662 ∧
      memLoad32 M' (F + 0x48) = v647 ∧
      memLoad32 M' (F + 0x4C) = v678 ∧
      memLoad32 M' (F + 0x50) = v676 ∧
      memLoad32 M' (F + 0x54) = v645 ∧
      memLoad32 M' (F + 0x58) = v708 ∧
      memLoad32 M' (F + 0x5C) = v706 ∧
      memLoad32 M' (F + 0x60) = v680 ∧
      memLoad32 M' (F + 0x64) = v682 ∧
      memLoad32 M' (F + 0x68) = v689 ∧
      memLoad32 M' (F + 0x6C) = v691 ∧
      memLoad32 M' (F + 0x70) = v669 ∧
      memLoad32 M' (F + 0x74) = v667 ∧
      memLoad32 M' (F + 0x78) = v545 ∧
      memLoad32 M' (F + 0x7C) = v717 ∧
      memLoad32 M' (F + 0x80) = v715 ∧
      memLoad32 M' (F + 0x84) = v572 ∧
      memLoad32 M' (F + 0x88) = v695 ∧
      memLoad32 M' (F + 0x8C) = v559 ∧
      memLoad32 M' (F + 0x94) = v481 ∧
      memLoad32 M' (F + 0x98) = v352 ∧
      memLoad32 M' (F + 0x9C) = v713 ∧
      memLoad32 M' (F + 0xA4) = v357 ∧
      memLoad32 M' (F + 0xA8) = v279 ∧
      memLoad32 M' (F + 0xAC) = v219 ∧
      memLoad32 M' (F + 0xB0) = v693 ∧
      memLoad32 M' (F + 0xB4) = v582 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xCC) = v264 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xD4) = v239 ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xF4) = v297 ∧
      memLoad32 M' (F + 0xF8) = v284 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x104) = v710 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .mulhu v87 v639 = v720 ∧
      aluEval .and v702 v7 = v722 ∧
      aluEval .mul v722 v150 = v724 ∧
      aluEval .mulhu v722 v150 = v725 ∧
      aluEval .mul v87 v639 = v726 ∧
      aluEval .add v719 v638 = v727 ∧
      aluEval .add v727 v712 = v728 ∧
      aluEval .sltu v697 v684 = v729 ∧
      aluEval .add v729 v728 = v730 ∧
      aluEval .srl v593 0x1D = v731 ∧
      aluEval .add v730 v731 = v732 ∧
      aluEval .sltu v698 v697 = v733 ∧
      aluEval .add v720 v705 = v734 ∧
      aluEval .add v732 v733 = v735 ∧
      aluEval .add v735 v725 = v736 ∧
      aluEval .add v698 v724 = v737 ∧
      aluEval .sltu v737 v724 = v738 ∧
      aluEval .sltu v699 v111 = v740 ∧
      aluEval .add v736 v738 = v741 ∧
      aluEval .sub v700 v740 = v742 ∧
      aluEval .srl v737 0x1D = v743 ∧
      aluEval .sll v741 0x3 = v744 ∧
      aluEval .or v743 v744 = v745 ∧
      aluEval .sub v742 v122 = v747 ∧
      aluEval .sub v699 v111 = v748 ∧
      aluEval .sll v136 0x14 = v750 ∧
      aluEval .srl v151 0xC = v752 ∧
      aluEval .add v750 v748 = v753 ∧
      aluEval .add v747 v752 = v754 ∧
      aluEval .sltu v753 v748 = v755 ∧
      aluEval .add v755 v642 = v757 ∧
      aluEval .add v640 v753 = v759 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n720, v720, d720, hv720, u720⟩ := s.aluG hc ev_at_a4c (off' := 0xA50) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv720
  obtain ⟨n721, d721, u721⟩ := u720.lwE hc ev_at_a50 (off' := 0xA52) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 228) (by decide)) (v := v7)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slE4])
  obtain ⟨n722, v722, d722, hv722, u722⟩ := u721.aluG hc ev_at_a52 (off' := 0xA56) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv722
  obtain ⟨n723, d723, u723⟩ := u722.lwE hc ev_at_a56 (off' := 0xA58) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 220) (by decide)) (v := v150)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slDC])
  obtain ⟨n724, v724, d724, hv724, u724⟩ := u723.aluG hc ev_at_a58 (off' := 0xA5C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv724
  obtain ⟨n725, v725, d725, hv725, u725⟩ := u724.aluG hc ev_at_a5c (off' := 0xA60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv725
  obtain ⟨n726, v726, d726, hv726, u726⟩ := u725.aluG hc ev_at_a60 (off' := 0xA64) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv726
  obtain ⟨n727, v727, d727, hv727, u727⟩ := u726.aluG hc ev_at_a64 (off' := 0xA66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv727
  obtain ⟨n728, v728, d728, hv728, u728⟩ := u727.aluG hc ev_at_a66 (off' := 0xA6A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv728
  obtain ⟨n729, v729, d729, hv729, u729⟩ := u728.aluG hc ev_at_a6a (off' := 0xA6E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv729
  obtain ⟨n730, v730, d730, hv730, u730⟩ := u729.aluG hc ev_at_a6e (off' := 0xA70) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv730
  obtain ⟨n731, v731, d731, hv731, u731⟩ := u730.aluImmG hc ev_at_a70 (off' := 0xA74) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv731
  obtain ⟨n732, v732, d732, hv732, u732⟩ := u731.aluG hc ev_at_a74 (off' := 0xA76) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv732
  obtain ⟨n733, v733, d733, hv733, u733⟩ := u732.aluG hc ev_at_a76 (off' := 0xA7A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv733
  obtain ⟨n734, v734, d734, hv734, u734⟩ := u733.aluG hc ev_at_a7a (off' := 0xA7C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv734
  obtain ⟨n735, v735, d735, hv735, u735⟩ := u734.aluG hc ev_at_a7c (off' := 0xA7E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv735
  obtain ⟨n736, v736, d736, hv736, u736⟩ := u735.aluG hc ev_at_a7e (off' := 0xA80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv736
  obtain ⟨n737, v737, d737, hv737, u737⟩ := u736.aluG hc ev_at_a80 (off' := 0xA82) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv737
  obtain ⟨n738, v738, d738, hv738, u738⟩ := u737.aluG hc ev_at_a82 (off' := 0xA86) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv738
  obtain ⟨n739, d739, u739⟩ := u738.lwE hc ev_at_a86 (off' := 0xA8A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 276) (by decide)) (v := v111)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl114])
  obtain ⟨n740, v740, d740, hv740, u740⟩ := u739.aluG hc ev_at_a8a (off' := 0xA8E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv740
  obtain ⟨n741, v741, d741, hv741, u741⟩ := u740.aluG hc ev_at_a8e (off' := 0xA92) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv741
  obtain ⟨n742, v742, d742, hv742, u742⟩ := u741.aluG hc ev_at_a92 (off' := 0xA96) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv742
  obtain ⟨n743, v743, d743, hv743, u743⟩ := u742.aluImmG hc ev_at_a96 (off' := 0xA98) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv743
  obtain ⟨n744, v744, d744, hv744, u744⟩ := u743.aluImmG hc ev_at_a98 (off' := 0xA9C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv744
  obtain ⟨n745, v745, d745, hv745, u745⟩ := u744.aluG hc ev_at_a9c (off' := 0xAA0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv745
  obtain ⟨n746, d746, u746⟩ := u745.lwE hc ev_at_aa0 (off' := 0xAA4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 280) (by decide)) (v := v122)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl118])
  obtain ⟨n747, v747, d747, hv747, u747⟩ := u746.aluG hc ev_at_aa4 (off' := 0xAA8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv747
  obtain ⟨n748, v748, d748, hv748, u748⟩ := u747.aluG hc ev_at_aa8 (off' := 0xAAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv748
  obtain ⟨n749, d749, u749⟩ := u748.lwE hc ev_at_aac (off' := 0xAAE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 184) (by decide)) (v := v136)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slB8])
  obtain ⟨n750, v750, d750, hv750, u750⟩ := u749.aluImmG hc ev_at_aae (off' := 0xAB0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv750
  obtain ⟨n751, d751, u751⟩ := u750.lwE hc ev_at_ab0 (off' := 0xAB2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 144) (by decide)) (v := v151)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl90])
  obtain ⟨n752, v752, d752, hv752, u752⟩ := u751.aluImmG hc ev_at_ab2 (off' := 0xAB4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv752
  obtain ⟨n753, v753, d753, hv753, u753⟩ := u752.aluG hc ev_at_ab4 (off' := 0xAB6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv753
  obtain ⟨n754, v754, d754, hv754, u754⟩ := u753.aluG hc ev_at_ab6 (off' := 0xAB8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv754
  obtain ⟨n755, v755, d755, hv755, u755⟩ := u754.aluG hc ev_at_ab8 (off' := 0xABC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv755
  obtain ⟨n756, d756, u756⟩ := u755.lwE hc ev_at_abc (off' := 0xABE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 32) (by decide)) (v := v642)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl20])
  obtain ⟨n757, v757, d757, hv757, u757⟩ := u756.aluG hc ev_at_abe (off' := 0xAC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv757
  obtain ⟨n758, d758, u758⟩ := u757.lwE hc ev_at_ac0 (off' := 0xAC2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 36) (by decide)) (v := v640)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl24])
  obtain ⟨n759, v759, d759, hv759, u759⟩ := u758.aluG hc ev_at_ac2 (off' := 0xAC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv759
  have qo1 : reg n759 ra = v673 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n759 sp = F := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n759 (3 : Fin 32) = G3 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n759 (4 : Fin 32) = G4 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n759 (5 : Fin 32) = v734 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n759 (6 : Fin 32) = v699 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n759 (7 : Fin 32) = v741 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n759 (8 : Fin 32) = v697 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n759 (9 : Fin 32) = v742 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n759 a0 = v642 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n759 a1 = v754 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n759 a2 = v743 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n759 a3 = v757 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n759 a4 = v753 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n759 a5 = v759 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n759 a6 = v745 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n759 a7 = v712 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n759 (18 : Fin 32) = v705 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n759 (19 : Fin 32) = v593 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n759 (20 : Fin 32) = v722 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n759 (21 : Fin 32) = v485 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n759 (22 : Fin 32) = v557 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n759 (23 : Fin 32) = v302 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n759 (24 : Fin 32) = v150 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n759 (25 : Fin 32) = v174 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n759 (26 : Fin 32) = v726 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n759 (27 : Fin 32) = v700 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n759 (28 : Fin 32) = v7 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n759 (29 : Fin 32) = v638 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n759 (30 : Fin 32) = v133 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n759 (31 : Fin 32) = v704 := by rw [u759.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have so14 : memLoad32 Mi (F + 0x14) = v671 := by
    rw [sl14]
  have so18 : memLoad32 Mi (F + 0x18) = v660 := by
    rw [sl18]
  have so1C : memLoad32 Mi (F + 0x1C) = v658 := by
    rw [sl1C]
  have so28 : memLoad32 Mi (F + 0x28) = v651 := by
    rw [sl28]
  have so2C : memLoad32 Mi (F + 0x2C) = v649 := by
    rw [sl2C]
  have so30 : memLoad32 Mi (F + 0x30) = v687 := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = v654 := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = v656 := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = v685 := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = v665 := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = v662 := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = v647 := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = v678 := by
    rw [sl4C]
  have so50 : memLoad32 Mi (F + 0x50) = v676 := by
    rw [sl50]
  have so54 : memLoad32 Mi (F + 0x54) = v645 := by
    rw [sl54]
  have so58 : memLoad32 Mi (F + 0x58) = v708 := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = v706 := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = v680 := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = v682 := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = v689 := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = v691 := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = v669 := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = v667 := by
    rw [sl74]
  have so78 : memLoad32 Mi (F + 0x78) = v545 := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = v717 := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = v715 := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = v572 := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = v695 := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = v559 := by
    rw [sl8C]
  have so94 : memLoad32 Mi (F + 0x94) = v481 := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = v352 := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = v713 := by
    rw [sl9C]
  have soA4 : memLoad32 Mi (F + 0xA4) = v357 := by
    rw [slA4]
  have soA8 : memLoad32 Mi (F + 0xA8) = v279 := by
    rw [slA8]
  have soAC : memLoad32 Mi (F + 0xAC) = v219 := by
    rw [slAC]
  have soB0 : memLoad32 Mi (F + 0xB0) = v693 := by
    rw [slB0]
  have soB4 : memLoad32 Mi (F + 0xB4) = v582 := by
    rw [slB4]
  have soBC : memLoad32 Mi (F + 0xBC) = v467 := by
    rw [slBC]
  have soC0 : memLoad32 Mi (F + 0xC0) = v405 := by
    rw [slC0]
  have soC4 : memLoad32 Mi (F + 0xC4) = v199 := by
    rw [slC4]
  have soC8 : memLoad32 Mi (F + 0xC8) = v335 := by
    rw [slC8]
  have soCC : memLoad32 Mi (F + 0xCC) = v264 := by
    rw [slCC]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  have soD4 : memLoad32 Mi (F + 0xD4) = v239 := by
    rw [slD4]
  have soE8 : memLoad32 Mi (F + 0xE8) = v419 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v341 := by
    rw [slEC]
  have soF0 : memLoad32 Mi (F + 0xF0) = v206 := by
    rw [slF0]
  have soF4 : memLoad32 Mi (F + 0xF4) = v297 := by
    rw [slF4]
  have soF8 : memLoad32 Mi (F + 0xF8) = v284 := by
    rw [slF8]
  have soFC : memLoad32 Mi (F + 0xFC) = v579 := by
    rw [slFC]
  have so100 : memLoad32 Mi (F + 0x100) = v540 := by
    rw [sl100]
  have so104 : memLoad32 Mi (F + 0x104) = v710 := by
    rw [sl104]
  have so108 : memLoad32 Mi (F + 0x108) = v203 := by
    rw [sl108]
  have so10C : memLoad32 Mi (F + 0x10C) = v274 := by
    rw [sl10C]
  have so110 : memLoad32 Mi (F + 0x110) = v702 := by
    rw [sl110]
  have so11C : memLoad32 Mi (F + 0x11C) = v231 := by
    rw [sl11C]
  have so120 : memLoad32 Mi (F + 0x120) = v116 := by
    rw [sl120]
  have so124 : memLoad32 Mi (F + 0x124) = v124 := by
    rw [sl124]
  exact ⟨n759, Mi, v720, v722, v724, v725, v726, v727, v728, v729, v730, v731, v732, v733, v734, v735, v736, v737, v738, v740, v741, v742, v743, v744, v745, v747, v748, v750, v752, v753, v754, v755, v757, v759, (.cons d720 (.cons d721 (.cons d722 (.cons d723 (.cons d724 (.cons d725 (.cons d726 (.cons d727 (.cons d728 (.cons d729 (.cons d730 (.cons d731 (.cons d732 (.cons d733 (.cons d734 (.cons d735 (.cons d736 (.cons d737 (.cons d738 (.cons d739 (.cons d740 (.cons d741 (.cons d742 (.cons d743 (.cons d744 (.cons d745 (.cons d746 (.cons d747 (.cons d748 (.cons d749 (.cons d750 (.cons d751 (.cons d752 (.cons d753 (.cons d754 (.cons d755 (.cons d756 (.cons d757 (.cons d758 (.single d759)))))))))))))))))))))))))))))))))))))))), u759.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so14, so18, so1C, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so94, so98, so9C, soA4, soA8, soAC, soB0, soB4, soBC, soC0, soC4, soC8, soCC, soD0, soD4, soE8, soEC, soF0, soF4, soF8, soFC, so100, so104, so108, so10C, so110, so11C, so120, so124, hv720, hv722, hv724, hv725, hv726, hv727, hv728, hv729, hv730, hv731, hv732, hv733, hv734, hv735, hv736, hv737, hv738, hv740, hv741, hv742, hv743, hv744, hv745, hv747, hv748, hv750, hv752, hv753, hv754, hv755, hv757, hv759⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g25 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v116 v124 v133 v150 v174 v199 v203 v206 v219 v231 v239 v264 v274 v279 v284 v297 v302 v335 v341 v352 v357 v405 v419 v467 v481 v485 v540 v545 v557 v559 v572 v579 v582 v593 v638 v642 v645 v647 v649 v651 v654 v656 v658 v660 v662 v665 v667 v669 v671 v673 v676 v678 v680 v682 v685 v687 v689 v691 v693 v695 v697 v699 v700 v702 v704 v705 v706 v708 v710 v712 v713 v715 v717 v722 v726 v734 v741 v742 v743 v745 v753 v754 v757 v759 : Word}
    (s : St Mi B n 0xAC4 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v673)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v734)
    (q6 : reg n (6 : Fin 32) = v699)
    (q7 : reg n (7 : Fin 32) = v741)
    (q8 : reg n (8 : Fin 32) = v697)
    (q9 : reg n (9 : Fin 32) = v742)
    (q10 : reg n a0 = v642)
    (q11 : reg n a1 = v754)
    (q12 : reg n a2 = v743)
    (q13 : reg n a3 = v757)
    (q14 : reg n a4 = v753)
    (q15 : reg n a5 = v759)
    (q16 : reg n a6 = v745)
    (q17 : reg n a7 = v712)
    (q18 : reg n (18 : Fin 32) = v705)
    (q19 : reg n (19 : Fin 32) = v593)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v150)
    (q25 : reg n (25 : Fin 32) = v174)
    (q26 : reg n (26 : Fin 32) = v726)
    (q27 : reg n (27 : Fin 32) = v700)
    (q28 : reg n (28 : Fin 32) = v7)
    (q29 : reg n (29 : Fin 32) = v638)
    (q30 : reg n (30 : Fin 32) = v133)
    (q31 : reg n (31 : Fin 32) = v704)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl14 : memLoad32 Mi (F + 0x14) = v671)
    (sl18 : memLoad32 Mi (F + 0x18) = v660)
    (sl1C : memLoad32 Mi (F + 0x1C) = v658)
    (sl28 : memLoad32 Mi (F + 0x28) = v651)
    (sl2C : memLoad32 Mi (F + 0x2C) = v649)
    (sl30 : memLoad32 Mi (F + 0x30) = v687)
    (sl34 : memLoad32 Mi (F + 0x34) = v654)
    (sl38 : memLoad32 Mi (F + 0x38) = v656)
    (sl3C : memLoad32 Mi (F + 0x3C) = v685)
    (sl40 : memLoad32 Mi (F + 0x40) = v665)
    (sl44 : memLoad32 Mi (F + 0x44) = v662)
    (sl48 : memLoad32 Mi (F + 0x48) = v647)
    (sl4C : memLoad32 Mi (F + 0x4C) = v678)
    (sl50 : memLoad32 Mi (F + 0x50) = v676)
    (sl54 : memLoad32 Mi (F + 0x54) = v645)
    (sl58 : memLoad32 Mi (F + 0x58) = v708)
    (sl5C : memLoad32 Mi (F + 0x5C) = v706)
    (sl60 : memLoad32 Mi (F + 0x60) = v680)
    (sl64 : memLoad32 Mi (F + 0x64) = v682)
    (sl68 : memLoad32 Mi (F + 0x68) = v689)
    (sl6C : memLoad32 Mi (F + 0x6C) = v691)
    (sl70 : memLoad32 Mi (F + 0x70) = v669)
    (sl74 : memLoad32 Mi (F + 0x74) = v667)
    (sl78 : memLoad32 Mi (F + 0x78) = v545)
    (sl7C : memLoad32 Mi (F + 0x7C) = v717)
    (sl80 : memLoad32 Mi (F + 0x80) = v715)
    (sl84 : memLoad32 Mi (F + 0x84) = v572)
    (sl88 : memLoad32 Mi (F + 0x88) = v695)
    (sl8C : memLoad32 Mi (F + 0x8C) = v559)
    (sl94 : memLoad32 Mi (F + 0x94) = v481)
    (sl98 : memLoad32 Mi (F + 0x98) = v352)
    (sl9C : memLoad32 Mi (F + 0x9C) = v713)
    (slA4 : memLoad32 Mi (F + 0xA4) = v357)
    (slA8 : memLoad32 Mi (F + 0xA8) = v279)
    (slAC : memLoad32 Mi (F + 0xAC) = v219)
    (slB0 : memLoad32 Mi (F + 0xB0) = v693)
    (slB4 : memLoad32 Mi (F + 0xB4) = v582)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slD4 : memLoad32 Mi (F + 0xD4) = v239)
    (slE8 : memLoad32 Mi (F + 0xE8) = v419)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slF4 : memLoad32 Mi (F + 0xF4) = v297)
    (slF8 : memLoad32 Mi (F + 0xF8) = v284)
    (slFC : memLoad32 Mi (F + 0xFC) = v579)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v710)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v760 v761 v763 v765 v766 v767 v768 v770 v771 v772 v775 v777 v778 v780 v781 v782 v784 v785 v786 v787 v789 v790 v792 v793 v794 v795 v796 v797 v798 v799 : Word),
      Steps n n' ∧
      St M' B n' 0xB34 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v734 ∧
      reg n' (6 : Fin 32) = v797 ∧
      reg n' (7 : Fin 32) = v741 ∧
      reg n' (8 : Fin 32) = v782 ∧
      reg n' (9 : Fin 32) = v239 ∧
      reg n' a0 = v799 ∧
      reg n' a1 = v795 ∧
      reg n' a2 = v777 ∧
      reg n' a3 = v792 ∧
      reg n' a4 = v794 ∧
      reg n' a5 = v796 ∧
      reg n' a6 = v745 ∧
      reg n' a7 = v786 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v593 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v150 ∧
      reg n' (25 : Fin 32) = v174 ∧
      reg n' (26 : Fin 32) = v726 ∧
      reg n' (27 : Fin 32) = v765 ∧
      reg n' (28 : Fin 32) = v798 ∧
      reg n' (29 : Fin 32) = v785 ∧
      reg n' (30 : Fin 32) = v133 ∧
      reg n' (31 : Fin 32) = v704 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x30) = v687 ∧
      memLoad32 M' (F + 0x34) = v654 ∧
      memLoad32 M' (F + 0x38) = v656 ∧
      memLoad32 M' (F + 0x3C) = v685 ∧
      memLoad32 M' (F + 0x40) = v665 ∧
      memLoad32 M' (F + 0x44) = v662 ∧
      memLoad32 M' (F + 0x48) = v647 ∧
      memLoad32 M' (F + 0x4C) = v678 ∧
      memLoad32 M' (F + 0x50) = v676 ∧
      memLoad32 M' (F + 0x54) = v645 ∧
      memLoad32 M' (F + 0x58) = v708 ∧
      memLoad32 M' (F + 0x5C) = v706 ∧
      memLoad32 M' (F + 0x60) = v680 ∧
      memLoad32 M' (F + 0x64) = v682 ∧
      memLoad32 M' (F + 0x68) = v689 ∧
      memLoad32 M' (F + 0x6C) = v691 ∧
      memLoad32 M' (F + 0x70) = v669 ∧
      memLoad32 M' (F + 0x74) = v667 ∧
      memLoad32 M' (F + 0x78) = v545 ∧
      memLoad32 M' (F + 0x7C) = v717 ∧
      memLoad32 M' (F + 0x80) = v715 ∧
      memLoad32 M' (F + 0x84) = v572 ∧
      memLoad32 M' (F + 0x88) = v695 ∧
      memLoad32 M' (F + 0x8C) = v559 ∧
      memLoad32 M' (F + 0x94) = v481 ∧
      memLoad32 M' (F + 0x98) = v352 ∧
      memLoad32 M' (F + 0x9C) = v713 ∧
      memLoad32 M' (F + 0xA8) = v279 ∧
      memLoad32 M' (F + 0xAC) = v219 ∧
      memLoad32 M' (F + 0xB0) = v693 ∧
      memLoad32 M' (F + 0xB4) = v582 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xCC) = v264 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xF4) = v297 ∧
      memLoad32 M' (F + 0xF8) = v284 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x104) = v710 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .add v754 v757 = v760 ∧
      aluEval .sltu v759 v753 = v761 ∧
      aluEval .add v761 v658 = v763 ∧
      aluEval .add v660 v759 = v765 ∧
      aluEval .add v760 v763 = v766 ∧
      aluEval .sltu v765 v759 = v767 ∧
      aluEval .add v767 v673 = v768 ∧
      aluEval .add v671 v765 = v770 ∧
      aluEval .add v766 v768 = v771 ∧
      aluEval .sltu v770 v765 = v772 ∧
      aluEval .add v772 v651 = v775 ∧
      aluEval .add 0 0x14D = v777 ∧
      aluEval .mul v419 v777 = v778 ∧
      aluEval .add v649 v770 = v780 ∧
      aluEval .mul v485 v302 = v781 ∧
      aluEval .sltu v780 v770 = v782 ∧
      aluEval .mul v557 v239 = v784 ∧
      aluEval .mulhu v419 v777 = v785 ∧
      aluEval .mul v722 v174 = v786 ∧
      aluEval .add v771 v775 = v787 ∧
      aluEval .sub v782 v357 = v789 ∧
      aluEval .add v787 v789 = v790 ∧
      aluEval .sub v780 v341 = v792 ∧
      aluEval .sltu v780 v341 = v793 ∧
      aluEval .add v778 v792 = v794 ∧
      aluEval .sub v790 v793 = v795 ∧
      aluEval .add v794 v781 = v796 ∧
      aluEval .add v784 v796 = v797 ∧
      aluEval .mulhu v485 v302 = v798 ∧
      aluEval .add v795 v785 = v799 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n760, v760, d760, hv760, u760⟩ := s.aluG hc ev_at_ac4 (off' := 0xAC6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv760
  obtain ⟨n761, v761, d761, hv761, u761⟩ := u760.aluG hc ev_at_ac6 (off' := 0xACA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv761
  obtain ⟨n762, d762, u762⟩ := u761.lwE hc ev_at_aca (off' := 0xACC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 28) (by decide)) (v := v658)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl1C])
  obtain ⟨n763, v763, d763, hv763, u763⟩ := u762.aluG hc ev_at_acc (off' := 0xACE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv763
  obtain ⟨n764, d764, u764⟩ := u763.lwE hc ev_at_ace (off' := 0xAD0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 24) (by decide)) (v := v660)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl18])
  obtain ⟨n765, v765, d765, hv765, u765⟩ := u764.aluG hc ev_at_ad0 (off' := 0xAD2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv765
  obtain ⟨n766, v766, d766, hv766, u766⟩ := u765.aluG hc ev_at_ad2 (off' := 0xAD4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv766
  obtain ⟨n767, v767, d767, hv767, u767⟩ := u766.aluG hc ev_at_ad4 (off' := 0xAD8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv767
  obtain ⟨n768, v768, d768, hv768, u768⟩ := u767.aluG hc ev_at_ad8 (off' := 0xADA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv768
  obtain ⟨n769, d769, u769⟩ := u768.lwE hc ev_at_ada (off' := 0xADC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 20) (by decide)) (v := v671)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl14])
  obtain ⟨n770, v770, d770, hv770, u770⟩ := u769.aluG hc ev_at_adc (off' := 0xADE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv770
  obtain ⟨n771, v771, d771, hv771, u771⟩ := u770.aluG hc ev_at_ade (off' := 0xAE0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv771
  obtain ⟨n772, v772, d772, hv772, u772⟩ := u771.aluG hc ev_at_ae0 (off' := 0xAE4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv772
  obtain ⟨n773, d773, u773⟩ := u772.aluE hc ev_at_ae4 (off' := 0xAE6) (by decide) (v := v7)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n774, d774, u774⟩ := u773.lwE hc ev_at_ae6 (off' := 0xAE8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 40) (by decide)) (v := v651)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl28])
  obtain ⟨n775, v775, d775, hv775, u775⟩ := u774.aluG hc ev_at_ae8 (off' := 0xAEA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv775
  obtain ⟨n776, d776, u776⟩ := u775.lwE hc ev_at_aea (off' := 0xAEC) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 232) (by decide)) (v := v419)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slE8])
  obtain ⟨n777, v777, d777, hv777, u777⟩ := u776.aluImmG hc ev_at_aec (off' := 0xAF0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv777
  obtain ⟨n778, v778, d778, hv778, u778⟩ := u777.aluG hc ev_at_af0 (off' := 0xAF4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv778
  obtain ⟨n779, d779, u779⟩ := u778.lwE hc ev_at_af4 (off' := 0xAF6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 44) (by decide)) (v := v649)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl2C])
  obtain ⟨n780, v780, d780, hv780, u780⟩ := u779.aluG hc ev_at_af6 (off' := 0xAF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv780
  obtain ⟨n781, v781, d781, hv781, u781⟩ := u780.aluG hc ev_at_af8 (off' := 0xAFC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv781
  obtain ⟨n782, v782, d782, hv782, u782⟩ := u781.aluG hc ev_at_afc (off' := 0xB00) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv782
  obtain ⟨n783, d783, u783⟩ := u782.lwE hc ev_at_b00 (off' := 0xB02) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 212) (by decide)) (v := v239)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slD4])
  obtain ⟨n784, v784, d784, hv784, u784⟩ := u783.aluG hc ev_at_b02 (off' := 0xB06) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv784
  obtain ⟨n785, v785, d785, hv785, u785⟩ := u784.aluG hc ev_at_b06 (off' := 0xB0A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv785
  obtain ⟨n786, v786, d786, hv786, u786⟩ := u785.aluG hc ev_at_b0a (off' := 0xB0E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv786
  obtain ⟨n787, v787, d787, hv787, u787⟩ := u786.aluG hc ev_at_b0e (off' := 0xB10) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv787
  obtain ⟨n788, d788, u788⟩ := u787.lwE hc ev_at_b10 (off' := 0xB12) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 164) (by decide)) (v := v357)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slA4])
  obtain ⟨n789, v789, d789, hv789, u789⟩ := u788.aluG hc ev_at_b12 (off' := 0xB16) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv789
  obtain ⟨n790, v790, d790, hv790, u790⟩ := u789.aluG hc ev_at_b16 (off' := 0xB18) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv790
  obtain ⟨n791, d791, u791⟩ := u790.lwE hc ev_at_b18 (off' := 0xB1A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 236) (by decide)) (v := v341)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slEC])
  obtain ⟨n792, v792, d792, hv792, u792⟩ := u791.aluG hc ev_at_b1a (off' := 0xB1E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv792
  obtain ⟨n793, v793, d793, hv793, u793⟩ := u792.aluG hc ev_at_b1e (off' := 0xB22) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv793
  obtain ⟨n794, v794, d794, hv794, u794⟩ := u793.aluG hc ev_at_b22 (off' := 0xB24) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv794
  obtain ⟨n795, v795, d795, hv795, u795⟩ := u794.aluG hc ev_at_b24 (off' := 0xB26) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv795
  obtain ⟨n796, v796, d796, hv796, u796⟩ := u795.aluG hc ev_at_b26 (off' := 0xB2A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv796
  obtain ⟨n797, v797, d797, hv797, u797⟩ := u796.aluG hc ev_at_b2a (off' := 0xB2C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv797
  obtain ⟨n798, v798, d798, hv798, u798⟩ := u797.aluG hc ev_at_b2c (off' := 0xB30) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv798
  obtain ⟨n799, v799, d799, hv799, u799⟩ := u798.aluG hc ev_at_b30 (off' := 0xB34) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv799
  have qo1 : reg n799 ra = v357 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n799 sp = F := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n799 (3 : Fin 32) = G3 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n799 (4 : Fin 32) = G4 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n799 (5 : Fin 32) = v734 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n799 (6 : Fin 32) = v797 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n799 (7 : Fin 32) = v741 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n799 (8 : Fin 32) = v782 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n799 (9 : Fin 32) = v239 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n799 a0 = v799 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n799 a1 = v795 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n799 a2 = v777 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n799 a3 = v792 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n799 a4 = v794 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n799 a5 = v796 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n799 a6 = v745 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n799 a7 = v786 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n799 (18 : Fin 32) = v7 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n799 (19 : Fin 32) = v593 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n799 (20 : Fin 32) = v722 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n799 (21 : Fin 32) = v485 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n799 (22 : Fin 32) = v557 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n799 (23 : Fin 32) = v302 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n799 (24 : Fin 32) = v150 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n799 (25 : Fin 32) = v174 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n799 (26 : Fin 32) = v726 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n799 (27 : Fin 32) = v765 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n799 (28 : Fin 32) = v798 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n799 (29 : Fin 32) = v785 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n799 (30 : Fin 32) = v133 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n799 (31 : Fin 32) = v704 := by rw [u799.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have so30 : memLoad32 Mi (F + 0x30) = v687 := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = v654 := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = v656 := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = v685 := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = v665 := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = v662 := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = v647 := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = v678 := by
    rw [sl4C]
  have so50 : memLoad32 Mi (F + 0x50) = v676 := by
    rw [sl50]
  have so54 : memLoad32 Mi (F + 0x54) = v645 := by
    rw [sl54]
  have so58 : memLoad32 Mi (F + 0x58) = v708 := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = v706 := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = v680 := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = v682 := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = v689 := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = v691 := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = v669 := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = v667 := by
    rw [sl74]
  have so78 : memLoad32 Mi (F + 0x78) = v545 := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = v717 := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = v715 := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = v572 := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = v695 := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = v559 := by
    rw [sl8C]
  have so94 : memLoad32 Mi (F + 0x94) = v481 := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = v352 := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = v713 := by
    rw [sl9C]
  have soA8 : memLoad32 Mi (F + 0xA8) = v279 := by
    rw [slA8]
  have soAC : memLoad32 Mi (F + 0xAC) = v219 := by
    rw [slAC]
  have soB0 : memLoad32 Mi (F + 0xB0) = v693 := by
    rw [slB0]
  have soB4 : memLoad32 Mi (F + 0xB4) = v582 := by
    rw [slB4]
  have soBC : memLoad32 Mi (F + 0xBC) = v467 := by
    rw [slBC]
  have soC0 : memLoad32 Mi (F + 0xC0) = v405 := by
    rw [slC0]
  have soC4 : memLoad32 Mi (F + 0xC4) = v199 := by
    rw [slC4]
  have soC8 : memLoad32 Mi (F + 0xC8) = v335 := by
    rw [slC8]
  have soCC : memLoad32 Mi (F + 0xCC) = v264 := by
    rw [slCC]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  have soE8 : memLoad32 Mi (F + 0xE8) = v419 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v341 := by
    rw [slEC]
  have soF0 : memLoad32 Mi (F + 0xF0) = v206 := by
    rw [slF0]
  have soF4 : memLoad32 Mi (F + 0xF4) = v297 := by
    rw [slF4]
  have soF8 : memLoad32 Mi (F + 0xF8) = v284 := by
    rw [slF8]
  have soFC : memLoad32 Mi (F + 0xFC) = v579 := by
    rw [slFC]
  have so100 : memLoad32 Mi (F + 0x100) = v540 := by
    rw [sl100]
  have so104 : memLoad32 Mi (F + 0x104) = v710 := by
    rw [sl104]
  have so108 : memLoad32 Mi (F + 0x108) = v203 := by
    rw [sl108]
  have so10C : memLoad32 Mi (F + 0x10C) = v274 := by
    rw [sl10C]
  have so110 : memLoad32 Mi (F + 0x110) = v702 := by
    rw [sl110]
  have so11C : memLoad32 Mi (F + 0x11C) = v231 := by
    rw [sl11C]
  have so120 : memLoad32 Mi (F + 0x120) = v116 := by
    rw [sl120]
  have so124 : memLoad32 Mi (F + 0x124) = v124 := by
    rw [sl124]
  exact ⟨n799, Mi, v760, v761, v763, v765, v766, v767, v768, v770, v771, v772, v775, v777, v778, v780, v781, v782, v784, v785, v786, v787, v789, v790, v792, v793, v794, v795, v796, v797, v798, v799, (.cons d760 (.cons d761 (.cons d762 (.cons d763 (.cons d764 (.cons d765 (.cons d766 (.cons d767 (.cons d768 (.cons d769 (.cons d770 (.cons d771 (.cons d772 (.cons d773 (.cons d774 (.cons d775 (.cons d776 (.cons d777 (.cons d778 (.cons d779 (.cons d780 (.cons d781 (.cons d782 (.cons d783 (.cons d784 (.cons d785 (.cons d786 (.cons d787 (.cons d788 (.cons d789 (.cons d790 (.cons d791 (.cons d792 (.cons d793 (.cons d794 (.cons d795 (.cons d796 (.cons d797 (.cons d798 (.single d799)))))))))))))))))))))))))))))))))))))))), u799.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so94, so98, so9C, soA8, soAC, soB0, soB4, soBC, soC0, soC4, soC8, soCC, soD0, soE8, soEC, soF0, soF4, soF8, soFC, so100, so104, so108, so10C, so110, so11C, so120, so124, hv760, hv761, hv763, hv765, hv766, hv767, hv768, hv770, hv771, hv772, hv775, hv777, hv778, hv780, hv781, hv782, hv784, hv785, hv786, hv787, hv789, hv790, hv792, hv793, hv794, hv795, hv796, hv797, hv798, hv799⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g26 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v116 v124 v133 v150 v174 v199 v203 v206 v219 v231 v239 v264 v274 v279 v284 v297 v302 v335 v341 v352 v357 v405 v419 v467 v481 v485 v540 v545 v557 v559 v572 v579 v582 v593 v645 v647 v654 v656 v662 v665 v667 v669 v676 v678 v680 v682 v685 v687 v689 v691 v693 v695 v702 v704 v706 v708 v710 v713 v715 v717 v722 v726 v734 v741 v745 v765 v777 v782 v785 v786 v792 v794 v795 v796 v797 v798 v799 : Word}
    (s : St Mi B n 0xB34 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v734)
    (q6 : reg n (6 : Fin 32) = v797)
    (q7 : reg n (7 : Fin 32) = v741)
    (q8 : reg n (8 : Fin 32) = v782)
    (q9 : reg n (9 : Fin 32) = v239)
    (q10 : reg n a0 = v799)
    (q11 : reg n a1 = v795)
    (q12 : reg n a2 = v777)
    (q13 : reg n a3 = v792)
    (q14 : reg n a4 = v794)
    (q15 : reg n a5 = v796)
    (q16 : reg n a6 = v745)
    (q17 : reg n a7 = v786)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v593)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v150)
    (q25 : reg n (25 : Fin 32) = v174)
    (q26 : reg n (26 : Fin 32) = v726)
    (q27 : reg n (27 : Fin 32) = v765)
    (q28 : reg n (28 : Fin 32) = v798)
    (q29 : reg n (29 : Fin 32) = v785)
    (q30 : reg n (30 : Fin 32) = v133)
    (q31 : reg n (31 : Fin 32) = v704)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl30 : memLoad32 Mi (F + 0x30) = v687)
    (sl34 : memLoad32 Mi (F + 0x34) = v654)
    (sl38 : memLoad32 Mi (F + 0x38) = v656)
    (sl3C : memLoad32 Mi (F + 0x3C) = v685)
    (sl40 : memLoad32 Mi (F + 0x40) = v665)
    (sl44 : memLoad32 Mi (F + 0x44) = v662)
    (sl48 : memLoad32 Mi (F + 0x48) = v647)
    (sl4C : memLoad32 Mi (F + 0x4C) = v678)
    (sl50 : memLoad32 Mi (F + 0x50) = v676)
    (sl54 : memLoad32 Mi (F + 0x54) = v645)
    (sl58 : memLoad32 Mi (F + 0x58) = v708)
    (sl5C : memLoad32 Mi (F + 0x5C) = v706)
    (sl60 : memLoad32 Mi (F + 0x60) = v680)
    (sl64 : memLoad32 Mi (F + 0x64) = v682)
    (sl68 : memLoad32 Mi (F + 0x68) = v689)
    (sl6C : memLoad32 Mi (F + 0x6C) = v691)
    (sl70 : memLoad32 Mi (F + 0x70) = v669)
    (sl74 : memLoad32 Mi (F + 0x74) = v667)
    (sl78 : memLoad32 Mi (F + 0x78) = v545)
    (sl7C : memLoad32 Mi (F + 0x7C) = v717)
    (sl80 : memLoad32 Mi (F + 0x80) = v715)
    (sl84 : memLoad32 Mi (F + 0x84) = v572)
    (sl88 : memLoad32 Mi (F + 0x88) = v695)
    (sl8C : memLoad32 Mi (F + 0x8C) = v559)
    (sl94 : memLoad32 Mi (F + 0x94) = v481)
    (sl98 : memLoad32 Mi (F + 0x98) = v352)
    (sl9C : memLoad32 Mi (F + 0x9C) = v713)
    (slA8 : memLoad32 Mi (F + 0xA8) = v279)
    (slAC : memLoad32 Mi (F + 0xAC) = v219)
    (slB0 : memLoad32 Mi (F + 0xB0) = v693)
    (slB4 : memLoad32 Mi (F + 0xB4) = v582)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE8 : memLoad32 Mi (F + 0xE8) = v419)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slF4 : memLoad32 Mi (F + 0xF4) = v297)
    (slF8 : memLoad32 Mi (F + 0xF8) = v284)
    (slFC : memLoad32 Mi (F + 0xFC) = v579)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v710)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v800 v801 v802 v803 v805 v807 v808 v809 v810 v811 v812 v813 v815 v816 v817 v818 v819 v820 v821 v823 v824 v825 v826 v827 v828 v829 v830 v831 v832 v833 v836 v838 v839 : Word),
      Steps n n' ∧
      St M' B n' 0xBAE (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v831 ∧
      reg n' (6 : Fin 32) = v797 ∧
      reg n' (7 : Fin 32) = v741 ∧
      reg n' (8 : Fin 32) = v816 ∧
      reg n' (9 : Fin 32) = v297 ∧
      reg n' a0 = v116 ∧
      reg n' a1 = v656 ∧
      reg n' a2 = v833 ∧
      reg n' a3 = v838 ∧
      reg n' a4 = v839 ∧
      reg n' a5 = v821 ∧
      reg n' a6 = v802 ∧
      reg n' a7 = v805 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v593 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v150 ∧
      reg n' (25 : Fin 32) = v174 ∧
      reg n' (26 : Fin 32) = v801 ∧
      reg n' (27 : Fin 32) = v765 ∧
      reg n' (28 : Fin 32) = v823 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v239 ∧
      reg n' (31 : Fin 32) = v704 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x30) = v687 ∧
      memLoad32 M' (F + 0x3C) = v685 ∧
      memLoad32 M' (F + 0x40) = v665 ∧
      memLoad32 M' (F + 0x44) = v662 ∧
      memLoad32 M' (F + 0x48) = v647 ∧
      memLoad32 M' (F + 0x4C) = v678 ∧
      memLoad32 M' (F + 0x50) = v676 ∧
      memLoad32 M' (F + 0x54) = v645 ∧
      memLoad32 M' (F + 0x58) = v708 ∧
      memLoad32 M' (F + 0x5C) = v706 ∧
      memLoad32 M' (F + 0x60) = v680 ∧
      memLoad32 M' (F + 0x64) = v682 ∧
      memLoad32 M' (F + 0x68) = v689 ∧
      memLoad32 M' (F + 0x6C) = v691 ∧
      memLoad32 M' (F + 0x70) = v669 ∧
      memLoad32 M' (F + 0x74) = v667 ∧
      memLoad32 M' (F + 0x78) = v545 ∧
      memLoad32 M' (F + 0x7C) = v717 ∧
      memLoad32 M' (F + 0x80) = v715 ∧
      memLoad32 M' (F + 0x84) = v572 ∧
      memLoad32 M' (F + 0x88) = v695 ∧
      memLoad32 M' (F + 0x8C) = v559 ∧
      memLoad32 M' (F + 0x94) = v481 ∧
      memLoad32 M' (F + 0x98) = v352 ∧
      memLoad32 M' (F + 0x9C) = v713 ∧
      memLoad32 M' (F + 0xA8) = v279 ∧
      memLoad32 M' (F + 0xAC) = v219 ∧
      memLoad32 M' (F + 0xB0) = v693 ∧
      memLoad32 M' (F + 0xB4) = v582 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xCC) = v264 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x104) = v710 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x118) = v803 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .add v797 v786 = v800 ∧
      aluEval .add v726 v704 = v801 ∧
      aluEval .add v745 v800 = v802 ∧
      aluEval .mul v802 v133 = v803 ∧
      aluEval .mulhu v557 v239 = v805 ∧
      aluEval .sltu v801 v704 = v807 ∧
      aluEval .sltu v794 v792 = v808 ∧
      aluEval .add v734 v807 = v809 ∧
      aluEval .add v799 v808 = v810 ∧
      aluEval .add v810 v798 = v811 ∧
      aluEval .mulhu v722 v174 = v812 ∧
      aluEval .sltu v796 v794 = v813 ∧
      aluEval .sltu v801 v297 = v815 ∧
      aluEval .sub v809 v815 = v816 ∧
      aluEval .add v811 v813 = v817 ∧
      aluEval .add v817 v805 = v818 ∧
      aluEval .and v803 v7 = v819 ∧
      aluEval .sltu v797 v796 = v820 ∧
      aluEval .mulhu v819 v150 = v821 ∧
      aluEval .sub v816 v284 = v823 ∧
      aluEval .add v818 v820 = v824 ∧
      aluEval .add v824 v812 = v825 ∧
      aluEval .sltu v800 v797 = v826 ∧
      aluEval .add v825 v826 = v827 ∧
      aluEval .srl v741 0x1D = v828 ∧
      aluEval .add v828 v827 = v829 ∧
      aluEval .sltu v802 v800 = v830 ∧
      aluEval .sub v801 v297 = v831 ∧
      aluEval .add v830 v829 = v832 ∧
      aluEval .add v832 v821 = v833 ∧
      aluEval .sltu v654 v116 = v836 ∧
      aluEval .sub v656 v836 = v838 ∧
      aluEval .sub v654 v116 = v839 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n800, v800, d800, hv800, u800⟩ := s.aluG hc ev_at_b34 (off' := 0xB38) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv800
  obtain ⟨n801, v801, d801, hv801, u801⟩ := u800.aluG hc ev_at_b38 (off' := 0xB3A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv801
  obtain ⟨n802, v802, d802, hv802, u802⟩ := u801.aluG hc ev_at_b3a (off' := 0xB3C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv802
  obtain ⟨n803, v803, d803, hv803, u803⟩ := u802.aluG hc ev_at_b3c (off' := 0xB40) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv803
  obtain ⟨n804, d804, u804⟩ := u803.swG hc ev_at_b40 (off' := 0xB44) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 280) (by decide)) (a := F + 0x118) (v := v803)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm804, hM804⟩ : ∃ M', memStore32 Mi (F + 0x118) v803 = M' := ⟨_, rfl⟩
  rw [hM804] at u804
  have hc804 : CodeIn Mm804 B ed25519VerifyCode := by rw [← hM804]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr804 : ∀ x, Sep F 0x128 x 1 → Mm804 x = M0 x := fun x hx => by
    rw [← hM804, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n805, v805, d805, hv805, u805⟩ := u804.aluG hc804 ev_at_b44 (off' := 0xB48) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv805
  obtain ⟨n806, d806, u806⟩ := u805.aluE hc804 ev_at_b48 (off' := 0xB4A) (by decide) (v := v239)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n807, v807, d807, hv807, u807⟩ := u806.aluG hc804 ev_at_b4a (off' := 0xB4E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv807
  obtain ⟨n808, v808, d808, hv808, u808⟩ := u807.aluG hc804 ev_at_b4e (off' := 0xB52) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv808
  obtain ⟨n809, v809, d809, hv809, u809⟩ := u808.aluG hc804 ev_at_b52 (off' := 0xB54) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv809
  obtain ⟨n810, v810, d810, hv810, u810⟩ := u809.aluG hc804 ev_at_b54 (off' := 0xB56) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv810
  obtain ⟨n811, v811, d811, hv811, u811⟩ := u810.aluG hc804 ev_at_b56 (off' := 0xB58) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv811
  obtain ⟨n812, v812, d812, hv812, u812⟩ := u811.aluG hc804 ev_at_b58 (off' := 0xB5C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv812
  obtain ⟨n813, v813, d813, hv813, u813⟩ := u812.aluG hc804 ev_at_b5c (off' := 0xB60) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv813
  obtain ⟨n814, d814, u814⟩ := u813.lwE hc804 ev_at_b60 (off' := 0xB62) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 244) (by decide)) (v := v297)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xF4) 4 from sep_offsets F (c := 280) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), slF4])
  obtain ⟨n815, v815, d815, hv815, u815⟩ := u814.aluG hc804 ev_at_b62 (off' := 0xB66) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv815
  obtain ⟨n816, v816, d816, hv816, u816⟩ := u815.aluG hc804 ev_at_b66 (off' := 0xB6A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv816
  obtain ⟨n817, v817, d817, hv817, u817⟩ := u816.aluG hc804 ev_at_b6a (off' := 0xB6C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv817
  obtain ⟨n818, v818, d818, hv818, u818⟩ := u817.aluG hc804 ev_at_b6c (off' := 0xB6E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv818
  obtain ⟨n819, v819, d819, hv819, u819⟩ := u818.aluG hc804 ev_at_b6e (off' := 0xB72) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv819
  obtain ⟨n820, v820, d820, hv820, u820⟩ := u819.aluG hc804 ev_at_b72 (off' := 0xB76) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv820
  obtain ⟨n821, v821, d821, hv821, u821⟩ := u820.aluG hc804 ev_at_b76 (off' := 0xB7A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv821
  obtain ⟨n822, d822, u822⟩ := u821.lwE hc804 ev_at_b7a (off' := 0xB7C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 248) (by decide)) (v := v284)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xF8) 4 from sep_offsets F (c := 280) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8])
  obtain ⟨n823, v823, d823, hv823, u823⟩ := u822.aluG hc804 ev_at_b7c (off' := 0xB80) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv823
  obtain ⟨n824, v824, d824, hv824, u824⟩ := u823.aluG hc804 ev_at_b80 (off' := 0xB82) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv824
  obtain ⟨n825, v825, d825, hv825, u825⟩ := u824.aluG hc804 ev_at_b82 (off' := 0xB84) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv825
  obtain ⟨n826, v826, d826, hv826, u826⟩ := u825.aluG hc804 ev_at_b84 (off' := 0xB88) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv826
  obtain ⟨n827, v827, d827, hv827, u827⟩ := u826.aluG hc804 ev_at_b88 (off' := 0xB8A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv827
  obtain ⟨n828, v828, d828, hv828, u828⟩ := u827.aluImmG hc804 ev_at_b8a (off' := 0xB8E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv828
  obtain ⟨n829, v829, d829, hv829, u829⟩ := u828.aluG hc804 ev_at_b8e (off' := 0xB90) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv829
  obtain ⟨n830, v830, d830, hv830, u830⟩ := u829.aluG hc804 ev_at_b90 (off' := 0xB94) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv830
  obtain ⟨n831, v831, d831, hv831, u831⟩ := u830.aluG hc804 ev_at_b94 (off' := 0xB98) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv831
  obtain ⟨n832, v832, d832, hv832, u832⟩ := u831.aluG hc804 ev_at_b98 (off' := 0xB9A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv832
  obtain ⟨n833, v833, d833, hv833, u833⟩ := u832.aluG hc804 ev_at_b9a (off' := 0xB9C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv833
  obtain ⟨n834, d834, u834⟩ := u833.lwE hc804 ev_at_b9c (off' := 0xBA0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 288) (by decide)) (v := v116)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x120) 4 from sep_offsets F (c := 280) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120])
  obtain ⟨n835, d835, u835⟩ := u834.lwE hc804 ev_at_ba0 (off' := 0xBA2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 52) (by decide)) (v := v654)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x34) 4 from sep_offsets F (c := 280) (n := 4) (d := 52) (k := 4) (by decide) (by decide) (by decide)), sl34])
  obtain ⟨n836, v836, d836, hv836, u836⟩ := u835.aluG hc804 ev_at_ba2 (off' := 0xBA6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv836
  obtain ⟨n837, d837, u837⟩ := u836.lwE hc804 ev_at_ba6 (off' := 0xBA8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 56) (by decide)) (v := v656)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x38) 4 from sep_offsets F (c := 280) (n := 4) (d := 56) (k := 4) (by decide) (by decide) (by decide)), sl38])
  obtain ⟨n838, v838, d838, hv838, u838⟩ := u837.aluG hc804 ev_at_ba8 (off' := 0xBAC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv838
  obtain ⟨n839, v839, d839, hv839, u839⟩ := u838.aluG hc804 ev_at_bac (off' := 0xBAE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv839
  have qo1 : reg n839 ra = v357 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n839 sp = F := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n839 (3 : Fin 32) = G3 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n839 (4 : Fin 32) = G4 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n839 (5 : Fin 32) = v831 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n839 (6 : Fin 32) = v797 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n839 (7 : Fin 32) = v741 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n839 (8 : Fin 32) = v816 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n839 (9 : Fin 32) = v297 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n839 a0 = v116 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n839 a1 = v656 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n839 a2 = v833 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n839 a3 = v838 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n839 a4 = v839 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n839 a5 = v821 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n839 a6 = v802 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n839 a7 = v805 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n839 (18 : Fin 32) = v7 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n839 (19 : Fin 32) = v593 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n839 (20 : Fin 32) = v722 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n839 (21 : Fin 32) = v485 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n839 (22 : Fin 32) = v557 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n839 (23 : Fin 32) = v302 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n839 (24 : Fin 32) = v150 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n839 (25 : Fin 32) = v174 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n839 (26 : Fin 32) = v801 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n839 (27 : Fin 32) = v765 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n839 (28 : Fin 32) = v823 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n839 (29 : Fin 32) = v819 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n839 (30 : Fin 32) = v239 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n839 (31 : Fin 32) = v704 := by rw [u839.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm804 (F + 0xC) = G21 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xC) 4 from sep_offsets F (c := 280) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm804 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x10) 4 from sep_offsets F (c := 280) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so30 : memLoad32 Mm804 (F + 0x30) = v687 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x30) 4 from sep_offsets F (c := 280) (n := 4) (d := 48) (k := 4) (by decide) (by decide) (by decide)), sl30]
  have so3C : memLoad32 Mm804 (F + 0x3C) = v685 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x3C) 4 from sep_offsets F (c := 280) (n := 4) (d := 60) (k := 4) (by decide) (by decide) (by decide)), sl3C]
  have so40 : memLoad32 Mm804 (F + 0x40) = v665 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x40) 4 from sep_offsets F (c := 280) (n := 4) (d := 64) (k := 4) (by decide) (by decide) (by decide)), sl40]
  have so44 : memLoad32 Mm804 (F + 0x44) = v662 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x44) 4 from sep_offsets F (c := 280) (n := 4) (d := 68) (k := 4) (by decide) (by decide) (by decide)), sl44]
  have so48 : memLoad32 Mm804 (F + 0x48) = v647 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x48) 4 from sep_offsets F (c := 280) (n := 4) (d := 72) (k := 4) (by decide) (by decide) (by decide)), sl48]
  have so4C : memLoad32 Mm804 (F + 0x4C) = v678 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x4C) 4 from sep_offsets F (c := 280) (n := 4) (d := 76) (k := 4) (by decide) (by decide) (by decide)), sl4C]
  have so50 : memLoad32 Mm804 (F + 0x50) = v676 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x50) 4 from sep_offsets F (c := 280) (n := 4) (d := 80) (k := 4) (by decide) (by decide) (by decide)), sl50]
  have so54 : memLoad32 Mm804 (F + 0x54) = v645 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x54) 4 from sep_offsets F (c := 280) (n := 4) (d := 84) (k := 4) (by decide) (by decide) (by decide)), sl54]
  have so58 : memLoad32 Mm804 (F + 0x58) = v708 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x58) 4 from sep_offsets F (c := 280) (n := 4) (d := 88) (k := 4) (by decide) (by decide) (by decide)), sl58]
  have so5C : memLoad32 Mm804 (F + 0x5C) = v706 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x5C) 4 from sep_offsets F (c := 280) (n := 4) (d := 92) (k := 4) (by decide) (by decide) (by decide)), sl5C]
  have so60 : memLoad32 Mm804 (F + 0x60) = v680 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x60) 4 from sep_offsets F (c := 280) (n := 4) (d := 96) (k := 4) (by decide) (by decide) (by decide)), sl60]
  have so64 : memLoad32 Mm804 (F + 0x64) = v682 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x64) 4 from sep_offsets F (c := 280) (n := 4) (d := 100) (k := 4) (by decide) (by decide) (by decide)), sl64]
  have so68 : memLoad32 Mm804 (F + 0x68) = v689 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x68) 4 from sep_offsets F (c := 280) (n := 4) (d := 104) (k := 4) (by decide) (by decide) (by decide)), sl68]
  have so6C : memLoad32 Mm804 (F + 0x6C) = v691 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x6C) 4 from sep_offsets F (c := 280) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C]
  have so70 : memLoad32 Mm804 (F + 0x70) = v669 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x70) 4 from sep_offsets F (c := 280) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 Mm804 (F + 0x74) = v667 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x74) 4 from sep_offsets F (c := 280) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 Mm804 (F + 0x78) = v545 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x78) 4 from sep_offsets F (c := 280) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 Mm804 (F + 0x7C) = v717 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x7C) 4 from sep_offsets F (c := 280) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 Mm804 (F + 0x80) = v715 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x80) 4 from sep_offsets F (c := 280) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so84 : memLoad32 Mm804 (F + 0x84) = v572 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x84) 4 from sep_offsets F (c := 280) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so88 : memLoad32 Mm804 (F + 0x88) = v695 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x88) 4 from sep_offsets F (c := 280) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 Mm804 (F + 0x8C) = v559 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x8C) 4 from sep_offsets F (c := 280) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so94 : memLoad32 Mm804 (F + 0x94) = v481 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x94) 4 from sep_offsets F (c := 280) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 Mm804 (F + 0x98) = v352 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x98) 4 from sep_offsets F (c := 280) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), sl98]
  have so9C : memLoad32 Mm804 (F + 0x9C) = v713 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x9C) 4 from sep_offsets F (c := 280) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  have soA8 : memLoad32 Mm804 (F + 0xA8) = v279 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xA8) 4 from sep_offsets F (c := 280) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), slA8]
  have soAC : memLoad32 Mm804 (F + 0xAC) = v219 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xAC) 4 from sep_offsets F (c := 280) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), slAC]
  have soB0 : memLoad32 Mm804 (F + 0xB0) = v693 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xB0) 4 from sep_offsets F (c := 280) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0]
  have soB4 : memLoad32 Mm804 (F + 0xB4) = v582 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xB4) 4 from sep_offsets F (c := 280) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), slB4]
  have soBC : memLoad32 Mm804 (F + 0xBC) = v467 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xBC) 4 from sep_offsets F (c := 280) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm804 (F + 0xC0) = v405 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xC0) 4 from sep_offsets F (c := 280) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC4 : memLoad32 Mm804 (F + 0xC4) = v199 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xC4) 4 from sep_offsets F (c := 280) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), slC4]
  have soC8 : memLoad32 Mm804 (F + 0xC8) = v335 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xC8) 4 from sep_offsets F (c := 280) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soCC : memLoad32 Mm804 (F + 0xCC) = v264 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xCC) 4 from sep_offsets F (c := 280) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), slCC]
  have soD0 : memLoad32 Mm804 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xD0) 4 from sep_offsets F (c := 280) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soE8 : memLoad32 Mm804 (F + 0xE8) = v419 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xE8) 4 from sep_offsets F (c := 280) (n := 4) (d := 232) (k := 4) (by decide) (by decide) (by decide)), slE8]
  have soEC : memLoad32 Mm804 (F + 0xEC) = v341 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xEC) 4 from sep_offsets F (c := 280) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF0 : memLoad32 Mm804 (F + 0xF0) = v206 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xF0) 4 from sep_offsets F (c := 280) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), slF0]
  have soFC : memLoad32 Mm804 (F + 0xFC) = v579 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0xFC) 4 from sep_offsets F (c := 280) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm804 (F + 0x100) = v540 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x100) 4 from sep_offsets F (c := 280) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm804 (F + 0x104) = v710 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x104) 4 from sep_offsets F (c := 280) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 Mm804 (F + 0x108) = v203 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x108) 4 from sep_offsets F (c := 280) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 Mm804 (F + 0x10C) = v274 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x10C) 4 from sep_offsets F (c := 280) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm804 (F + 0x110) = v702 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x110) 4 from sep_offsets F (c := 280) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so118 : memLoad32 Mm804 (F + 0x118) = v803 := by
    rw [← hM804, memLoad32_store32_same]
  have so11C : memLoad32 Mm804 (F + 0x11C) = v231 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x11C) 4 from sep_offsets F (c := 280) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so124 : memLoad32 Mm804 (F + 0x124) = v124 := by
    rw [← hM804, memLoad32_store32_sep (show Sep (F + 0x118) 4 (F + 0x124) 4 from sep_offsets F (c := 280) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n839, Mm804, v800, v801, v802, v803, v805, v807, v808, v809, v810, v811, v812, v813, v815, v816, v817, v818, v819, v820, v821, v823, v824, v825, v826, v827, v828, v829, v830, v831, v832, v833, v836, v838, v839, (.cons d800 (.cons d801 (.cons d802 (.cons d803 (.cons d804 (.cons d805 (.cons d806 (.cons d807 (.cons d808 (.cons d809 (.cons d810 (.cons d811 (.cons d812 (.cons d813 (.cons d814 (.cons d815 (.cons d816 (.cons d817 (.cons d818 (.cons d819 (.cons d820 (.cons d821 (.cons d822 (.cons d823 (.cons d824 (.cons d825 (.cons d826 (.cons d827 (.cons d828 (.cons d829 (.cons d830 (.cons d831 (.cons d832 (.cons d833 (.cons d834 (.cons d835 (.cons d836 (.cons d837 (.cons d838 (.single d839)))))))))))))))))))))))))))))))))))))))), u839.self, hc804, fr804, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so30, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so94, so98, so9C, soA8, soAC, soB0, soB4, soBC, soC0, soC4, soC8, soCC, soD0, soE8, soEC, soF0, soFC, so100, so104, so108, so10C, so110, so118, so11C, so124, hv800, hv801, hv802, hv803, hv805, hv807, hv808, hv809, hv810, hv811, hv812, hv813, hv815, hv816, hv817, hv818, hv819, hv820, hv821, hv823, hv824, hv825, hv826, hv827, hv828, hv829, hv830, hv831, hv832, hv833, hv836, hv838, hv839⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g27 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v116 v124 v150 v174 v199 v203 v206 v219 v231 v239 v264 v274 v279 v297 v302 v335 v341 v352 v357 v405 v419 v467 v481 v485 v540 v545 v557 v559 v572 v579 v582 v593 v645 v647 v656 v662 v665 v667 v669 v676 v678 v680 v682 v685 v687 v689 v691 v693 v695 v702 v704 v706 v708 v710 v713 v715 v717 v722 v741 v765 v797 v801 v802 v803 v805 v816 v819 v821 v823 v831 v833 v838 v839 : Word}
    (s : St Mi B n 0xBAE (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v357)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v831)
    (q6 : reg n (6 : Fin 32) = v797)
    (q7 : reg n (7 : Fin 32) = v741)
    (q8 : reg n (8 : Fin 32) = v816)
    (q9 : reg n (9 : Fin 32) = v297)
    (q10 : reg n a0 = v116)
    (q11 : reg n a1 = v656)
    (q12 : reg n a2 = v833)
    (q13 : reg n a3 = v838)
    (q14 : reg n a4 = v839)
    (q15 : reg n a5 = v821)
    (q16 : reg n a6 = v802)
    (q17 : reg n a7 = v805)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v593)
    (q20 : reg n (20 : Fin 32) = v722)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v150)
    (q25 : reg n (25 : Fin 32) = v174)
    (q26 : reg n (26 : Fin 32) = v801)
    (q27 : reg n (27 : Fin 32) = v765)
    (q28 : reg n (28 : Fin 32) = v823)
    (q29 : reg n (29 : Fin 32) = v819)
    (q30 : reg n (30 : Fin 32) = v239)
    (q31 : reg n (31 : Fin 32) = v704)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl30 : memLoad32 Mi (F + 0x30) = v687)
    (sl3C : memLoad32 Mi (F + 0x3C) = v685)
    (sl40 : memLoad32 Mi (F + 0x40) = v665)
    (sl44 : memLoad32 Mi (F + 0x44) = v662)
    (sl48 : memLoad32 Mi (F + 0x48) = v647)
    (sl4C : memLoad32 Mi (F + 0x4C) = v678)
    (sl50 : memLoad32 Mi (F + 0x50) = v676)
    (sl54 : memLoad32 Mi (F + 0x54) = v645)
    (sl58 : memLoad32 Mi (F + 0x58) = v708)
    (sl5C : memLoad32 Mi (F + 0x5C) = v706)
    (sl60 : memLoad32 Mi (F + 0x60) = v680)
    (sl64 : memLoad32 Mi (F + 0x64) = v682)
    (sl68 : memLoad32 Mi (F + 0x68) = v689)
    (sl6C : memLoad32 Mi (F + 0x6C) = v691)
    (sl70 : memLoad32 Mi (F + 0x70) = v669)
    (sl74 : memLoad32 Mi (F + 0x74) = v667)
    (sl78 : memLoad32 Mi (F + 0x78) = v545)
    (sl7C : memLoad32 Mi (F + 0x7C) = v717)
    (sl80 : memLoad32 Mi (F + 0x80) = v715)
    (sl84 : memLoad32 Mi (F + 0x84) = v572)
    (sl88 : memLoad32 Mi (F + 0x88) = v695)
    (sl8C : memLoad32 Mi (F + 0x8C) = v559)
    (sl94 : memLoad32 Mi (F + 0x94) = v481)
    (sl98 : memLoad32 Mi (F + 0x98) = v352)
    (sl9C : memLoad32 Mi (F + 0x9C) = v713)
    (slA8 : memLoad32 Mi (F + 0xA8) = v279)
    (slAC : memLoad32 Mi (F + 0xAC) = v219)
    (slB0 : memLoad32 Mi (F + 0xB0) = v693)
    (slB4 : memLoad32 Mi (F + 0xB4) = v582)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE8 : memLoad32 Mi (F + 0xE8) = v419)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slFC : memLoad32 Mi (F + 0xFC) = v579)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v710)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v702)
    (sl118 : memLoad32 Mi (F + 0x118) = v803)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v841 v843 v845 v846 v848 v850 v851 v852 v853 v855 v856 v858 v859 v861 v863 v864 v865 v867 v868 v869 v870 v872 v873 v874 v876 v878 v879 : Word),
      Steps n n' ∧
      St M' B n' 0xC16 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v357 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v831 ∧
      reg n' (6 : Fin 32) = v797 ∧
      reg n' (7 : Fin 32) = v873 ∧
      reg n' (8 : Fin 32) = v851 ∧
      reg n' (9 : Fin 32) = v861 ∧
      reg n' a0 = v878 ∧
      reg n' a1 = v656 ∧
      reg n' a2 = v833 ∧
      reg n' a3 = v874 ∧
      reg n' a4 = v876 ∧
      reg n' a5 = v879 ∧
      reg n' a6 = v869 ∧
      reg n' a7 = v485 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v593 ∧
      reg n' (20 : Fin 32) = v722 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v150 ∧
      reg n' (25 : Fin 32) = v174 ∧
      reg n' (26 : Fin 32) = v545 ∧
      reg n' (27 : Fin 32) = v765 ∧
      reg n' (28 : Fin 32) = v823 ∧
      reg n' (29 : Fin 32) = v819 ∧
      reg n' (30 : Fin 32) = v239 ∧
      reg n' (31 : Fin 32) = v481 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x58) = v708 ∧
      memLoad32 M' (F + 0x5C) = v706 ∧
      memLoad32 M' (F + 0x60) = v680 ∧
      memLoad32 M' (F + 0x64) = v682 ∧
      memLoad32 M' (F + 0x68) = v689 ∧
      memLoad32 M' (F + 0x6C) = v691 ∧
      memLoad32 M' (F + 0x70) = v669 ∧
      memLoad32 M' (F + 0x74) = v667 ∧
      memLoad32 M' (F + 0x7C) = v717 ∧
      memLoad32 M' (F + 0x80) = v715 ∧
      memLoad32 M' (F + 0x84) = v572 ∧
      memLoad32 M' (F + 0x88) = v695 ∧
      memLoad32 M' (F + 0x8C) = v559 ∧
      memLoad32 M' (F + 0x98) = v352 ∧
      memLoad32 M' (F + 0x9C) = v713 ∧
      memLoad32 M' (F + 0xA8) = v279 ∧
      memLoad32 M' (F + 0xB0) = v693 ∧
      memLoad32 M' (F + 0xB4) = v582 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xCC) = v264 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x104) = v710 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v702 ∧
      memLoad32 M' (F + 0x118) = v803 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      aluEval .add v838 v647 = v841 ∧
      aluEval .add v645 v839 = v843 ∧
      aluEval .sub v841 v124 = v845 ∧
      aluEval .sltu v843 v839 = v846 ∧
      aluEval .add v846 v662 = v848 ∧
      aluEval .add v665 v843 = v850 ∧
      aluEval .mul v819 v150 = v851 ∧
      aluEval .sltu v850 v843 = v852 ∧
      aluEval .add v845 v848 = v853 ∧
      aluEval .add v852 v687 = v855 ∧
      aluEval .add v853 v855 = v856 ∧
      aluEval .add v685 v850 = v858 ∧
      aluEval .sltu v858 v850 = v859 ∧
      aluEval .add v676 v858 = v861 ∧
      aluEval .add v859 v678 = v863 ∧
      aluEval .sltu v861 v858 = v864 ∧
      aluEval .add v856 v863 = v865 ∧
      aluEval .sub v864 v545 = v867 ∧
      aluEval .add v865 v867 = v868 ∧
      aluEval .add v802 v851 = v869 ∧
      aluEval .sltu v869 v851 = v870 ∧
      aluEval .sltu v861 v481 = v872 ∧
      aluEval .add v833 v870 = v873 ∧
      aluEval .sub v868 v872 = v874 ∧
      aluEval .srl v219 0xC = v876 ∧
      aluEval .add 0 0x14D = v878 ∧
      aluEval .mulhu v485 v878 = v879 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n840, d840, u840⟩ := s.lwE hc ev_at_bae (off' := 0xBB0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 72) (by decide)) (v := v647)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl48])
  obtain ⟨n841, v841, d841, hv841, u841⟩ := u840.aluG hc ev_at_bb0 (off' := 0xBB2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv841
  obtain ⟨n842, d842, u842⟩ := u841.lwE hc ev_at_bb2 (off' := 0xBB4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 84) (by decide)) (v := v645)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl54])
  obtain ⟨n843, v843, d843, hv843, u843⟩ := u842.aluG hc ev_at_bb4 (off' := 0xBB6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv843
  obtain ⟨n844, d844, u844⟩ := u843.lwE hc ev_at_bb6 (off' := 0xBBA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 292) (by decide)) (v := v124)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl124])
  obtain ⟨n845, v845, d845, hv845, u845⟩ := u844.aluG hc ev_at_bba (off' := 0xBBC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv845
  obtain ⟨n846, v846, d846, hv846, u846⟩ := u845.aluG hc ev_at_bbc (off' := 0xBC0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv846
  obtain ⟨n847, d847, u847⟩ := u846.lwE hc ev_at_bc0 (off' := 0xBC2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 68) (by decide)) (v := v662)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl44])
  obtain ⟨n848, v848, d848, hv848, u848⟩ := u847.aluG hc ev_at_bc2 (off' := 0xBC4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv848
  obtain ⟨n849, d849, u849⟩ := u848.lwE hc ev_at_bc4 (off' := 0xBC6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 64) (by decide)) (v := v665)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl40])
  obtain ⟨n850, v850, d850, hv850, u850⟩ := u849.aluG hc ev_at_bc6 (off' := 0xBC8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv850
  obtain ⟨n851, v851, d851, hv851, u851⟩ := u850.aluG hc ev_at_bc8 (off' := 0xBCC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv851
  obtain ⟨n852, v852, d852, hv852, u852⟩ := u851.aluG hc ev_at_bcc (off' := 0xBD0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv852
  obtain ⟨n853, v853, d853, hv853, u853⟩ := u852.aluG hc ev_at_bd0 (off' := 0xBD2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv853
  obtain ⟨n854, d854, u854⟩ := u853.lwE hc ev_at_bd2 (off' := 0xBD4) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 48) (by decide)) (v := v687)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl30])
  obtain ⟨n855, v855, d855, hv855, u855⟩ := u854.aluG hc ev_at_bd4 (off' := 0xBD6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv855
  obtain ⟨n856, v856, d856, hv856, u856⟩ := u855.aluG hc ev_at_bd6 (off' := 0xBD8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv856
  obtain ⟨n857, d857, u857⟩ := u856.lwE hc ev_at_bd8 (off' := 0xBDA) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 60) (by decide)) (v := v685)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl3C])
  obtain ⟨n858, v858, d858, hv858, u858⟩ := u857.aluG hc ev_at_bda (off' := 0xBDC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv858
  obtain ⟨n859, v859, d859, hv859, u859⟩ := u858.aluG hc ev_at_bdc (off' := 0xBE0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv859
  obtain ⟨n860, d860, u860⟩ := u859.lwE hc ev_at_be0 (off' := 0xBE2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 80) (by decide)) (v := v676)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl50])
  obtain ⟨n861, v861, d861, hv861, u861⟩ := u860.aluG hc ev_at_be2 (off' := 0xBE4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv861
  obtain ⟨n862, d862, u862⟩ := u861.lwE hc ev_at_be4 (off' := 0xBE6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 76) (by decide)) (v := v678)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl4C])
  obtain ⟨n863, v863, d863, hv863, u863⟩ := u862.aluG hc ev_at_be6 (off' := 0xBE8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv863
  obtain ⟨n864, v864, d864, hv864, u864⟩ := u863.aluG hc ev_at_be8 (off' := 0xBEC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv864
  obtain ⟨n865, v865, d865, hv865, u865⟩ := u864.aluG hc ev_at_bec (off' := 0xBEE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv865
  obtain ⟨n866, d866, u866⟩ := u865.lwE hc ev_at_bee (off' := 0xBF0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 120) (by decide)) (v := v545)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl78])
  obtain ⟨n867, v867, d867, hv867, u867⟩ := u866.aluG hc ev_at_bf0 (off' := 0xBF4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv867
  obtain ⟨n868, v868, d868, hv868, u868⟩ := u867.aluG hc ev_at_bf4 (off' := 0xBF6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv868
  obtain ⟨n869, v869, d869, hv869, u869⟩ := u868.aluG hc ev_at_bf6 (off' := 0xBF8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv869
  obtain ⟨n870, v870, d870, hv870, u870⟩ := u869.aluG hc ev_at_bf8 (off' := 0xBFC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv870
  obtain ⟨n871, d871, u871⟩ := u870.lwE hc ev_at_bfc (off' := 0xBFE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 148) (by decide)) (v := v481)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl94])
  obtain ⟨n872, v872, d872, hv872, u872⟩ := u871.aluG hc ev_at_bfe (off' := 0xC02) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv872
  obtain ⟨n873, v873, d873, hv873, u873⟩ := u872.aluG hc ev_at_c02 (off' := 0xC06) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv873
  obtain ⟨n874, v874, d874, hv874, u874⟩ := u873.aluG hc ev_at_c06 (off' := 0xC08) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv874
  obtain ⟨n875, d875, u875⟩ := u874.lwE hc ev_at_c08 (off' := 0xC0A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 172) (by decide)) (v := v219)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slAC])
  obtain ⟨n876, v876, d876, hv876, u876⟩ := u875.aluImmG hc ev_at_c0a (off' := 0xC0C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv876
  obtain ⟨n877, d877, u877⟩ := u876.aluE hc ev_at_c0c (off' := 0xC0E) (by decide) (v := v485)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n878, v878, d878, hv878, u878⟩ := u877.aluImmG hc ev_at_c0e (off' := 0xC12) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv878
  obtain ⟨n879, v879, d879, hv879, u879⟩ := u878.aluG hc ev_at_c12 (off' := 0xC16) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv879
  have qo1 : reg n879 ra = v357 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n879 sp = F := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n879 (3 : Fin 32) = G3 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n879 (4 : Fin 32) = G4 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n879 (5 : Fin 32) = v831 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n879 (6 : Fin 32) = v797 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n879 (7 : Fin 32) = v873 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n879 (8 : Fin 32) = v851 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n879 (9 : Fin 32) = v861 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n879 a0 = v878 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n879 a1 = v656 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n879 a2 = v833 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n879 a3 = v874 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n879 a4 = v876 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n879 a5 = v879 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n879 a6 = v869 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n879 a7 = v485 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n879 (18 : Fin 32) = v7 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n879 (19 : Fin 32) = v593 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n879 (20 : Fin 32) = v722 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n879 (21 : Fin 32) = v485 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n879 (22 : Fin 32) = v557 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n879 (23 : Fin 32) = v302 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n879 (24 : Fin 32) = v150 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n879 (25 : Fin 32) = v174 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n879 (26 : Fin 32) = v545 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n879 (27 : Fin 32) = v765 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n879 (28 : Fin 32) = v823 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n879 (29 : Fin 32) = v819 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n879 (30 : Fin 32) = v239 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n879 (31 : Fin 32) = v481 := by rw [u879.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mi (F + 0xC) = G21 := by
    rw [slC]
  have so10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [sl10]
  have so58 : memLoad32 Mi (F + 0x58) = v708 := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = v706 := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = v680 := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = v682 := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = v689 := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = v691 := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = v669 := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = v667 := by
    rw [sl74]
  have so7C : memLoad32 Mi (F + 0x7C) = v717 := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = v715 := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = v572 := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = v695 := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = v559 := by
    rw [sl8C]
  have so98 : memLoad32 Mi (F + 0x98) = v352 := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = v713 := by
    rw [sl9C]
  have soA8 : memLoad32 Mi (F + 0xA8) = v279 := by
    rw [slA8]
  have soB0 : memLoad32 Mi (F + 0xB0) = v693 := by
    rw [slB0]
  have soB4 : memLoad32 Mi (F + 0xB4) = v582 := by
    rw [slB4]
  have soBC : memLoad32 Mi (F + 0xBC) = v467 := by
    rw [slBC]
  have soC0 : memLoad32 Mi (F + 0xC0) = v405 := by
    rw [slC0]
  have soC4 : memLoad32 Mi (F + 0xC4) = v199 := by
    rw [slC4]
  have soC8 : memLoad32 Mi (F + 0xC8) = v335 := by
    rw [slC8]
  have soCC : memLoad32 Mi (F + 0xCC) = v264 := by
    rw [slCC]
  have soD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [slD0]
  have soE8 : memLoad32 Mi (F + 0xE8) = v419 := by
    rw [slE8]
  have soEC : memLoad32 Mi (F + 0xEC) = v341 := by
    rw [slEC]
  have soF0 : memLoad32 Mi (F + 0xF0) = v206 := by
    rw [slF0]
  have soFC : memLoad32 Mi (F + 0xFC) = v579 := by
    rw [slFC]
  have so100 : memLoad32 Mi (F + 0x100) = v540 := by
    rw [sl100]
  have so104 : memLoad32 Mi (F + 0x104) = v710 := by
    rw [sl104]
  have so108 : memLoad32 Mi (F + 0x108) = v203 := by
    rw [sl108]
  have so10C : memLoad32 Mi (F + 0x10C) = v274 := by
    rw [sl10C]
  have so110 : memLoad32 Mi (F + 0x110) = v702 := by
    rw [sl110]
  have so118 : memLoad32 Mi (F + 0x118) = v803 := by
    rw [sl118]
  have so11C : memLoad32 Mi (F + 0x11C) = v231 := by
    rw [sl11C]
  exact ⟨n879, Mi, v841, v843, v845, v846, v848, v850, v851, v852, v853, v855, v856, v858, v859, v861, v863, v864, v865, v867, v868, v869, v870, v872, v873, v874, v876, v878, v879, (.cons d840 (.cons d841 (.cons d842 (.cons d843 (.cons d844 (.cons d845 (.cons d846 (.cons d847 (.cons d848 (.cons d849 (.cons d850 (.cons d851 (.cons d852 (.cons d853 (.cons d854 (.cons d855 (.cons d856 (.cons d857 (.cons d858 (.cons d859 (.cons d860 (.cons d861 (.cons d862 (.cons d863 (.cons d864 (.cons d865 (.cons d866 (.cons d867 (.cons d868 (.cons d869 (.cons d870 (.cons d871 (.cons d872 (.cons d873 (.cons d874 (.cons d875 (.cons d876 (.cons d877 (.cons d878 (.single d879)))))))))))))))))))))))))))))))))))))))), u879.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so58, so5C, so60, so64, so68, so6C, so70, so74, so7C, so80, so84, so88, so8C, so98, so9C, soA8, soB0, soB4, soBC, soC0, soC4, soC8, soCC, soD0, soE8, soEC, soF0, soFC, so100, so104, so108, so10C, so110, so118, so11C, hv841, hv843, hv845, hv846, hv848, hv850, hv851, hv852, hv853, hv855, hv856, hv858, hv859, hv861, hv863, hv864, hv865, hv867, hv868, hv869, hv870, hv872, hv873, hv874, hv876, hv878, hv879⟩

end C3.RV32
