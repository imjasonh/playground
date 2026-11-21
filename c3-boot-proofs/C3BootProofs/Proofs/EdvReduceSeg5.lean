import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce` in `ed25519_verify`, segments 16 to 17

Each theorem steps 40 instructions. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g16 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v16 v36 v62 v67 v75 v87 v111 v116 v122 v124 v133 v136 v150 v151 v174 v199 v203 v206 v219 v231 v239 v254 v264 v274 v279 v284 v297 v302 v308 v310 v312 v320 v335 v341 v352 v357 v388 v405 v409 v419 v467 v476 v480 v481 v485 v509 v527 v530 v533 v534 v536 v537 v538 v540 v545 v553 v555 v556 v557 v559 : Word}
    (s : St Mi B n 0x862 (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v409)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v279)
    (q6 : reg n (6 : Fin 32) = v419)
    (q7 : reg n (7 : Fin 32) = v533)
    (q8 : reg n (8 : Fin 32) = v538)
    (q9 : reg n (9 : Fin 32) = v536)
    (q10 : reg n a0 = v553)
    (q11 : reg n a1 = v555)
    (q12 : reg n a2 = v559)
    (q13 : reg n a3 = v320)
    (q14 : reg n a4 = v527)
    (q15 : reg n a5 = v534)
    (q16 : reg n a6 = v556)
    (q17 : reg n a7 = v509)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v133)
    (q20 : reg n (20 : Fin 32) = v310)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v476)
    (q25 : reg n (25 : Fin 32) = v352)
    (q26 : reg n (26 : Fin 32) = v480)
    (q27 : reg n (27 : Fin 32) = v530)
    (q28 : reg n (28 : Fin 32) = v254)
    (q29 : reg n (29 : Fin 32) = v545)
    (q30 : reg n (30 : Fin 32) = v388)
    (q31 : reg n (31 : Fin 32) = v537)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl70 : memLoad32 Mi (F + 0x70) = v308)
    (sl78 : memLoad32 Mi (F + 0x78) = v545)
    (sl7C : memLoad32 Mi (F + 0x7C) = v312)
    (sl88 : memLoad32 Mi (F + 0x88) = v36)
    (sl90 : memLoad32 Mi (F + 0x90) = v151)
    (sl94 : memLoad32 Mi (F + 0x94) = v481)
    (sl9C : memLoad32 Mi (F + 0x9C) = v75)
    (slA0 : memLoad32 Mi (F + 0xA0) = v87)
    (slA4 : memLoad32 Mi (F + 0xA4) = v357)
    (slA8 : memLoad32 Mi (F + 0xA8) = v279)
    (slAC : memLoad32 Mi (F + 0xAC) = v219)
    (slB0 : memLoad32 Mi (F + 0xB0) = v16)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slD4 : memLoad32 Mi (F + 0xD4) = v239)
    (slD8 : memLoad32 Mi (F + 0xD8) = v174)
    (slDC : memLoad32 Mi (F + 0xDC) = v150)
    (slE0 : memLoad32 Mi (F + 0xE0) = v133)
    (slE4 : memLoad32 Mi (F + 0xE4) = v7)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slF4 : memLoad32 Mi (F + 0xF4) = v297)
    (slF8 : memLoad32 Mi (F + 0xF8) = v284)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v562 v563 v564 v566 v567 v568 v569 v570 v571 v572 v574 v576 v577 v579 v581 v582 v584 v585 v586 v587 v588 v589 v590 v592 v593 v594 v595 v596 v597 v598 v599 : Word),
      Steps n n' ∧
      St M' B n' 0x8DC (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v409 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v576 ∧
      reg n' (6 : Fin 32) = v419 ∧
      reg n' (7 : Fin 32) = v592 ∧
      reg n' (8 : Fin 32) = v568 ∧
      reg n' (9 : Fin 32) = v590 ∧
      reg n' a0 = v599 ∧
      reg n' a1 = v585 ∧
      reg n' a2 = v308 ∧
      reg n' a3 = v588 ∧
      reg n' a4 = v596 ∧
      reg n' a5 = v589 ∧
      reg n' a6 = v594 ∧
      reg n' a7 = v595 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v593 ∧
      reg n' (20 : Fin 32) = v310 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v476 ∧
      reg n' (25 : Fin 32) = v352 ∧
      reg n' (26 : Fin 32) = v480 ∧
      reg n' (27 : Fin 32) = v598 ∧
      reg n' (28 : Fin 32) = v254 ∧
      reg n' (29 : Fin 32) = v587 ∧
      reg n' (30 : Fin 32) = v388 ∧
      reg n' (31 : Fin 32) = v537 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x78) = v545 ∧
      memLoad32 M' (F + 0x84) = v572 ∧
      memLoad32 M' (F + 0x8C) = v559 ∧
      memLoad32 M' (F + 0x90) = v151 ∧
      memLoad32 M' (F + 0x94) = v481 ∧
      memLoad32 M' (F + 0x9C) = v75 ∧
      memLoad32 M' (F + 0xA0) = v87 ∧
      memLoad32 M' (F + 0xA4) = v357 ∧
      memLoad32 M' (F + 0xA8) = v279 ∧
      memLoad32 M' (F + 0xAC) = v219 ∧
      memLoad32 M' (F + 0xB4) = v582 ∧
      memLoad32 M' (F + 0xB8) = v136 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xCC) = v264 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xD4) = v239 ∧
      memLoad32 M' (F + 0xD8) = v174 ∧
      memLoad32 M' (F + 0xDC) = v150 ∧
      memLoad32 M' (F + 0xE0) = v133 ∧
      memLoad32 M' (F + 0xE4) = v7 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xF4) = v297 ∧
      memLoad32 M' (F + 0xF8) = v284 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .mulhu v557 v150 = v562 ∧
      aluEval .sltu v559 v320 = v563 ∧
      aluEval .sltu v536 v533 = v564 ∧
      aluEval .add v563 v312 = v566 ∧
      aluEval .add v553 v564 = v567 ∧
      aluEval .srl v509 0x1D = v568 ∧
      aluEval .mul v557 v150 = v569 ∧
      aluEval .add v567 v568 = v570 ∧
      aluEval .sltu v537 v536 = v571 ∧
      aluEval .add v566 v556 = v572 ∧
      aluEval .add v570 v571 = v574 ∧
      aluEval .add v16 v254 = v576 ∧
      aluEval .add v574 v562 = v577 ∧
      aluEval .mulhu v308 v310 = v579 ∧
      aluEval .sll v308 0x14 = v581 ∧
      aluEval .sub v581 v308 = v582 ∧
      (0x2F7C1000 : Word) = v584 ∧
      aluEval .add v584 0xFFFFF98B = v585 ∧
      aluEval .add v569 v537 = v586 ∧
      aluEval .sltu v586 v569 = v587 ∧
      aluEval .mul v388 v585 = v588 ∧
      aluEval .mulhu v388 v585 = v589 ∧
      aluEval .mul v476 v480 = v590 ∧
      aluEval .add v36 v308 = v592 ∧
      aluEval .add v577 v587 = v593 ∧
      aluEval .mulhu v476 v480 = v594 ∧
      aluEval .mulhu v576 v409 = v595 ∧
      aluEval .srl v586 0x1D = v596 ∧
      aluEval .sll v593 0x3 = v597 ∧
      aluEval .or v596 v597 = v598 ∧
      aluEval .mul v576 v409 = v599 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n560, d560, u560⟩ := s.swG hc ev_at_862 (off' := 0x864) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 140) (by decide)) (a := F + 0x8C) (v := v559)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm560, hM560⟩ : ∃ M', memStore32 Mi (F + 0x8C) v559 = M' := ⟨_, rfl⟩
  rw [hM560] at u560
  have hc560 : CodeIn Mm560 B ed25519VerifyCode := by rw [← hM560]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr560 : ∀ x, Sep F 0x128 x 1 → Mm560 x = M0 x := fun x hx => by
    rw [← hM560, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n561, d561, u561⟩ := u560.lwE hc560 ev_at_864 (off' := 0x866) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 220) (by decide)) (v := v150)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xDC) 4 from sep_offsets F (c := 140) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), slDC])
  obtain ⟨n562, v562, d562, hv562, u562⟩ := u561.aluG hc560 ev_at_866 (off' := 0x86A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv562
  obtain ⟨n563, v563, d563, hv563, u563⟩ := u562.aluG hc560 ev_at_86a (off' := 0x86E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv563
  obtain ⟨n564, v564, d564, hv564, u564⟩ := u563.aluG hc560 ev_at_86e (off' := 0x872) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv564
  obtain ⟨n565, d565, u565⟩ := u564.lwE hc560 ev_at_872 (off' := 0x874) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 124) (by decide)) (v := v312)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x7C) 4 from sep_offsets F (c := 140) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C])
  obtain ⟨n566, v566, d566, hv566, u566⟩ := u565.aluG hc560 ev_at_874 (off' := 0x876) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv566
  obtain ⟨n567, v567, d567, hv567, u567⟩ := u566.aluG hc560 ev_at_876 (off' := 0x878) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv567
  obtain ⟨n568, v568, d568, hv568, u568⟩ := u567.aluImmG hc560 ev_at_878 (off' := 0x87C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv568
  obtain ⟨n569, v569, d569, hv569, u569⟩ := u568.aluG hc560 ev_at_87c (off' := 0x880) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv569
  obtain ⟨n570, v570, d570, hv570, u570⟩ := u569.aluG hc560 ev_at_880 (off' := 0x882) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv570
  obtain ⟨n571, v571, d571, hv571, u571⟩ := u570.aluG hc560 ev_at_882 (off' := 0x886) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv571
  obtain ⟨n572, v572, d572, hv572, u572⟩ := u571.aluG hc560 ev_at_886 (off' := 0x888) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv572
  obtain ⟨n573, d573, u573⟩ := u572.swG hc560 ev_at_888 (off' := 0x88A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 132) (by decide)) (a := F + 0x84) (v := v572)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm573, hM573⟩ : ∃ M', memStore32 Mm560 (F + 0x84) v572 = M' := ⟨_, rfl⟩
  rw [hM573] at u573
  have hc573 : CodeIn Mm573 B ed25519VerifyCode := by rw [← hM573]; exact hc560.store32 (frm_sep' sFC (by decide))
  have fr573 : ∀ x, Sep F 0x128 x 1 → Mm573 x = M0 x := fun x hx => by
    rw [← hM573, memStore32_get_sep (frm_sep' hx (by decide)), fr560 x hx]
  obtain ⟨n574, v574, d574, hv574, u574⟩ := u573.aluG hc573 ev_at_88a (off' := 0x88C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv574
  obtain ⟨n575, d575, u575⟩ := u574.lwE hc573 ev_at_88c (off' := 0x88E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 176) (by decide)) (v := v16)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xB0) 4 from sep_offsets F (c := 132) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xB0) 4 from sep_offsets F (c := 140) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0])
  obtain ⟨n576, v576, d576, hv576, u576⟩ := u575.aluG hc573 ev_at_88e (off' := 0x890) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv576
  obtain ⟨n577, v577, d577, hv577, u577⟩ := u576.aluG hc573 ev_at_890 (off' := 0x892) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv577
  obtain ⟨n578, d578, u578⟩ := u577.lwE hc573 ev_at_892 (off' := 0x894) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 112) (by decide)) (v := v308)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x70) 4 from sep_offsets F (c := 132) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x70) 4 from sep_offsets F (c := 140) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70])
  obtain ⟨n579, v579, d579, hv579, u579⟩ := u578.aluG hc573 ev_at_894 (off' := 0x898) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv579
  obtain ⟨n580, d580, u580⟩ := u579.swG hc573 ev_at_898 (off' := 0x89A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 252) (by decide)) (a := F + 0xFC) (v := v579)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm580, hM580⟩ : ∃ M', memStore32 Mm573 (F + 0xFC) v579 = M' := ⟨_, rfl⟩
  rw [hM580] at u580
  have hc580 : CodeIn Mm580 B ed25519VerifyCode := by rw [← hM580]; exact hc573.store32 (frm_sep' sFC (by decide))
  have fr580 : ∀ x, Sep F 0x128 x 1 → Mm580 x = M0 x := fun x hx => by
    rw [← hM580, memStore32_get_sep (frm_sep' hx (by decide)), fr573 x hx]
  obtain ⟨n581, v581, d581, hv581, u581⟩ := u580.aluImmG hc580 ev_at_89a (off' := 0x89E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv581
  obtain ⟨n582, v582, d582, hv582, u582⟩ := u581.aluG hc580 ev_at_89e (off' := 0x8A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv582
  obtain ⟨n583, d583, u583⟩ := u582.swG hc580 ev_at_8a0 (off' := 0x8A2) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 180) (by decide)) (a := F + 0xB4) (v := v582)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm583, hM583⟩ : ∃ M', memStore32 Mm580 (F + 0xB4) v582 = M' := ⟨_, rfl⟩
  rw [hM583] at u583
  have hc583 : CodeIn Mm583 B ed25519VerifyCode := by rw [← hM583]; exact hc580.store32 (frm_sep' sFC (by decide))
  have fr583 : ∀ x, Sep F 0x128 x 1 → Mm583 x = M0 x := fun x hx => by
    rw [← hM583, memStore32_get_sep (frm_sep' hx (by decide)), fr580 x hx]
  obtain ⟨n584, v584, d584, hv584, u584⟩ := u583.luiG hc583 ev_at_8a2 (off' := 0x8A6) (by decide)
  obtain ⟨n585, v585, d585, hv585, u585⟩ := u584.aluImmG hc583 ev_at_8a6 (off' := 0x8AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv585
  obtain ⟨n586, v586, d586, hv586, u586⟩ := u585.aluG hc583 ev_at_8aa (off' := 0x8AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv586
  obtain ⟨n587, v587, d587, hv587, u587⟩ := u586.aluG hc583 ev_at_8ae (off' := 0x8B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv587
  obtain ⟨n588, v588, d588, hv588, u588⟩ := u587.aluG hc583 ev_at_8b2 (off' := 0x8B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv588
  obtain ⟨n589, v589, d589, hv589, u589⟩ := u588.aluG hc583 ev_at_8b6 (off' := 0x8BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv589
  obtain ⟨n590, v590, d590, hv590, u590⟩ := u589.aluG hc583 ev_at_8ba (off' := 0x8BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv590
  obtain ⟨n591, d591, u591⟩ := u590.lwE hc583 ev_at_8be (off' := 0x8C0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 136) (by decide)) (v := v36)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x88) 4 from sep_offsets F (c := 180) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x88) 4 from sep_offsets F (c := 252) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x88) 4 from sep_offsets F (c := 132) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x88) 4 from sep_offsets F (c := 140) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88])
  obtain ⟨n592, v592, d592, hv592, u592⟩ := u591.aluG hc583 ev_at_8c0 (off' := 0x8C2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv592
  obtain ⟨n593, v593, d593, hv593, u593⟩ := u592.aluG hc583 ev_at_8c2 (off' := 0x8C6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv593
  obtain ⟨n594, v594, d594, hv594, u594⟩ := u593.aluG hc583 ev_at_8c6 (off' := 0x8CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv594
  obtain ⟨n595, v595, d595, hv595, u595⟩ := u594.aluG hc583 ev_at_8ca (off' := 0x8CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv595
  obtain ⟨n596, v596, d596, hv596, u596⟩ := u595.aluImmG hc583 ev_at_8ce (off' := 0x8D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv596
  obtain ⟨n597, v597, d597, hv597, u597⟩ := u596.aluImmG hc583 ev_at_8d0 (off' := 0x8D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv597
  obtain ⟨n598, v598, d598, hv598, u598⟩ := u597.aluG hc583 ev_at_8d4 (off' := 0x8D8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv598
  obtain ⟨n599, v599, d599, hv599, u599⟩ := u598.aluG hc583 ev_at_8d8 (off' := 0x8DC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv599
  have qo1 : reg n599 ra = v409 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n599 sp = F := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n599 (3 : Fin 32) = G3 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n599 (4 : Fin 32) = G4 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n599 (5 : Fin 32) = v576 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n599 (6 : Fin 32) = v419 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n599 (7 : Fin 32) = v592 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n599 (8 : Fin 32) = v568 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n599 (9 : Fin 32) = v590 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n599 a0 = v599 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n599 a1 = v585 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n599 a2 = v308 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n599 a3 = v588 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n599 a4 = v596 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n599 a5 = v589 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n599 a6 = v594 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n599 a7 = v595 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n599 (18 : Fin 32) = v7 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n599 (19 : Fin 32) = v593 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n599 (20 : Fin 32) = v310 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n599 (21 : Fin 32) = v485 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n599 (22 : Fin 32) = v557 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n599 (23 : Fin 32) = v302 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n599 (24 : Fin 32) = v476 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n599 (25 : Fin 32) = v352 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n599 (26 : Fin 32) = v480 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n599 (27 : Fin 32) = v598 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n599 (28 : Fin 32) = v254 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n599 (29 : Fin 32) = v587 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n599 (30 : Fin 32) = v388 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n599 (31 : Fin 32) = v537 := by rw [u599.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm583 (F + 0xC) = G21 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xC) 4 from sep_offsets F (c := 180) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xC) 4 from sep_offsets F (c := 252) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xC) 4 from sep_offsets F (c := 132) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xC) 4 from sep_offsets F (c := 140) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm583 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x10) 4 from sep_offsets F (c := 180) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x10) 4 from sep_offsets F (c := 252) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x10) 4 from sep_offsets F (c := 132) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x10) 4 from sep_offsets F (c := 140) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so78 : memLoad32 Mm583 (F + 0x78) = v545 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x78) 4 from sep_offsets F (c := 180) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x78) 4 from sep_offsets F (c := 252) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x78) 4 from sep_offsets F (c := 132) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x78) 4 from sep_offsets F (c := 140) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so84 : memLoad32 Mm583 (F + 0x84) = v572 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x84) 4 from sep_offsets F (c := 180) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x84) 4 from sep_offsets F (c := 252) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_same]
  have so8C : memLoad32 Mm583 (F + 0x8C) = v559 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x8C) 4 from sep_offsets F (c := 180) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x8C) 4 from sep_offsets F (c := 252) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x8C) 4 from sep_offsets F (c := 132) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_same]
  have so90 : memLoad32 Mm583 (F + 0x90) = v151 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x90) 4 from sep_offsets F (c := 180) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x90) 4 from sep_offsets F (c := 252) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x90) 4 from sep_offsets F (c := 132) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x90) 4 from sep_offsets F (c := 140) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 Mm583 (F + 0x94) = v481 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x94) 4 from sep_offsets F (c := 180) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x94) 4 from sep_offsets F (c := 252) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x94) 4 from sep_offsets F (c := 132) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x94) 4 from sep_offsets F (c := 140) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so9C : memLoad32 Mm583 (F + 0x9C) = v75 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x9C) 4 from sep_offsets F (c := 180) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x9C) 4 from sep_offsets F (c := 252) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x9C) 4 from sep_offsets F (c := 132) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x9C) 4 from sep_offsets F (c := 140) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  have soA0 : memLoad32 Mm583 (F + 0xA0) = v87 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xA0) 4 from sep_offsets F (c := 180) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xA0) 4 from sep_offsets F (c := 252) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xA0) 4 from sep_offsets F (c := 132) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xA0) 4 from sep_offsets F (c := 140) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), slA0]
  have soA4 : memLoad32 Mm583 (F + 0xA4) = v357 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xA4) 4 from sep_offsets F (c := 180) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xA4) 4 from sep_offsets F (c := 252) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xA4) 4 from sep_offsets F (c := 132) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xA4) 4 from sep_offsets F (c := 140) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), slA4]
  have soA8 : memLoad32 Mm583 (F + 0xA8) = v279 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xA8) 4 from sep_offsets F (c := 180) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xA8) 4 from sep_offsets F (c := 252) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xA8) 4 from sep_offsets F (c := 132) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xA8) 4 from sep_offsets F (c := 140) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), slA8]
  have soAC : memLoad32 Mm583 (F + 0xAC) = v219 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xAC) 4 from sep_offsets F (c := 180) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xAC) 4 from sep_offsets F (c := 252) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xAC) 4 from sep_offsets F (c := 132) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xAC) 4 from sep_offsets F (c := 140) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), slAC]
  have soB4 : memLoad32 Mm583 (F + 0xB4) = v582 := by
    rw [← hM583, memLoad32_store32_same]
  have soB8 : memLoad32 Mm583 (F + 0xB8) = v136 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xB8) 4 from sep_offsets F (c := 180) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xB8) 4 from sep_offsets F (c := 252) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xB8) 4 from sep_offsets F (c := 132) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xB8) 4 from sep_offsets F (c := 140) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm583 (F + 0xBC) = v467 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xBC) 4 from sep_offsets F (c := 180) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xBC) 4 from sep_offsets F (c := 252) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xBC) 4 from sep_offsets F (c := 132) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xBC) 4 from sep_offsets F (c := 140) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm583 (F + 0xC0) = v405 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xC0) 4 from sep_offsets F (c := 180) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xC0) 4 from sep_offsets F (c := 252) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xC0) 4 from sep_offsets F (c := 132) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xC0) 4 from sep_offsets F (c := 140) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC4 : memLoad32 Mm583 (F + 0xC4) = v199 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xC4) 4 from sep_offsets F (c := 180) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xC4) 4 from sep_offsets F (c := 252) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xC4) 4 from sep_offsets F (c := 132) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xC4) 4 from sep_offsets F (c := 140) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), slC4]
  have soC8 : memLoad32 Mm583 (F + 0xC8) = v335 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xC8) 4 from sep_offsets F (c := 180) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xC8) 4 from sep_offsets F (c := 252) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xC8) 4 from sep_offsets F (c := 132) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xC8) 4 from sep_offsets F (c := 140) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soCC : memLoad32 Mm583 (F + 0xCC) = v264 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xCC) 4 from sep_offsets F (c := 180) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xCC) 4 from sep_offsets F (c := 252) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xCC) 4 from sep_offsets F (c := 132) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xCC) 4 from sep_offsets F (c := 140) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), slCC]
  have soD0 : memLoad32 Mm583 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xD0) 4 from sep_offsets F (c := 180) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xD0) 4 from sep_offsets F (c := 252) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xD0) 4 from sep_offsets F (c := 132) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xD0) 4 from sep_offsets F (c := 140) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soD4 : memLoad32 Mm583 (F + 0xD4) = v239 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xD4) 4 from sep_offsets F (c := 180) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xD4) 4 from sep_offsets F (c := 252) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xD4) 4 from sep_offsets F (c := 132) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xD4) 4 from sep_offsets F (c := 140) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), slD4]
  have soD8 : memLoad32 Mm583 (F + 0xD8) = v174 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xD8) 4 from sep_offsets F (c := 180) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xD8) 4 from sep_offsets F (c := 252) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xD8) 4 from sep_offsets F (c := 132) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xD8) 4 from sep_offsets F (c := 140) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), slD8]
  have soDC : memLoad32 Mm583 (F + 0xDC) = v150 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xDC) 4 from sep_offsets F (c := 180) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xDC) 4 from sep_offsets F (c := 252) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xDC) 4 from sep_offsets F (c := 132) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xDC) 4 from sep_offsets F (c := 140) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), slDC]
  have soE0 : memLoad32 Mm583 (F + 0xE0) = v133 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xE0) 4 from sep_offsets F (c := 180) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xE0) 4 from sep_offsets F (c := 252) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xE0) 4 from sep_offsets F (c := 132) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xE0) 4 from sep_offsets F (c := 140) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE4 : memLoad32 Mm583 (F + 0xE4) = v7 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xE4) 4 from sep_offsets F (c := 180) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xE4) 4 from sep_offsets F (c := 252) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xE4) 4 from sep_offsets F (c := 132) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xE4) 4 from sep_offsets F (c := 140) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), slE4]
  have soEC : memLoad32 Mm583 (F + 0xEC) = v341 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xEC) 4 from sep_offsets F (c := 180) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xEC) 4 from sep_offsets F (c := 252) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xEC) 4 from sep_offsets F (c := 132) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xEC) 4 from sep_offsets F (c := 140) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF0 : memLoad32 Mm583 (F + 0xF0) = v206 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xF0) 4 from sep_offsets F (c := 180) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xF0) 4 from sep_offsets F (c := 252) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xF0) 4 from sep_offsets F (c := 132) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xF0) 4 from sep_offsets F (c := 140) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), slF0]
  have soF4 : memLoad32 Mm583 (F + 0xF4) = v297 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xF4) 4 from sep_offsets F (c := 180) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xF4) 4 from sep_offsets F (c := 252) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xF4) 4 from sep_offsets F (c := 132) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xF4) 4 from sep_offsets F (c := 140) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), slF4]
  have soF8 : memLoad32 Mm583 (F + 0xF8) = v284 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xF8) 4 from sep_offsets F (c := 180) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0xF8) 4 from sep_offsets F (c := 252) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0xF8) 4 from sep_offsets F (c := 132) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0xF8) 4 from sep_offsets F (c := 140) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have soFC : memLoad32 Mm583 (F + 0xFC) = v579 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0xFC) 4 from sep_offsets F (c := 180) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_same]
  have so100 : memLoad32 Mm583 (F + 0x100) = v540 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x100) 4 from sep_offsets F (c := 180) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x100) 4 from sep_offsets F (c := 252) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x100) 4 from sep_offsets F (c := 132) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x100) 4 from sep_offsets F (c := 140) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm583 (F + 0x104) = v62 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x104) 4 from sep_offsets F (c := 180) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x104) 4 from sep_offsets F (c := 252) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x104) 4 from sep_offsets F (c := 132) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x104) 4 from sep_offsets F (c := 140) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 Mm583 (F + 0x108) = v203 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x108) 4 from sep_offsets F (c := 180) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x108) 4 from sep_offsets F (c := 252) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x108) 4 from sep_offsets F (c := 132) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x108) 4 from sep_offsets F (c := 140) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 Mm583 (F + 0x10C) = v274 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x10C) 4 from sep_offsets F (c := 180) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x10C) 4 from sep_offsets F (c := 252) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x10C) 4 from sep_offsets F (c := 132) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x10C) 4 from sep_offsets F (c := 140) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm583 (F + 0x110) = v67 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x110) 4 from sep_offsets F (c := 180) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x110) 4 from sep_offsets F (c := 252) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x110) 4 from sep_offsets F (c := 132) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x110) 4 from sep_offsets F (c := 140) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm583 (F + 0x114) = v111 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x114) 4 from sep_offsets F (c := 180) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x114) 4 from sep_offsets F (c := 252) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x114) 4 from sep_offsets F (c := 132) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x114) 4 from sep_offsets F (c := 140) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm583 (F + 0x118) = v122 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x118) 4 from sep_offsets F (c := 180) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x118) 4 from sep_offsets F (c := 252) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x118) 4 from sep_offsets F (c := 132) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x118) 4 from sep_offsets F (c := 140) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 Mm583 (F + 0x11C) = v231 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x11C) 4 from sep_offsets F (c := 180) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x11C) 4 from sep_offsets F (c := 252) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x11C) 4 from sep_offsets F (c := 132) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x11C) 4 from sep_offsets F (c := 140) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so120 : memLoad32 Mm583 (F + 0x120) = v116 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x120) 4 from sep_offsets F (c := 180) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x120) 4 from sep_offsets F (c := 252) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x120) 4 from sep_offsets F (c := 132) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x120) 4 from sep_offsets F (c := 140) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm583 (F + 0x124) = v124 := by
    rw [← hM583, memLoad32_store32_sep (show Sep (F + 0xB4) 4 (F + 0x124) 4 from sep_offsets F (c := 180) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM580, memLoad32_store32_sep (show Sep (F + 0xFC) 4 (F + 0x124) 4 from sep_offsets F (c := 252) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM573, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x124) 4 from sep_offsets F (c := 132) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM560, memLoad32_store32_sep (show Sep (F + 0x8C) 4 (F + 0x124) 4 from sep_offsets F (c := 140) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n599, Mm583, v562, v563, v564, v566, v567, v568, v569, v570, v571, v572, v574, v576, v577, v579, v581, v582, v584, v585, v586, v587, v588, v589, v590, v592, v593, v594, v595, v596, v597, v598, v599, (.cons d560 (.cons d561 (.cons d562 (.cons d563 (.cons d564 (.cons d565 (.cons d566 (.cons d567 (.cons d568 (.cons d569 (.cons d570 (.cons d571 (.cons d572 (.cons d573 (.cons d574 (.cons d575 (.cons d576 (.cons d577 (.cons d578 (.cons d579 (.cons d580 (.cons d581 (.cons d582 (.cons d583 (.cons d584 (.cons d585 (.cons d586 (.cons d587 (.cons d588 (.cons d589 (.cons d590 (.cons d591 (.cons d592 (.cons d593 (.cons d594 (.cons d595 (.cons d596 (.cons d597 (.cons d598 (.single d599)))))))))))))))))))))))))))))))))))))))), u599.self, hc583, fr583, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so78, so84, so8C, so90, so94, so9C, soA0, soA4, soA8, soAC, soB4, soB8, soBC, soC0, soC4, soC8, soCC, soD0, soD4, soD8, soDC, soE0, soE4, soEC, soF0, soF4, soF8, soFC, so100, so104, so108, so10C, so110, so114, so118, so11C, so120, so124, hv562, hv563, hv564, hv566, hv567, hv568, hv569, hv570, hv571, hv572, hv574, hv576, hv577, hv579, hv581, hv582, hv584, hv585, hv586, hv587, hv588, hv589, hv590, hv592, hv593, hv594, hv595, hv596, hv597, hv598, hv599⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g17 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v62 v67 v75 v87 v111 v116 v122 v124 v133 v136 v150 v151 v174 v199 v203 v206 v219 v231 v239 v254 v264 v274 v279 v284 v297 v302 v308 v310 v335 v341 v352 v357 v388 v405 v409 v419 v467 v476 v480 v481 v485 v537 v540 v545 v557 v559 v568 v572 v576 v579 v582 v585 v587 v588 v589 v590 v592 v593 v594 v595 v596 v598 v599 : Word}
    (s : St Mi B n 0x8DC (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v409)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v576)
    (q6 : reg n (6 : Fin 32) = v419)
    (q7 : reg n (7 : Fin 32) = v592)
    (q8 : reg n (8 : Fin 32) = v568)
    (q9 : reg n (9 : Fin 32) = v590)
    (q10 : reg n a0 = v599)
    (q11 : reg n a1 = v585)
    (q12 : reg n a2 = v308)
    (q13 : reg n a3 = v588)
    (q14 : reg n a4 = v596)
    (q15 : reg n a5 = v589)
    (q16 : reg n a6 = v594)
    (q17 : reg n a7 = v595)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v593)
    (q20 : reg n (20 : Fin 32) = v310)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v557)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v476)
    (q25 : reg n (25 : Fin 32) = v352)
    (q26 : reg n (26 : Fin 32) = v480)
    (q27 : reg n (27 : Fin 32) = v598)
    (q28 : reg n (28 : Fin 32) = v254)
    (q29 : reg n (29 : Fin 32) = v587)
    (q30 : reg n (30 : Fin 32) = v388)
    (q31 : reg n (31 : Fin 32) = v537)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl78 : memLoad32 Mi (F + 0x78) = v545)
    (sl84 : memLoad32 Mi (F + 0x84) = v572)
    (sl8C : memLoad32 Mi (F + 0x8C) = v559)
    (sl90 : memLoad32 Mi (F + 0x90) = v151)
    (sl94 : memLoad32 Mi (F + 0x94) = v481)
    (sl9C : memLoad32 Mi (F + 0x9C) = v75)
    (slA0 : memLoad32 Mi (F + 0xA0) = v87)
    (slA4 : memLoad32 Mi (F + 0xA4) = v357)
    (slA8 : memLoad32 Mi (F + 0xA8) = v279)
    (slAC : memLoad32 Mi (F + 0xAC) = v219)
    (slB4 : memLoad32 Mi (F + 0xB4) = v582)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slD4 : memLoad32 Mi (F + 0xD4) = v239)
    (slD8 : memLoad32 Mi (F + 0xD8) = v174)
    (slDC : memLoad32 Mi (F + 0xDC) = v150)
    (slE0 : memLoad32 Mi (F + 0xE0) = v133)
    (slE4 : memLoad32 Mi (F + 0xE4) = v7)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slF4 : memLoad32 Mi (F + 0xF4) = v297)
    (slF8 : memLoad32 Mi (F + 0xF8) = v284)
    (slFC : memLoad32 Mi (F + 0xFC) = v579)
    (sl100 : memLoad32 Mi (F + 0x100) = v540)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v601 v602 v603 v604 v606 v607 v608 v609 v610 v612 v613 v614 v615 v616 v618 v620 v621 v622 v624 v625 v627 v628 v629 v630 v631 v632 v633 v634 v635 v636 v637 v638 v639 : Word),
      Steps n n' ∧
      St M' B n' 0x954 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v409 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v576 ∧
      reg n' (6 : Fin 32) = v419 ∧
      reg n' (7 : Fin 32) = v592 ∧
      reg n' (8 : Fin 32) = v239 ∧
      reg n' (9 : Fin 32) = v625 ∧
      reg n' a0 = v639 ∧
      reg n' a1 = v585 ∧
      reg n' a2 = v621 ∧
      reg n' a3 = v630 ∧
      reg n' a4 = v637 ∧
      reg n' a5 = v615 ∧
      reg n' a6 = v633 ∧
      reg n' a7 = v627 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v593 ∧
      reg n' (20 : Fin 32) = v310 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v476 ∧
      reg n' (25 : Fin 32) = v352 ∧
      reg n' (26 : Fin 32) = v480 ∧
      reg n' (27 : Fin 32) = v598 ∧
      reg n' (28 : Fin 32) = v254 ∧
      reg n' (29 : Fin 32) = v638 ∧
      reg n' (30 : Fin 32) = v388 ∧
      reg n' (31 : Fin 32) = v537 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x78) = v545 ∧
      memLoad32 M' (F + 0x84) = v572 ∧
      memLoad32 M' (F + 0x8C) = v559 ∧
      memLoad32 M' (F + 0x90) = v151 ∧
      memLoad32 M' (F + 0x94) = v481 ∧
      memLoad32 M' (F + 0x98) = v352 ∧
      memLoad32 M' (F + 0x9C) = v75 ∧
      memLoad32 M' (F + 0xA0) = v87 ∧
      memLoad32 M' (F + 0xA4) = v357 ∧
      memLoad32 M' (F + 0xA8) = v279 ∧
      memLoad32 M' (F + 0xAC) = v219 ∧
      memLoad32 M' (F + 0xB4) = v582 ∧
      memLoad32 M' (F + 0xB8) = v136 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xCC) = v264 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xD4) = v239 ∧
      memLoad32 M' (F + 0xD8) = v174 ∧
      memLoad32 M' (F + 0xDC) = v150 ∧
      memLoad32 M' (F + 0xE0) = v133 ∧
      memLoad32 M' (F + 0xE4) = v7 ∧
      memLoad32 M' (F + 0xE8) = v419 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xF4) = v297 ∧
      memLoad32 M' (F + 0xF8) = v284 ∧
      memLoad32 M' (F + 0xFC) = v579 ∧
      memLoad32 M' (F + 0x100) = v540 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .sltu v588 v62 = v601 ∧
      aluEval .sub v588 v62 = v602 ∧
      aluEval .sub v589 v601 = v603 ∧
      aluEval .add v602 v590 = v604 ∧
      aluEval .sub v603 v67 = v606 ∧
      aluEval .sltu v604 v602 = v607 ∧
      aluEval .add v606 v594 = v608 ∧
      aluEval .add v607 v595 = v609 ∧
      aluEval .add v609 v608 = v610 ∧
      aluEval .add 0 0x14D = v612 ∧
      aluEval .mul v352 v612 = v613 ∧
      aluEval .add v604 v599 = v614 ∧
      aluEval .mulhu v352 v612 = v615 ∧
      aluEval .sltu v614 v604 = v616 ∧
      aluEval .mul v419 v302 = v618 ∧
      aluEval .add v284 v616 = v620 ∧
      aluEval .mulhu v419 v302 = v621 ∧
      aluEval .add v610 v620 = v622 ∧
      aluEval .add v297 v614 = v624 ∧
      aluEval .sltu v624 v614 = v625 ∧
      aluEval .mulhu v485 v239 = v627 ∧
      aluEval .add v622 v625 = v628 ∧
      aluEval .add v613 v624 = v629 ∧
      aluEval .add v628 v615 = v630 ∧
      aluEval .sltu v629 v624 = v631 ∧
      aluEval .add v631 v630 = v632 ∧
      aluEval .add v618 v629 = v633 ∧
      aluEval .add v632 v621 = v634 ∧
      aluEval .sltu v633 v629 = v635 ∧
      aluEval .add v634 v635 = v636 ∧
      (0x16893000 : Word) = v637 ∧
      aluEval .add v636 v627 = v638 ∧
      aluEval .add v637 0x166 = v639 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n600, d600, u600⟩ := s.lwE hc ev_at_8dc (off' := 0x8E0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 260) (by decide)) (v := v62)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl104])
  obtain ⟨n601, v601, d601, hv601, u601⟩ := u600.aluG hc ev_at_8e0 (off' := 0x8E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv601
  obtain ⟨n602, v602, d602, hv602, u602⟩ := u601.aluG hc ev_at_8e4 (off' := 0x8E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv602
  obtain ⟨n603, v603, d603, hv603, u603⟩ := u602.aluG hc ev_at_8e6 (off' := 0x8E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv603
  obtain ⟨n604, v604, d604, hv604, u604⟩ := u603.aluG hc ev_at_8e8 (off' := 0x8EC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv604
  obtain ⟨n605, d605, u605⟩ := u604.lwE hc ev_at_8ec (off' := 0x8F0) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 272) (by decide)) (v := v67)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl110])
  obtain ⟨n606, v606, d606, hv606, u606⟩ := u605.aluG hc ev_at_8f0 (off' := 0x8F4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv606
  obtain ⟨n607, v607, d607, hv607, u607⟩ := u606.aluG hc ev_at_8f4 (off' := 0x8F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv607
  obtain ⟨n608, v608, d608, hv608, u608⟩ := u607.aluG hc ev_at_8f8 (off' := 0x8FA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv608
  obtain ⟨n609, v609, d609, hv609, u609⟩ := u608.aluG hc ev_at_8fa (off' := 0x8FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv609
  obtain ⟨n610, v610, d610, hv610, u610⟩ := u609.aluG hc ev_at_8fc (off' := 0x8FE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv610
  obtain ⟨n611, d611, u611⟩ := u610.swG hc ev_at_8fe (off' := 0x900) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 152) (by decide)) (a := F + 0x98) (v := v352)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm611, hM611⟩ : ∃ M', memStore32 Mi (F + 0x98) v352 = M' := ⟨_, rfl⟩
  rw [hM611] at u611
  have hc611 : CodeIn Mm611 B ed25519VerifyCode := by rw [← hM611]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr611 : ∀ x, Sep F 0x128 x 1 → Mm611 x = M0 x := fun x hx => by
    rw [← hM611, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n612, v612, d612, hv612, u612⟩ := u611.aluImmG hc611 ev_at_900 (off' := 0x904) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv612
  obtain ⟨n613, v613, d613, hv613, u613⟩ := u612.aluG hc611 ev_at_904 (off' := 0x908) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv613
  obtain ⟨n614, v614, d614, hv614, u614⟩ := u613.aluG hc611 ev_at_908 (off' := 0x90C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv614
  obtain ⟨n615, v615, d615, hv615, u615⟩ := u614.aluG hc611 ev_at_90c (off' := 0x910) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv615
  obtain ⟨n616, v616, d616, hv616, u616⟩ := u615.aluG hc611 ev_at_910 (off' := 0x914) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv616
  obtain ⟨n617, d617, u617⟩ := u616.swG hc611 ev_at_914 (off' := 0x916) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 232) (by decide)) (a := F + 0xE8) (v := v419)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm617, hM617⟩ : ∃ M', memStore32 Mm611 (F + 0xE8) v419 = M' := ⟨_, rfl⟩
  rw [hM617] at u617
  have hc617 : CodeIn Mm617 B ed25519VerifyCode := by rw [← hM617]; exact hc611.store32 (frm_sep' sFC (by decide))
  have fr617 : ∀ x, Sep F 0x128 x 1 → Mm617 x = M0 x := fun x hx => by
    rw [← hM617, memStore32_get_sep (frm_sep' hx (by decide)), fr611 x hx]
  obtain ⟨n618, v618, d618, hv618, u618⟩ := u617.aluG hc617 ev_at_916 (off' := 0x91A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv618
  obtain ⟨n619, d619, u619⟩ := u618.lwE hc617 ev_at_91a (off' := 0x91C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 248) (by decide)) (v := v284)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xF8) 4 from sep_offsets F (c := 232) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xF8) 4 from sep_offsets F (c := 152) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8])
  obtain ⟨n620, v620, d620, hv620, u620⟩ := u619.aluG hc617 ev_at_91c (off' := 0x91E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv620
  obtain ⟨n621, v621, d621, hv621, u621⟩ := u620.aluG hc617 ev_at_91e (off' := 0x922) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv621
  obtain ⟨n622, v622, d622, hv622, u622⟩ := u621.aluG hc617 ev_at_922 (off' := 0x924) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv622
  obtain ⟨n623, d623, u623⟩ := u622.lwE hc617 ev_at_924 (off' := 0x926) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 244) (by decide)) (v := v297)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xF4) 4 from sep_offsets F (c := 232) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xF4) 4 from sep_offsets F (c := 152) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), slF4])
  obtain ⟨n624, v624, d624, hv624, u624⟩ := u623.aluG hc617 ev_at_926 (off' := 0x928) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv624
  obtain ⟨n625, v625, d625, hv625, u625⟩ := u624.aluG hc617 ev_at_928 (off' := 0x92C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv625
  obtain ⟨n626, d626, u626⟩ := u625.lwE hc617 ev_at_92c (off' := 0x92E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 212) (by decide)) (v := v239)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xD4) 4 from sep_offsets F (c := 232) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xD4) 4 from sep_offsets F (c := 152) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), slD4])
  obtain ⟨n627, v627, d627, hv627, u627⟩ := u626.aluG hc617 ev_at_92e (off' := 0x932) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv627
  obtain ⟨n628, v628, d628, hv628, u628⟩ := u627.aluG hc617 ev_at_932 (off' := 0x934) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv628
  obtain ⟨n629, v629, d629, hv629, u629⟩ := u628.aluG hc617 ev_at_934 (off' := 0x936) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv629
  obtain ⟨n630, v630, d630, hv630, u630⟩ := u629.aluG hc617 ev_at_936 (off' := 0x938) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv630
  obtain ⟨n631, v631, d631, hv631, u631⟩ := u630.aluG hc617 ev_at_938 (off' := 0x93C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv631
  obtain ⟨n632, v632, d632, hv632, u632⟩ := u631.aluG hc617 ev_at_93c (off' := 0x93E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv632
  obtain ⟨n633, v633, d633, hv633, u633⟩ := u632.aluG hc617 ev_at_93e (off' := 0x940) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv633
  obtain ⟨n634, v634, d634, hv634, u634⟩ := u633.aluG hc617 ev_at_940 (off' := 0x942) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv634
  obtain ⟨n635, v635, d635, hv635, u635⟩ := u634.aluG hc617 ev_at_942 (off' := 0x946) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv635
  obtain ⟨n636, v636, d636, hv636, u636⟩ := u635.aluG hc617 ev_at_946 (off' := 0x948) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv636
  obtain ⟨n637, v637, d637, hv637, u637⟩ := u636.luiG hc617 ev_at_948 (off' := 0x94C) (by decide)
  obtain ⟨n638, v638, d638, hv638, u638⟩ := u637.aluG hc617 ev_at_94c (off' := 0x950) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv638
  obtain ⟨n639, v639, d639, hv639, u639⟩ := u638.aluImmG hc617 ev_at_950 (off' := 0x954) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv639
  have qo1 : reg n639 ra = v409 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n639 sp = F := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n639 (3 : Fin 32) = G3 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n639 (4 : Fin 32) = G4 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n639 (5 : Fin 32) = v576 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n639 (6 : Fin 32) = v419 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n639 (7 : Fin 32) = v592 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n639 (8 : Fin 32) = v239 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n639 (9 : Fin 32) = v625 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n639 a0 = v639 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n639 a1 = v585 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n639 a2 = v621 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n639 a3 = v630 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n639 a4 = v637 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n639 a5 = v615 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n639 a6 = v633 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n639 a7 = v627 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n639 (18 : Fin 32) = v7 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n639 (19 : Fin 32) = v593 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n639 (20 : Fin 32) = v310 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n639 (21 : Fin 32) = v485 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n639 (22 : Fin 32) = v557 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n639 (23 : Fin 32) = v302 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n639 (24 : Fin 32) = v476 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n639 (25 : Fin 32) = v352 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n639 (26 : Fin 32) = v480 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n639 (27 : Fin 32) = v598 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n639 (28 : Fin 32) = v254 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n639 (29 : Fin 32) = v638 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n639 (30 : Fin 32) = v388 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n639 (31 : Fin 32) = v537 := by rw [u639.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm617 (F + 0xC) = G21 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xC) 4 from sep_offsets F (c := 232) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xC) 4 from sep_offsets F (c := 152) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm617 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x10) 4 from sep_offsets F (c := 232) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x10) 4 from sep_offsets F (c := 152) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so78 : memLoad32 Mm617 (F + 0x78) = v545 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x78) 4 from sep_offsets F (c := 232) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x78) 4 from sep_offsets F (c := 152) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so84 : memLoad32 Mm617 (F + 0x84) = v572 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x84) 4 from sep_offsets F (c := 232) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x84) 4 from sep_offsets F (c := 152) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84]
  have so8C : memLoad32 Mm617 (F + 0x8C) = v559 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x8C) 4 from sep_offsets F (c := 232) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x8C) 4 from sep_offsets F (c := 152) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 Mm617 (F + 0x90) = v151 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x90) 4 from sep_offsets F (c := 232) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x90) 4 from sep_offsets F (c := 152) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 Mm617 (F + 0x94) = v481 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x94) 4 from sep_offsets F (c := 232) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x94) 4 from sep_offsets F (c := 152) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so98 : memLoad32 Mm617 (F + 0x98) = v352 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x98) 4 from sep_offsets F (c := 232) (n := 4) (d := 152) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_same]
  have so9C : memLoad32 Mm617 (F + 0x9C) = v75 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x9C) 4 from sep_offsets F (c := 232) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x9C) 4 from sep_offsets F (c := 152) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  have soA0 : memLoad32 Mm617 (F + 0xA0) = v87 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xA0) 4 from sep_offsets F (c := 232) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xA0) 4 from sep_offsets F (c := 152) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), slA0]
  have soA4 : memLoad32 Mm617 (F + 0xA4) = v357 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xA4) 4 from sep_offsets F (c := 232) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xA4) 4 from sep_offsets F (c := 152) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), slA4]
  have soA8 : memLoad32 Mm617 (F + 0xA8) = v279 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xA8) 4 from sep_offsets F (c := 232) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xA8) 4 from sep_offsets F (c := 152) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), slA8]
  have soAC : memLoad32 Mm617 (F + 0xAC) = v219 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xAC) 4 from sep_offsets F (c := 232) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xAC) 4 from sep_offsets F (c := 152) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), slAC]
  have soB4 : memLoad32 Mm617 (F + 0xB4) = v582 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xB4) 4 from sep_offsets F (c := 232) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xB4) 4 from sep_offsets F (c := 152) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), slB4]
  have soB8 : memLoad32 Mm617 (F + 0xB8) = v136 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xB8) 4 from sep_offsets F (c := 232) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xB8) 4 from sep_offsets F (c := 152) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm617 (F + 0xBC) = v467 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xBC) 4 from sep_offsets F (c := 232) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xBC) 4 from sep_offsets F (c := 152) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm617 (F + 0xC0) = v405 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xC0) 4 from sep_offsets F (c := 232) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xC0) 4 from sep_offsets F (c := 152) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC4 : memLoad32 Mm617 (F + 0xC4) = v199 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xC4) 4 from sep_offsets F (c := 232) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xC4) 4 from sep_offsets F (c := 152) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), slC4]
  have soC8 : memLoad32 Mm617 (F + 0xC8) = v335 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xC8) 4 from sep_offsets F (c := 232) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xC8) 4 from sep_offsets F (c := 152) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soCC : memLoad32 Mm617 (F + 0xCC) = v264 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xCC) 4 from sep_offsets F (c := 232) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xCC) 4 from sep_offsets F (c := 152) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), slCC]
  have soD0 : memLoad32 Mm617 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xD0) 4 from sep_offsets F (c := 232) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xD0) 4 from sep_offsets F (c := 152) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soD4 : memLoad32 Mm617 (F + 0xD4) = v239 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xD4) 4 from sep_offsets F (c := 232) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xD4) 4 from sep_offsets F (c := 152) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), slD4]
  have soD8 : memLoad32 Mm617 (F + 0xD8) = v174 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xD8) 4 from sep_offsets F (c := 232) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xD8) 4 from sep_offsets F (c := 152) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), slD8]
  have soDC : memLoad32 Mm617 (F + 0xDC) = v150 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xDC) 4 from sep_offsets F (c := 232) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xDC) 4 from sep_offsets F (c := 152) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), slDC]
  have soE0 : memLoad32 Mm617 (F + 0xE0) = v133 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xE0) 4 from sep_offsets F (c := 232) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xE0) 4 from sep_offsets F (c := 152) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE4 : memLoad32 Mm617 (F + 0xE4) = v7 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xE4) 4 from sep_offsets F (c := 232) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xE4) 4 from sep_offsets F (c := 152) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), slE4]
  have soE8 : memLoad32 Mm617 (F + 0xE8) = v419 := by
    rw [← hM617, memLoad32_store32_same]
  have soEC : memLoad32 Mm617 (F + 0xEC) = v341 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xEC) 4 from sep_offsets F (c := 232) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xEC) 4 from sep_offsets F (c := 152) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF0 : memLoad32 Mm617 (F + 0xF0) = v206 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xF0) 4 from sep_offsets F (c := 232) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xF0) 4 from sep_offsets F (c := 152) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), slF0]
  have soF4 : memLoad32 Mm617 (F + 0xF4) = v297 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xF4) 4 from sep_offsets F (c := 232) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xF4) 4 from sep_offsets F (c := 152) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), slF4]
  have soF8 : memLoad32 Mm617 (F + 0xF8) = v284 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xF8) 4 from sep_offsets F (c := 232) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xF8) 4 from sep_offsets F (c := 152) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have soFC : memLoad32 Mm617 (F + 0xFC) = v579 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0xFC) 4 from sep_offsets F (c := 232) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0xFC) 4 from sep_offsets F (c := 152) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm617 (F + 0x100) = v540 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x100) 4 from sep_offsets F (c := 232) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x100) 4 from sep_offsets F (c := 152) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so108 : memLoad32 Mm617 (F + 0x108) = v203 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x108) 4 from sep_offsets F (c := 232) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x108) 4 from sep_offsets F (c := 152) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 Mm617 (F + 0x10C) = v274 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x10C) 4 from sep_offsets F (c := 232) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x10C) 4 from sep_offsets F (c := 152) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so114 : memLoad32 Mm617 (F + 0x114) = v111 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x114) 4 from sep_offsets F (c := 232) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x114) 4 from sep_offsets F (c := 152) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm617 (F + 0x118) = v122 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x118) 4 from sep_offsets F (c := 232) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x118) 4 from sep_offsets F (c := 152) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 Mm617 (F + 0x11C) = v231 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x11C) 4 from sep_offsets F (c := 232) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x11C) 4 from sep_offsets F (c := 152) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so120 : memLoad32 Mm617 (F + 0x120) = v116 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x120) 4 from sep_offsets F (c := 232) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x120) 4 from sep_offsets F (c := 152) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm617 (F + 0x124) = v124 := by
    rw [← hM617, memLoad32_store32_sep (show Sep (F + 0xE8) 4 (F + 0x124) 4 from sep_offsets F (c := 232) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM611, memLoad32_store32_sep (show Sep (F + 0x98) 4 (F + 0x124) 4 from sep_offsets F (c := 152) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n639, Mm617, v601, v602, v603, v604, v606, v607, v608, v609, v610, v612, v613, v614, v615, v616, v618, v620, v621, v622, v624, v625, v627, v628, v629, v630, v631, v632, v633, v634, v635, v636, v637, v638, v639, (.cons d600 (.cons d601 (.cons d602 (.cons d603 (.cons d604 (.cons d605 (.cons d606 (.cons d607 (.cons d608 (.cons d609 (.cons d610 (.cons d611 (.cons d612 (.cons d613 (.cons d614 (.cons d615 (.cons d616 (.cons d617 (.cons d618 (.cons d619 (.cons d620 (.cons d621 (.cons d622 (.cons d623 (.cons d624 (.cons d625 (.cons d626 (.cons d627 (.cons d628 (.cons d629 (.cons d630 (.cons d631 (.cons d632 (.cons d633 (.cons d634 (.cons d635 (.cons d636 (.cons d637 (.cons d638 (.single d639)))))))))))))))))))))))))))))))))))))))), u639.self, hc617, fr617, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so78, so84, so8C, so90, so94, so98, so9C, soA0, soA4, soA8, soAC, soB4, soB8, soBC, soC0, soC4, soC8, soCC, soD0, soD4, soD8, soDC, soE0, soE4, soE8, soEC, soF0, soF4, soF8, soFC, so100, so108, so10C, so114, so118, so11C, so120, so124, hv601, hv602, hv603, hv604, hv606, hv607, hv608, hv609, hv610, hv612, hv613, hv614, hv615, hv616, hv618, hv620, hv621, hv622, hv624, hv625, hv627, hv628, hv629, hv630, hv631, hv632, hv633, hv634, hv635, hv636, hv637, hv638, hv639⟩

end C3.RV32
