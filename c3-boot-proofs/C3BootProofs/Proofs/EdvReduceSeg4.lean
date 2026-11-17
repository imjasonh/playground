import C3BootProofs.Proofs.EdvReduceFacts

/-! # The inlined `Scalar::reduce` in `ed25519_verify`, segments 13 to 15

Each theorem steps 40 instructions. `scripts/gen-ev-reduce.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g13 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v15 v16 v36 v40 v51 v62 v67 v75 v87 v111 v116 v122 v124 v133 v136 v150 v151 v174 v175 v185 v199 v203 v206 v219 v231 v236 v239 v254 v264 v274 v279 v284 v297 v302 v308 v310 v312 v320 v321 v335 v337 v341 v351 v352 v357 v378 v379 v388 v400 v405 v409 v419 v421 v429 v430 v431 v435 v436 v437 v438 v439 : Word}
    (s : St Mi B n 0x6FE (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v409)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v279)
    (q6 : reg n (6 : Fin 32) = v419)
    (q7 : reg n (7 : Fin 32) = v400)
    (q8 : reg n (8 : Fin 32) = v206)
    (q9 : reg n (9 : Fin 32) = v439)
    (q10 : reg n a0 = v437)
    (q11 : reg n a1 = v436)
    (q12 : reg n a2 = v203)
    (q13 : reg n a3 = v435)
    (q14 : reg n a4 = v438)
    (q15 : reg n a5 = v431)
    (q16 : reg n a6 = v429)
    (q17 : reg n a7 = v351)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v133)
    (q20 : reg n (20 : Fin 32) = v352)
    (q21 : reg n (21 : Fin 32) = v379)
    (q22 : reg n (22 : Fin 32) = v430)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v421)
    (q25 : reg n (25 : Fin 32) = v239)
    (q26 : reg n (26 : Fin 32) = v219)
    (q27 : reg n (27 : Fin 32) = v174)
    (q28 : reg n (28 : Fin 32) = v378)
    (q29 : reg n (29 : Fin 32) = v321)
    (q30 : reg n (30 : Fin 32) = v388)
    (q31 : reg n (31 : Fin 32) = v150)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl6C : memLoad32 Mi (F + 0x6C) = v310)
    (sl70 : memLoad32 Mi (F + 0x70) = v308)
    (sl74 : memLoad32 Mi (F + 0x74) = v320)
    (sl78 : memLoad32 Mi (F + 0x78) = v337)
    (sl7C : memLoad32 Mi (F + 0x7C) = v312)
    (sl80 : memLoad32 Mi (F + 0x80) = v254)
    (sl84 : memLoad32 Mi (F + 0x84) = v175)
    (sl88 : memLoad32 Mi (F + 0x88) = v36)
    (sl8C : memLoad32 Mi (F + 0x8C) = v236)
    (sl90 : memLoad32 Mi (F + 0x90) = v151)
    (sl94 : memLoad32 Mi (F + 0x94) = v185)
    (sl9C : memLoad32 Mi (F + 0x9C) = v75)
    (slA0 : memLoad32 Mi (F + 0xA0) = v87)
    (slA4 : memLoad32 Mi (F + 0xA4) = v357)
    (slAC : memLoad32 Mi (F + 0xAC) = v219)
    (slB0 : memLoad32 Mi (F + 0xB0) = v16)
    (slB4 : memLoad32 Mi (F + 0xB4) = v15)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slE0 : memLoad32 Mi (F + 0xE0) = v133)
    (slE4 : memLoad32 Mi (F + 0xE4) = v7)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slF4 : memLoad32 Mi (F + 0xF4) = v297)
    (slF8 : memLoad32 Mi (F + 0xF8) = v284)
    (slFC : memLoad32 Mi (F + 0xFC) = v40)
    (sl100 : memLoad32 Mi (F + 0x100) = v51)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v440 v441 v442 v443 v444 v445 v446 v449 v451 v452 v453 v454 v455 v456 v457 v458 v459 v460 v461 v462 v463 v464 v465 v466 v467 v470 v471 v472 v474 v476 v477 v479 : Word),
      Steps n n' ∧
      St M' B n' 0x76E (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v409 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v279 ∧
      reg n' (6 : Fin 32) = v419 ∧
      reg n' (7 : Fin 32) = v441 ∧
      reg n' (8 : Fin 32) = v457 ∧
      reg n' (9 : Fin 32) = v479 ∧
      reg n' a0 = v467 ∧
      reg n' a1 = v472 ∧
      reg n' a2 = v477 ∧
      reg n' a3 = v474 ∧
      reg n' a4 = v465 ∧
      reg n' a5 = v463 ∧
      reg n' a6 = v442 ∧
      reg n' a7 = v351 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v133 ∧
      reg n' (20 : Fin 32) = v310 ∧
      reg n' (21 : Fin 32) = v379 ∧
      reg n' (22 : Fin 32) = v455 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v476 ∧
      reg n' (25 : Fin 32) = v352 ∧
      reg n' (26 : Fin 32) = v219 ∧
      reg n' (27 : Fin 32) = v174 ∧
      reg n' (28 : Fin 32) = v239 ∧
      reg n' (29 : Fin 32) = v321 ∧
      reg n' (30 : Fin 32) = v388 ∧
      reg n' (31 : Fin 32) = v150 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x70) = v308 ∧
      memLoad32 M' (F + 0x74) = v320 ∧
      memLoad32 M' (F + 0x78) = v337 ∧
      memLoad32 M' (F + 0x7C) = v312 ∧
      memLoad32 M' (F + 0x80) = v254 ∧
      memLoad32 M' (F + 0x88) = v36 ∧
      memLoad32 M' (F + 0x8C) = v236 ∧
      memLoad32 M' (F + 0x90) = v151 ∧
      memLoad32 M' (F + 0x9C) = v75 ∧
      memLoad32 M' (F + 0xA0) = v87 ∧
      memLoad32 M' (F + 0xA4) = v357 ∧
      memLoad32 M' (F + 0xAC) = v219 ∧
      memLoad32 M' (F + 0xB0) = v16 ∧
      memLoad32 M' (F + 0xB8) = v136 ∧
      memLoad32 M' (F + 0xBC) = v467 ∧
      memLoad32 M' (F + 0xC0) = v405 ∧
      memLoad32 M' (F + 0xC4) = v199 ∧
      memLoad32 M' (F + 0xC8) = v335 ∧
      memLoad32 M' (F + 0xCC) = v264 ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M0 (F + 0xD0) ∧
      memLoad32 M' (F + 0xD8) = v174 ∧
      memLoad32 M' (F + 0xE0) = v133 ∧
      memLoad32 M' (F + 0xE4) = v7 ∧
      memLoad32 M' (F + 0xEC) = v341 ∧
      memLoad32 M' (F + 0xF0) = v206 ∧
      memLoad32 M' (F + 0xF4) = v297 ∧
      memLoad32 M' (F + 0xF8) = v284 ∧
      memLoad32 M' (F + 0xFC) = v40 ∧
      memLoad32 M' (F + 0x100) = v51 ∧
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .mul v279 v302 = v440 ∧
      aluEval .add v436 v439 = v441 ∧
      aluEval .add v429 v430 = v442 ∧
      aluEval .add v435 v431 = v443 ∧
      aluEval .sltu v442 v430 = v444 ∧
      aluEval .mul v352 v239 = v445 ∧
      aluEval .mulhu v352 v239 = v446 ∧
      aluEval .add v443 v444 = v449 ∧
      aluEval .mul v419 v174 = v451 ∧
      aluEval .add v449 v438 = v452 ∧
      aluEval .srl v437 0x1D = v453 ∧
      aluEval .add v440 v442 = v454 ∧
      aluEval .mulhu v419 v174 = v455 ∧
      aluEval .sltu v454 v442 = v456 ∧
      aluEval .sll v441 0x3 = v457 ∧
      aluEval .or v453 v457 = v458 ∧
      aluEval .add v452 v456 = v459 ∧
      aluEval .add v446 v459 = v460 ∧
      aluEval .add v445 v454 = v461 ∧
      aluEval .sltu v461 v454 = v462 ∧
      aluEval .add v451 v461 = v463 ∧
      aluEval .add v460 v462 = v464 ∧
      aluEval .add v463 v458 = v465 ∧
      aluEval .add v464 v455 = v466 ∧
      aluEval .mul v465 v133 = v467 ∧
      aluEval .sll v175 0x14 = v470 ∧
      aluEval .sltu v463 v461 = v471 ∧
      aluEval .add v466 v471 = v472 ∧
      aluEval .sub v470 v185 = v474 ∧
      aluEval .add v15 v185 = v476 ∧
      (0x3A617000 : Word) = v477 ∧
      aluEval .mulhu v185 v310 = v479 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n440, v440, d440, hv440, u440⟩ := s.aluG hc ev_at_6fe (off' := 0x702) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv440
  obtain ⟨n441, v441, d441, hv441, u441⟩ := u440.aluG hc ev_at_702 (off' := 0x706) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv441
  obtain ⟨n442, v442, d442, hv442, u442⟩ := u441.aluG hc ev_at_706 (off' := 0x708) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv442
  obtain ⟨n443, v443, d443, hv443, u443⟩ := u442.aluG hc ev_at_708 (off' := 0x70A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv443
  obtain ⟨n444, v444, d444, hv444, u444⟩ := u443.aluG hc ev_at_70a (off' := 0x70E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv444
  obtain ⟨n445, v445, d445, hv445, u445⟩ := u444.aluG hc ev_at_70e (off' := 0x712) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv445
  obtain ⟨n446, v446, d446, hv446, u446⟩ := u445.aluG hc ev_at_712 (off' := 0x716) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv446
  obtain ⟨n447, d447, u447⟩ := u446.aluE hc ev_at_716 (off' := 0x718) (by decide) (v := v239)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n448, d448, u448⟩ := u447.aluE hc ev_at_718 (off' := 0x71A) (by decide) (v := v352)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; first | exact BitVec.zero_add _ | exact BitVec.add_zero _)
  obtain ⟨n449, v449, d449, hv449, u449⟩ := u448.aluG hc ev_at_71a (off' := 0x71C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv449
  obtain ⟨n450, d450, u450⟩ := u449.swG hc ev_at_71c (off' := 0x71E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 216) (by decide)) (a := F + 0xD8) (v := v174)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm450, hM450⟩ : ∃ M', memStore32 Mi (F + 0xD8) v174 = M' := ⟨_, rfl⟩
  rw [hM450] at u450
  have hc450 : CodeIn Mm450 B ed25519VerifyCode := by rw [← hM450]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr450 : ∀ x, Sep F 0x128 x 1 → Mm450 x = M0 x := fun x hx => by
    rw [← hM450, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n451, v451, d451, hv451, u451⟩ := u450.aluG hc450 ev_at_71e (off' := 0x722) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv451
  obtain ⟨n452, v452, d452, hv452, u452⟩ := u451.aluG hc450 ev_at_722 (off' := 0x724) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv452
  obtain ⟨n453, v453, d453, hv453, u453⟩ := u452.aluImmG hc450 ev_at_724 (off' := 0x726) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv453
  obtain ⟨n454, v454, d454, hv454, u454⟩ := u453.aluG hc450 ev_at_726 (off' := 0x728) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv454
  obtain ⟨n455, v455, d455, hv455, u455⟩ := u454.aluG hc450 ev_at_728 (off' := 0x72C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv455
  obtain ⟨n456, v456, d456, hv456, u456⟩ := u455.aluG hc450 ev_at_72c (off' := 0x730) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv456
  obtain ⟨n457, v457, d457, hv457, u457⟩ := u456.aluImmG hc450 ev_at_730 (off' := 0x734) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv457
  obtain ⟨n458, v458, d458, hv458, u458⟩ := u457.aluG hc450 ev_at_734 (off' := 0x736) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv458
  obtain ⟨n459, v459, d459, hv459, u459⟩ := u458.aluG hc450 ev_at_736 (off' := 0x738) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv459
  obtain ⟨n460, v460, d460, hv460, u460⟩ := u459.aluG hc450 ev_at_738 (off' := 0x73A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv460
  obtain ⟨n461, v461, d461, hv461, u461⟩ := u460.aluG hc450 ev_at_73a (off' := 0x73C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv461
  obtain ⟨n462, v462, d462, hv462, u462⟩ := u461.aluG hc450 ev_at_73c (off' := 0x740) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv462
  obtain ⟨n463, v463, d463, hv463, u463⟩ := u462.aluG hc450 ev_at_740 (off' := 0x742) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv463
  obtain ⟨n464, v464, d464, hv464, u464⟩ := u463.aluG hc450 ev_at_742 (off' := 0x744) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv464
  obtain ⟨n465, v465, d465, hv465, u465⟩ := u464.aluG hc450 ev_at_744 (off' := 0x748) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv465
  obtain ⟨n466, v466, d466, hv466, u466⟩ := u465.aluG hc450 ev_at_748 (off' := 0x74A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv466
  obtain ⟨n467, v467, d467, hv467, u467⟩ := u466.aluG hc450 ev_at_74a (off' := 0x74E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv467
  obtain ⟨n468, d468, u468⟩ := u467.swG hc450 ev_at_74e (off' := 0x750) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 188) (by decide)) (a := F + 0xBC) (v := v467)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm468, hM468⟩ : ∃ M', memStore32 Mm450 (F + 0xBC) v467 = M' := ⟨_, rfl⟩
  rw [hM468] at u468
  have hc468 : CodeIn Mm468 B ed25519VerifyCode := by rw [← hM468]; exact hc450.store32 (frm_sep' sFC (by decide))
  have fr468 : ∀ x, Sep F 0x128 x 1 → Mm468 x = M0 x := fun x hx => by
    rw [← hM468, memStore32_get_sep (frm_sep' hx (by decide)), fr450 x hx]
  obtain ⟨n469, d469, u469⟩ := u468.lwE hc468 ev_at_750 (off' := 0x752) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 132) (by decide)) (v := v175)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x84) 4 from sep_offsets F (c := 188) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x84) 4 from sep_offsets F (c := 216) (n := 4) (d := 132) (k := 4) (by decide) (by decide) (by decide)), sl84])
  obtain ⟨n470, v470, d470, hv470, u470⟩ := u469.aluImmG hc468 ev_at_752 (off' := 0x754) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv470
  obtain ⟨n471, v471, d471, hv471, u471⟩ := u470.aluG hc468 ev_at_754 (off' := 0x758) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv471
  obtain ⟨n472, v472, d472, hv472, u472⟩ := u471.aluG hc468 ev_at_758 (off' := 0x75A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv472
  obtain ⟨n473, d473, u473⟩ := u472.lwE hc468 ev_at_75a (off' := 0x75C) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 148) (by decide)) (v := v185)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x94) 4 from sep_offsets F (c := 188) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x94) 4 from sep_offsets F (c := 216) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94])
  obtain ⟨n474, v474, d474, hv474, u474⟩ := u473.aluG hc468 ev_at_75c (off' := 0x760) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv474
  obtain ⟨n475, d475, u475⟩ := u474.lwE hc468 ev_at_760 (off' := 0x762) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 180) (by decide)) (v := v15)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xB4) 4 from sep_offsets F (c := 188) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xB4) 4 from sep_offsets F (c := 216) (n := 4) (d := 180) (k := 4) (by decide) (by decide) (by decide)), slB4])
  obtain ⟨n476, v476, d476, hv476, u476⟩ := u475.aluG hc468 ev_at_762 (off' := 0x764) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv476
  obtain ⟨n477, v477, d477, hv477, u477⟩ := u476.luiG hc468 ev_at_764 (off' := 0x768) (by decide)
  obtain ⟨n478, d478, u478⟩ := u477.lwE hc468 ev_at_768 (off' := 0x76A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 108) (by decide)) (v := v310)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x6C) 4 from sep_offsets F (c := 188) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x6C) 4 from sep_offsets F (c := 216) (n := 4) (d := 108) (k := 4) (by decide) (by decide) (by decide)), sl6C])
  obtain ⟨n479, v479, d479, hv479, u479⟩ := u478.aluG hc468 ev_at_76a (off' := 0x76E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv479
  have qo1 : reg n479 ra = v409 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n479 sp = F := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n479 (3 : Fin 32) = G3 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n479 (4 : Fin 32) = G4 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n479 (5 : Fin 32) = v279 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n479 (6 : Fin 32) = v419 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n479 (7 : Fin 32) = v441 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n479 (8 : Fin 32) = v457 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n479 (9 : Fin 32) = v479 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n479 a0 = v467 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n479 a1 = v472 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n479 a2 = v477 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n479 a3 = v474 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n479 a4 = v465 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n479 a5 = v463 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n479 a6 = v442 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n479 a7 = v351 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n479 (18 : Fin 32) = v7 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n479 (19 : Fin 32) = v133 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n479 (20 : Fin 32) = v310 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n479 (21 : Fin 32) = v379 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n479 (22 : Fin 32) = v455 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n479 (23 : Fin 32) = v302 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n479 (24 : Fin 32) = v476 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n479 (25 : Fin 32) = v352 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n479 (26 : Fin 32) = v219 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n479 (27 : Fin 32) = v174 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n479 (28 : Fin 32) = v239 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n479 (29 : Fin 32) = v321 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n479 (30 : Fin 32) = v388 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n479 (31 : Fin 32) = v150 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm468 (F + 0xC) = G21 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xC) 4 from sep_offsets F (c := 188) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xC) 4 from sep_offsets F (c := 216) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm468 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x10) 4 from sep_offsets F (c := 188) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x10) 4 from sep_offsets F (c := 216) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so70 : memLoad32 Mm468 (F + 0x70) = v308 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x70) 4 from sep_offsets F (c := 188) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x70) 4 from sep_offsets F (c := 216) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 Mm468 (F + 0x74) = v320 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x74) 4 from sep_offsets F (c := 188) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x74) 4 from sep_offsets F (c := 216) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 Mm468 (F + 0x78) = v337 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x78) 4 from sep_offsets F (c := 188) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x78) 4 from sep_offsets F (c := 216) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 Mm468 (F + 0x7C) = v312 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x7C) 4 from sep_offsets F (c := 188) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x7C) 4 from sep_offsets F (c := 216) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 Mm468 (F + 0x80) = v254 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x80) 4 from sep_offsets F (c := 188) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x80) 4 from sep_offsets F (c := 216) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so88 : memLoad32 Mm468 (F + 0x88) = v36 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x88) 4 from sep_offsets F (c := 188) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x88) 4 from sep_offsets F (c := 216) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 Mm468 (F + 0x8C) = v236 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x8C) 4 from sep_offsets F (c := 188) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x8C) 4 from sep_offsets F (c := 216) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 Mm468 (F + 0x90) = v151 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x90) 4 from sep_offsets F (c := 188) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x90) 4 from sep_offsets F (c := 216) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so9C : memLoad32 Mm468 (F + 0x9C) = v75 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x9C) 4 from sep_offsets F (c := 188) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x9C) 4 from sep_offsets F (c := 216) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  have soA0 : memLoad32 Mm468 (F + 0xA0) = v87 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xA0) 4 from sep_offsets F (c := 188) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xA0) 4 from sep_offsets F (c := 216) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), slA0]
  have soA4 : memLoad32 Mm468 (F + 0xA4) = v357 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xA4) 4 from sep_offsets F (c := 188) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xA4) 4 from sep_offsets F (c := 216) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), slA4]
  have soAC : memLoad32 Mm468 (F + 0xAC) = v219 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xAC) 4 from sep_offsets F (c := 188) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xAC) 4 from sep_offsets F (c := 216) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), slAC]
  have soB0 : memLoad32 Mm468 (F + 0xB0) = v16 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xB0) 4 from sep_offsets F (c := 188) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xB0) 4 from sep_offsets F (c := 216) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0]
  have soB8 : memLoad32 Mm468 (F + 0xB8) = v136 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xB8) 4 from sep_offsets F (c := 188) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xB8) 4 from sep_offsets F (c := 216) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm468 (F + 0xBC) = v467 := by
    rw [← hM468, memLoad32_store32_same]
  have soC0 : memLoad32 Mm468 (F + 0xC0) = v405 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xC0) 4 from sep_offsets F (c := 188) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xC0) 4 from sep_offsets F (c := 216) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC4 : memLoad32 Mm468 (F + 0xC4) = v199 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xC4) 4 from sep_offsets F (c := 188) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xC4) 4 from sep_offsets F (c := 216) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), slC4]
  have soC8 : memLoad32 Mm468 (F + 0xC8) = v335 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xC8) 4 from sep_offsets F (c := 188) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xC8) 4 from sep_offsets F (c := 216) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soCC : memLoad32 Mm468 (F + 0xCC) = v264 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xCC) 4 from sep_offsets F (c := 188) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xCC) 4 from sep_offsets F (c := 216) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), slCC]
  have soD0 : memLoad32 Mm468 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xD0) 4 from sep_offsets F (c := 188) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xD0) 4 from sep_offsets F (c := 216) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soD8 : memLoad32 Mm468 (F + 0xD8) = v174 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xD8) 4 from sep_offsets F (c := 188) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_same]
  have soE0 : memLoad32 Mm468 (F + 0xE0) = v133 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xE0) 4 from sep_offsets F (c := 188) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xE0) 4 from sep_offsets F (c := 216) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE4 : memLoad32 Mm468 (F + 0xE4) = v7 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xE4) 4 from sep_offsets F (c := 188) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xE4) 4 from sep_offsets F (c := 216) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), slE4]
  have soEC : memLoad32 Mm468 (F + 0xEC) = v341 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xEC) 4 from sep_offsets F (c := 188) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xEC) 4 from sep_offsets F (c := 216) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF0 : memLoad32 Mm468 (F + 0xF0) = v206 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xF0) 4 from sep_offsets F (c := 188) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xF0) 4 from sep_offsets F (c := 216) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), slF0]
  have soF4 : memLoad32 Mm468 (F + 0xF4) = v297 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xF4) 4 from sep_offsets F (c := 188) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xF4) 4 from sep_offsets F (c := 216) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), slF4]
  have soF8 : memLoad32 Mm468 (F + 0xF8) = v284 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xF8) 4 from sep_offsets F (c := 188) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xF8) 4 from sep_offsets F (c := 216) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have soFC : memLoad32 Mm468 (F + 0xFC) = v40 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0xFC) 4 from sep_offsets F (c := 188) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xFC) 4 from sep_offsets F (c := 216) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC]
  have so100 : memLoad32 Mm468 (F + 0x100) = v51 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x100) 4 from sep_offsets F (c := 188) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x100) 4 from sep_offsets F (c := 216) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100]
  have so104 : memLoad32 Mm468 (F + 0x104) = v62 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x104) 4 from sep_offsets F (c := 188) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x104) 4 from sep_offsets F (c := 216) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 Mm468 (F + 0x108) = v203 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x108) 4 from sep_offsets F (c := 188) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x108) 4 from sep_offsets F (c := 216) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 Mm468 (F + 0x10C) = v274 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x10C) 4 from sep_offsets F (c := 188) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x10C) 4 from sep_offsets F (c := 216) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm468 (F + 0x110) = v67 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x110) 4 from sep_offsets F (c := 188) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x110) 4 from sep_offsets F (c := 216) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm468 (F + 0x114) = v111 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x114) 4 from sep_offsets F (c := 188) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x114) 4 from sep_offsets F (c := 216) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm468 (F + 0x118) = v122 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x118) 4 from sep_offsets F (c := 188) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x118) 4 from sep_offsets F (c := 216) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 Mm468 (F + 0x11C) = v231 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x11C) 4 from sep_offsets F (c := 188) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x11C) 4 from sep_offsets F (c := 216) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so120 : memLoad32 Mm468 (F + 0x120) = v116 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x120) 4 from sep_offsets F (c := 188) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x120) 4 from sep_offsets F (c := 216) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm468 (F + 0x124) = v124 := by
    rw [← hM468, memLoad32_store32_sep (show Sep (F + 0xBC) 4 (F + 0x124) 4 from sep_offsets F (c := 188) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM450, memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0x124) 4 from sep_offsets F (c := 216) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n479, Mm468, v440, v441, v442, v443, v444, v445, v446, v449, v451, v452, v453, v454, v455, v456, v457, v458, v459, v460, v461, v462, v463, v464, v465, v466, v467, v470, v471, v472, v474, v476, v477, v479, (.cons d440 (.cons d441 (.cons d442 (.cons d443 (.cons d444 (.cons d445 (.cons d446 (.cons d447 (.cons d448 (.cons d449 (.cons d450 (.cons d451 (.cons d452 (.cons d453 (.cons d454 (.cons d455 (.cons d456 (.cons d457 (.cons d458 (.cons d459 (.cons d460 (.cons d461 (.cons d462 (.cons d463 (.cons d464 (.cons d465 (.cons d466 (.cons d467 (.cons d468 (.cons d469 (.cons d470 (.cons d471 (.cons d472 (.cons d473 (.cons d474 (.cons d475 (.cons d476 (.cons d477 (.cons d478 (.single d479)))))))))))))))))))))))))))))))))))))))), u479.self, hc468, fr468, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so70, so74, so78, so7C, so80, so88, so8C, so90, so9C, soA0, soA4, soAC, soB0, soB8, soBC, soC0, soC4, soC8, soCC, soD0, soD8, soE0, soE4, soEC, soF0, soF4, soF8, soFC, so100, so104, so108, so10C, so110, so114, so118, so11C, so120, so124, hv440, hv441, hv442, hv443, hv444, hv445, hv446, hv449, hv451, hv452, hv453, hv454, hv455, hv456, hv457, hv458, hv459, hv460, hv461, hv462, hv463, hv464, hv465, hv466, hv467, hv470, hv471, hv472, hv474, hv476, hv477, hv479⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g14 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v16 v36 v40 v51 v62 v67 v75 v87 v111 v116 v122 v124 v133 v136 v150 v151 v174 v199 v203 v206 v219 v231 v236 v239 v254 v264 v274 v279 v284 v297 v302 v308 v310 v312 v320 v321 v335 v337 v341 v351 v352 v357 v379 v388 v405 v409 v419 v441 v442 v455 v457 v463 v465 v467 v472 v474 v476 v477 v479 : Word}
    (s : St Mi B n 0x76E (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v409)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v279)
    (q6 : reg n (6 : Fin 32) = v419)
    (q7 : reg n (7 : Fin 32) = v441)
    (q8 : reg n (8 : Fin 32) = v457)
    (q9 : reg n (9 : Fin 32) = v479)
    (q10 : reg n a0 = v467)
    (q11 : reg n a1 = v472)
    (q12 : reg n a2 = v477)
    (q13 : reg n a3 = v474)
    (q14 : reg n a4 = v465)
    (q15 : reg n a5 = v463)
    (q16 : reg n a6 = v442)
    (q17 : reg n a7 = v351)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v133)
    (q20 : reg n (20 : Fin 32) = v310)
    (q21 : reg n (21 : Fin 32) = v379)
    (q22 : reg n (22 : Fin 32) = v455)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v476)
    (q25 : reg n (25 : Fin 32) = v352)
    (q26 : reg n (26 : Fin 32) = v219)
    (q27 : reg n (27 : Fin 32) = v174)
    (q28 : reg n (28 : Fin 32) = v239)
    (q29 : reg n (29 : Fin 32) = v321)
    (q30 : reg n (30 : Fin 32) = v388)
    (q31 : reg n (31 : Fin 32) = v150)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl70 : memLoad32 Mi (F + 0x70) = v308)
    (sl74 : memLoad32 Mi (F + 0x74) = v320)
    (sl78 : memLoad32 Mi (F + 0x78) = v337)
    (sl7C : memLoad32 Mi (F + 0x7C) = v312)
    (sl80 : memLoad32 Mi (F + 0x80) = v254)
    (sl88 : memLoad32 Mi (F + 0x88) = v36)
    (sl8C : memLoad32 Mi (F + 0x8C) = v236)
    (sl90 : memLoad32 Mi (F + 0x90) = v151)
    (sl9C : memLoad32 Mi (F + 0x9C) = v75)
    (slA0 : memLoad32 Mi (F + 0xA0) = v87)
    (slA4 : memLoad32 Mi (F + 0xA4) = v357)
    (slAC : memLoad32 Mi (F + 0xAC) = v219)
    (slB0 : memLoad32 Mi (F + 0xB0) = v16)
    (slB8 : memLoad32 Mi (F + 0xB8) = v136)
    (slBC : memLoad32 Mi (F + 0xBC) = v467)
    (slC0 : memLoad32 Mi (F + 0xC0) = v405)
    (slC4 : memLoad32 Mi (F + 0xC4) = v199)
    (slC8 : memLoad32 Mi (F + 0xC8) = v335)
    (slCC : memLoad32 Mi (F + 0xCC) = v264)
    (slD0 : memLoad32 Mi (F + 0xD0) = memLoad32 M0 (F + 0xD0))
    (slD8 : memLoad32 Mi (F + 0xD8) = v174)
    (slE0 : memLoad32 Mi (F + 0xE0) = v133)
    (slE4 : memLoad32 Mi (F + 0xE4) = v7)
    (slEC : memLoad32 Mi (F + 0xEC) = v341)
    (slF0 : memLoad32 Mi (F + 0xF0) = v206)
    (slF4 : memLoad32 Mi (F + 0xF4) = v297)
    (slF8 : memLoad32 Mi (F + 0xF8) = v284)
    (slFC : memLoad32 Mi (F + 0xFC) = v40)
    (sl100 : memLoad32 Mi (F + 0x100) = v51)
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v480 v481 v483 v484 v485 v486 v488 v489 v490 v491 v492 v493 v494 v495 v497 v498 v499 v500 v502 v503 v504 v505 v506 v507 v508 v509 v510 v511 v512 v514 v515 v516 v518 : Word),
      Steps n n' ∧
      St M' B n' 0x7EE (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v409 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v279 ∧
      reg n' (6 : Fin 32) = v419 ∧
      reg n' (7 : Fin 32) = v518 ∧
      reg n' (8 : Fin 32) = v51 ∧
      reg n' (9 : Fin 32) = v40 ∧
      reg n' a0 = v274 ∧
      reg n' a1 = v514 ∧
      reg n' a2 = v483 ∧
      reg n' a3 = v510 ∧
      reg n' a4 = v511 ∧
      reg n' a5 = v515 ∧
      reg n' a6 = v516 ∧
      reg n' a7 = v509 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v133 ∧
      reg n' (20 : Fin 32) = v310 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v488 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v476 ∧
      reg n' (25 : Fin 32) = v352 ∧
      reg n' (26 : Fin 32) = v480 ∧
      reg n' (27 : Fin 32) = v506 ∧
      reg n' (28 : Fin 32) = v239 ∧
      reg n' (29 : Fin 32) = v493 ∧
      reg n' (30 : Fin 32) = v388 ∧
      reg n' (31 : Fin 32) = v150 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x70) = v308 ∧
      memLoad32 M' (F + 0x74) = v320 ∧
      memLoad32 M' (F + 0x78) = v337 ∧
      memLoad32 M' (F + 0x7C) = v312 ∧
      memLoad32 M' (F + 0x80) = v254 ∧
      memLoad32 M' (F + 0x88) = v36 ∧
      memLoad32 M' (F + 0x8C) = v236 ∧
      memLoad32 M' (F + 0x90) = v151 ∧
      memLoad32 M' (F + 0x94) = v481 ∧
      memLoad32 M' (F + 0x9C) = v75 ∧
      memLoad32 M' (F + 0xA0) = v87 ∧
      memLoad32 M' (F + 0xA4) = v357 ∧
      memLoad32 M' (F + 0xA8) = v279 ∧
      memLoad32 M' (F + 0xAC) = v219 ∧
      memLoad32 M' (F + 0xB0) = v16 ∧
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
      memLoad32 M' (F + 0x104) = v62 ∧
      memLoad32 M' (F + 0x108) = v203 ∧
      memLoad32 M' (F + 0x10C) = v274 ∧
      memLoad32 M' (F + 0x110) = v67 ∧
      memLoad32 M' (F + 0x114) = v111 ∧
      memLoad32 M' (F + 0x118) = v122 ∧
      memLoad32 M' (F + 0x11C) = v231 ∧
      memLoad32 M' (F + 0x120) = v116 ∧
      memLoad32 M' (F + 0x124) = v124 ∧
      aluEval .add v477 0x302 = v480 ∧
      aluEval .add v474 v321 = v481 ∧
      aluEval .mul v388 v480 = v483 ∧
      aluEval .mulhu v388 v480 = v484 ∧
      aluEval .and v467 v7 = v485 ∧
      aluEval .sltu v481 v321 = v486 ∧
      aluEval .mulhu v485 v150 = v488 ∧
      aluEval .srl v441 0x1D = v489 ∧
      aluEval .mulhu v476 v409 = v490 ∧
      aluEval .mul v476 v409 = v491 ∧
      aluEval .mul v485 v150 = v492 ∧
      aluEval .add v486 v479 = v493 ∧
      aluEval .add v472 v489 = v494 ∧
      aluEval .sltu v465 v463 = v495 ∧
      aluEval .sltu v483 v40 = v497 ∧
      aluEval .add v494 v495 = v498 ∧
      aluEval .sub v484 v497 = v499 ∧
      aluEval .add v498 v488 = v500 ∧
      aluEval .sub v499 v51 = v502 ∧
      aluEval .sub v483 v40 = v503 ∧
      aluEval .add v502 v490 = v504 ∧
      aluEval .add v465 v492 = v505 ∧
      aluEval .add v491 v503 = v506 ∧
      aluEval .sltu v505 v492 = v507 ∧
      aluEval .sltu v506 v503 = v508 ∧
      aluEval .add v500 v507 = v509 ∧
      aluEval .add v508 v504 = v510 ∧
      aluEval .srl v505 0x1D = v511 ∧
      aluEval .add 0 0x14D = v512 ∧
      aluEval .mul v279 v512 = v514 ∧
      aluEval .mulhu v279 v512 = v515 ∧
      aluEval .mul v352 v302 = v516 ∧
      aluEval .mul v419 v239 = v518 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n480, v480, d480, hv480, u480⟩ := s.aluImmG hc ev_at_76e (off' := 0x772) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv480
  obtain ⟨n481, v481, d481, hv481, u481⟩ := u480.aluG hc ev_at_772 (off' := 0x774) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv481
  obtain ⟨n482, d482, u482⟩ := u481.swG hc ev_at_774 (off' := 0x776) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 148) (by decide)) (a := F + 0x94) (v := v481)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm482, hM482⟩ : ∃ M', memStore32 Mi (F + 0x94) v481 = M' := ⟨_, rfl⟩
  rw [hM482] at u482
  have hc482 : CodeIn Mm482 B ed25519VerifyCode := by rw [← hM482]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr482 : ∀ x, Sep F 0x128 x 1 → Mm482 x = M0 x := fun x hx => by
    rw [← hM482, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n483, v483, d483, hv483, u483⟩ := u482.aluG hc482 ev_at_776 (off' := 0x77A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv483
  obtain ⟨n484, v484, d484, hv484, u484⟩ := u483.aluG hc482 ev_at_77a (off' := 0x77E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv484
  obtain ⟨n485, v485, d485, hv485, u485⟩ := u484.aluG hc482 ev_at_77e (off' := 0x782) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv485
  obtain ⟨n486, v486, d486, hv486, u486⟩ := u485.aluG hc482 ev_at_782 (off' := 0x786) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv486
  obtain ⟨n487, d487, u487⟩ := u486.swG hc482 ev_at_786 (off' := 0x788) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 220) (by decide)) (a := F + 0xDC) (v := v150)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm487, hM487⟩ : ∃ M', memStore32 Mm482 (F + 0xDC) v150 = M' := ⟨_, rfl⟩
  rw [hM487] at u487
  have hc487 : CodeIn Mm487 B ed25519VerifyCode := by rw [← hM487]; exact hc482.store32 (frm_sep' sFC (by decide))
  have fr487 : ∀ x, Sep F 0x128 x 1 → Mm487 x = M0 x := fun x hx => by
    rw [← hM487, memStore32_get_sep (frm_sep' hx (by decide)), fr482 x hx]
  obtain ⟨n488, v488, d488, hv488, u488⟩ := u487.aluG hc487 ev_at_788 (off' := 0x78C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv488
  obtain ⟨n489, v489, d489, hv489, u489⟩ := u488.aluImmG hc487 ev_at_78c (off' := 0x790) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv489
  obtain ⟨n490, v490, d490, hv490, u490⟩ := u489.aluG hc487 ev_at_790 (off' := 0x794) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv490
  obtain ⟨n491, v491, d491, hv491, u491⟩ := u490.aluG hc487 ev_at_794 (off' := 0x798) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv491
  obtain ⟨n492, v492, d492, hv492, u492⟩ := u491.aluG hc487 ev_at_798 (off' := 0x79C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv492
  obtain ⟨n493, v493, d493, hv493, u493⟩ := u492.aluG hc487 ev_at_79c (off' := 0x79E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv493
  obtain ⟨n494, v494, d494, hv494, u494⟩ := u493.aluG hc487 ev_at_79e (off' := 0x7A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv494
  obtain ⟨n495, v495, d495, hv495, u495⟩ := u494.aluG hc487 ev_at_7a0 (off' := 0x7A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv495
  obtain ⟨n496, d496, u496⟩ := u495.lwE hc487 ev_at_7a4 (off' := 0x7A6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 252) (by decide)) (v := v40)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xFC) 4 from sep_offsets F (c := 220) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xFC) 4 from sep_offsets F (c := 148) (n := 4) (d := 252) (k := 4) (by decide) (by decide) (by decide)), slFC])
  obtain ⟨n497, v497, d497, hv497, u497⟩ := u496.aluG hc487 ev_at_7a6 (off' := 0x7AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv497
  obtain ⟨n498, v498, d498, hv498, u498⟩ := u497.aluG hc487 ev_at_7aa (off' := 0x7AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv498
  obtain ⟨n499, v499, d499, hv499, u499⟩ := u498.aluG hc487 ev_at_7ac (off' := 0x7B0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv499
  obtain ⟨n500, v500, d500, hv500, u500⟩ := u499.aluG hc487 ev_at_7b0 (off' := 0x7B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv500
  obtain ⟨n501, d501, u501⟩ := u500.lwE hc487 ev_at_7b2 (off' := 0x7B6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 256) (by decide)) (v := v51)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x100) 4 from sep_offsets F (c := 220) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x100) 4 from sep_offsets F (c := 148) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), sl100])
  obtain ⟨n502, v502, d502, hv502, u502⟩ := u501.aluG hc487 ev_at_7b6 (off' := 0x7B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv502
  obtain ⟨n503, v503, d503, hv503, u503⟩ := u502.aluG hc487 ev_at_7b8 (off' := 0x7BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv503
  obtain ⟨n504, v504, d504, hv504, u504⟩ := u503.aluG hc487 ev_at_7bc (off' := 0x7BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv504
  obtain ⟨n505, v505, d505, hv505, u505⟩ := u504.aluG hc487 ev_at_7be (off' := 0x7C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv505
  obtain ⟨n506, v506, d506, hv506, u506⟩ := u505.aluG hc487 ev_at_7c0 (off' := 0x7C2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv506
  obtain ⟨n507, v507, d507, hv507, u507⟩ := u506.aluG hc487 ev_at_7c2 (off' := 0x7C6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv507
  obtain ⟨n508, v508, d508, hv508, u508⟩ := u507.aluG hc487 ev_at_7c6 (off' := 0x7CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv508
  obtain ⟨n509, v509, d509, hv509, u509⟩ := u508.aluG hc487 ev_at_7ca (off' := 0x7CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv509
  obtain ⟨n510, v510, d510, hv510, u510⟩ := u509.aluG hc487 ev_at_7ce (off' := 0x7D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv510
  obtain ⟨n511, v511, d511, hv511, u511⟩ := u510.aluImmG hc487 ev_at_7d0 (off' := 0x7D2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv511
  obtain ⟨n512, v512, d512, hv512, u512⟩ := u511.aluImmG hc487 ev_at_7d2 (off' := 0x7D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv512
  obtain ⟨n513, d513, u513⟩ := u512.swG hc487 ev_at_7d6 (off' := 0x7D8) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 168) (by decide)) (a := F + 0xA8) (v := v279)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm513, hM513⟩ : ∃ M', memStore32 Mm487 (F + 0xA8) v279 = M' := ⟨_, rfl⟩
  rw [hM513] at u513
  have hc513 : CodeIn Mm513 B ed25519VerifyCode := by rw [← hM513]; exact hc487.store32 (frm_sep' sFC (by decide))
  have fr513 : ∀ x, Sep F 0x128 x 1 → Mm513 x = M0 x := fun x hx => by
    rw [← hM513, memStore32_get_sep (frm_sep' hx (by decide)), fr487 x hx]
  obtain ⟨n514, v514, d514, hv514, u514⟩ := u513.aluG hc513 ev_at_7d8 (off' := 0x7DC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv514
  obtain ⟨n515, v515, d515, hv515, u515⟩ := u514.aluG hc513 ev_at_7dc (off' := 0x7E0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv515
  obtain ⟨n516, v516, d516, hv516, u516⟩ := u515.aluG hc513 ev_at_7e0 (off' := 0x7E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv516
  obtain ⟨n517, d517, u517⟩ := u516.swG hc513 ev_at_7e4 (off' := 0x7E6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 212) (by decide)) (a := F + 0xD4) (v := v239)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm517, hM517⟩ : ∃ M', memStore32 Mm513 (F + 0xD4) v239 = M' := ⟨_, rfl⟩
  rw [hM517] at u517
  have hc517 : CodeIn Mm517 B ed25519VerifyCode := by rw [← hM517]; exact hc513.store32 (frm_sep' sFC (by decide))
  have fr517 : ∀ x, Sep F 0x128 x 1 → Mm517 x = M0 x := fun x hx => by
    rw [← hM517, memStore32_get_sep (frm_sep' hx (by decide)), fr513 x hx]
  obtain ⟨n518, v518, d518, hv518, u518⟩ := u517.aluG hc517 ev_at_7e6 (off' := 0x7EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv518
  obtain ⟨n519, d519, u519⟩ := u518.lwE hc517 ev_at_7ea (off' := 0x7EE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 268) (by decide)) (v := v274)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x10C) 4 from sep_offsets F (c := 212) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x10C) 4 from sep_offsets F (c := 168) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x10C) 4 from sep_offsets F (c := 220) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x10C) 4 from sep_offsets F (c := 148) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C])
  have qo1 : reg n519 ra = v409 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n519 sp = F := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n519 (3 : Fin 32) = G3 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n519 (4 : Fin 32) = G4 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n519 (5 : Fin 32) = v279 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n519 (6 : Fin 32) = v419 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n519 (7 : Fin 32) = v518 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n519 (8 : Fin 32) = v51 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n519 (9 : Fin 32) = v40 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n519 a0 = v274 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n519 a1 = v514 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n519 a2 = v483 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n519 a3 = v510 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n519 a4 = v511 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n519 a5 = v515 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n519 a6 = v516 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n519 a7 = v509 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n519 (18 : Fin 32) = v7 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n519 (19 : Fin 32) = v133 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n519 (20 : Fin 32) = v310 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n519 (21 : Fin 32) = v485 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n519 (22 : Fin 32) = v488 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n519 (23 : Fin 32) = v302 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n519 (24 : Fin 32) = v476 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n519 (25 : Fin 32) = v352 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n519 (26 : Fin 32) = v480 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n519 (27 : Fin 32) = v506 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n519 (28 : Fin 32) = v239 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n519 (29 : Fin 32) = v493 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n519 (30 : Fin 32) = v388 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n519 (31 : Fin 32) = v150 := by rw [u519.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm517 (F + 0xC) = G21 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xC) 4 from sep_offsets F (c := 212) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xC) 4 from sep_offsets F (c := 168) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xC) 4 from sep_offsets F (c := 220) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xC) 4 from sep_offsets F (c := 148) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm517 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x10) 4 from sep_offsets F (c := 212) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x10) 4 from sep_offsets F (c := 168) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x10) 4 from sep_offsets F (c := 220) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x10) 4 from sep_offsets F (c := 148) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so70 : memLoad32 Mm517 (F + 0x70) = v308 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x70) 4 from sep_offsets F (c := 212) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x70) 4 from sep_offsets F (c := 168) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x70) 4 from sep_offsets F (c := 220) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x70) 4 from sep_offsets F (c := 148) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so74 : memLoad32 Mm517 (F + 0x74) = v320 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x74) 4 from sep_offsets F (c := 212) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x74) 4 from sep_offsets F (c := 168) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x74) 4 from sep_offsets F (c := 220) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x74) 4 from sep_offsets F (c := 148) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74]
  have so78 : memLoad32 Mm517 (F + 0x78) = v337 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x78) 4 from sep_offsets F (c := 212) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x78) 4 from sep_offsets F (c := 168) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x78) 4 from sep_offsets F (c := 220) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x78) 4 from sep_offsets F (c := 148) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78]
  have so7C : memLoad32 Mm517 (F + 0x7C) = v312 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x7C) 4 from sep_offsets F (c := 212) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x7C) 4 from sep_offsets F (c := 168) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x7C) 4 from sep_offsets F (c := 220) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x7C) 4 from sep_offsets F (c := 148) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so80 : memLoad32 Mm517 (F + 0x80) = v254 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x80) 4 from sep_offsets F (c := 212) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x80) 4 from sep_offsets F (c := 168) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x80) 4 from sep_offsets F (c := 220) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x80) 4 from sep_offsets F (c := 148) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80]
  have so88 : memLoad32 Mm517 (F + 0x88) = v36 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x88) 4 from sep_offsets F (c := 212) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x88) 4 from sep_offsets F (c := 168) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x88) 4 from sep_offsets F (c := 220) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x88) 4 from sep_offsets F (c := 148) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so8C : memLoad32 Mm517 (F + 0x8C) = v236 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x8C) 4 from sep_offsets F (c := 212) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x8C) 4 from sep_offsets F (c := 168) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x8C) 4 from sep_offsets F (c := 220) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x8C) 4 from sep_offsets F (c := 148) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C]
  have so90 : memLoad32 Mm517 (F + 0x90) = v151 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x90) 4 from sep_offsets F (c := 212) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x90) 4 from sep_offsets F (c := 168) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x90) 4 from sep_offsets F (c := 220) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x90) 4 from sep_offsets F (c := 148) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 Mm517 (F + 0x94) = v481 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x94) 4 from sep_offsets F (c := 212) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x94) 4 from sep_offsets F (c := 168) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x94) 4 from sep_offsets F (c := 220) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_same]
  have so9C : memLoad32 Mm517 (F + 0x9C) = v75 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x9C) 4 from sep_offsets F (c := 212) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x9C) 4 from sep_offsets F (c := 168) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x9C) 4 from sep_offsets F (c := 220) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x9C) 4 from sep_offsets F (c := 148) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  have soA0 : memLoad32 Mm517 (F + 0xA0) = v87 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xA0) 4 from sep_offsets F (c := 212) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xA0) 4 from sep_offsets F (c := 168) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xA0) 4 from sep_offsets F (c := 220) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xA0) 4 from sep_offsets F (c := 148) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), slA0]
  have soA4 : memLoad32 Mm517 (F + 0xA4) = v357 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xA4) 4 from sep_offsets F (c := 212) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xA4) 4 from sep_offsets F (c := 168) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xA4) 4 from sep_offsets F (c := 220) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xA4) 4 from sep_offsets F (c := 148) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), slA4]
  have soA8 : memLoad32 Mm517 (F + 0xA8) = v279 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xA8) 4 from sep_offsets F (c := 212) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_same]
  have soAC : memLoad32 Mm517 (F + 0xAC) = v219 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xAC) 4 from sep_offsets F (c := 212) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xAC) 4 from sep_offsets F (c := 168) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xAC) 4 from sep_offsets F (c := 220) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xAC) 4 from sep_offsets F (c := 148) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), slAC]
  have soB0 : memLoad32 Mm517 (F + 0xB0) = v16 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xB0) 4 from sep_offsets F (c := 212) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xB0) 4 from sep_offsets F (c := 168) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xB0) 4 from sep_offsets F (c := 220) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xB0) 4 from sep_offsets F (c := 148) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0]
  have soB8 : memLoad32 Mm517 (F + 0xB8) = v136 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xB8) 4 from sep_offsets F (c := 212) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xB8) 4 from sep_offsets F (c := 168) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xB8) 4 from sep_offsets F (c := 220) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xB8) 4 from sep_offsets F (c := 148) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm517 (F + 0xBC) = v467 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xBC) 4 from sep_offsets F (c := 212) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xBC) 4 from sep_offsets F (c := 168) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xBC) 4 from sep_offsets F (c := 220) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xBC) 4 from sep_offsets F (c := 148) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm517 (F + 0xC0) = v405 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xC0) 4 from sep_offsets F (c := 212) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xC0) 4 from sep_offsets F (c := 168) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xC0) 4 from sep_offsets F (c := 220) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xC0) 4 from sep_offsets F (c := 148) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC4 : memLoad32 Mm517 (F + 0xC4) = v199 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xC4) 4 from sep_offsets F (c := 212) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xC4) 4 from sep_offsets F (c := 168) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xC4) 4 from sep_offsets F (c := 220) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xC4) 4 from sep_offsets F (c := 148) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), slC4]
  have soC8 : memLoad32 Mm517 (F + 0xC8) = v335 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xC8) 4 from sep_offsets F (c := 212) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xC8) 4 from sep_offsets F (c := 168) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xC8) 4 from sep_offsets F (c := 220) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xC8) 4 from sep_offsets F (c := 148) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soCC : memLoad32 Mm517 (F + 0xCC) = v264 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xCC) 4 from sep_offsets F (c := 212) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xCC) 4 from sep_offsets F (c := 168) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xCC) 4 from sep_offsets F (c := 220) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xCC) 4 from sep_offsets F (c := 148) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), slCC]
  have soD0 : memLoad32 Mm517 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xD0) 4 from sep_offsets F (c := 212) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xD0) 4 from sep_offsets F (c := 168) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xD0) 4 from sep_offsets F (c := 220) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xD0) 4 from sep_offsets F (c := 148) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soD4 : memLoad32 Mm517 (F + 0xD4) = v239 := by
    rw [← hM517, memLoad32_store32_same]
  have soD8 : memLoad32 Mm517 (F + 0xD8) = v174 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xD8) 4 from sep_offsets F (c := 212) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xD8) 4 from sep_offsets F (c := 168) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xD8) 4 from sep_offsets F (c := 220) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xD8) 4 from sep_offsets F (c := 148) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), slD8]
  have soDC : memLoad32 Mm517 (F + 0xDC) = v150 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xDC) 4 from sep_offsets F (c := 212) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xDC) 4 from sep_offsets F (c := 168) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_same]
  have soE0 : memLoad32 Mm517 (F + 0xE0) = v133 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xE0) 4 from sep_offsets F (c := 212) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xE0) 4 from sep_offsets F (c := 168) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xE0) 4 from sep_offsets F (c := 220) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xE0) 4 from sep_offsets F (c := 148) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE4 : memLoad32 Mm517 (F + 0xE4) = v7 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xE4) 4 from sep_offsets F (c := 212) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xE4) 4 from sep_offsets F (c := 168) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xE4) 4 from sep_offsets F (c := 220) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xE4) 4 from sep_offsets F (c := 148) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), slE4]
  have soEC : memLoad32 Mm517 (F + 0xEC) = v341 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xEC) 4 from sep_offsets F (c := 212) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xEC) 4 from sep_offsets F (c := 168) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xEC) 4 from sep_offsets F (c := 220) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xEC) 4 from sep_offsets F (c := 148) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF0 : memLoad32 Mm517 (F + 0xF0) = v206 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xF0) 4 from sep_offsets F (c := 212) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xF0) 4 from sep_offsets F (c := 168) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xF0) 4 from sep_offsets F (c := 220) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xF0) 4 from sep_offsets F (c := 148) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), slF0]
  have soF4 : memLoad32 Mm517 (F + 0xF4) = v297 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xF4) 4 from sep_offsets F (c := 212) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xF4) 4 from sep_offsets F (c := 168) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xF4) 4 from sep_offsets F (c := 220) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xF4) 4 from sep_offsets F (c := 148) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), slF4]
  have soF8 : memLoad32 Mm517 (F + 0xF8) = v284 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xF8) 4 from sep_offsets F (c := 212) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0xF8) 4 from sep_offsets F (c := 168) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0xF8) 4 from sep_offsets F (c := 220) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0xF8) 4 from sep_offsets F (c := 148) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have so104 : memLoad32 Mm517 (F + 0x104) = v62 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x104) 4 from sep_offsets F (c := 212) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x104) 4 from sep_offsets F (c := 168) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x104) 4 from sep_offsets F (c := 220) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x104) 4 from sep_offsets F (c := 148) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 Mm517 (F + 0x108) = v203 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x108) 4 from sep_offsets F (c := 212) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x108) 4 from sep_offsets F (c := 168) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x108) 4 from sep_offsets F (c := 220) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x108) 4 from sep_offsets F (c := 148) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 Mm517 (F + 0x10C) = v274 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x10C) 4 from sep_offsets F (c := 212) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x10C) 4 from sep_offsets F (c := 168) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x10C) 4 from sep_offsets F (c := 220) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x10C) 4 from sep_offsets F (c := 148) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm517 (F + 0x110) = v67 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x110) 4 from sep_offsets F (c := 212) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x110) 4 from sep_offsets F (c := 168) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x110) 4 from sep_offsets F (c := 220) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x110) 4 from sep_offsets F (c := 148) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm517 (F + 0x114) = v111 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x114) 4 from sep_offsets F (c := 212) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x114) 4 from sep_offsets F (c := 168) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x114) 4 from sep_offsets F (c := 220) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x114) 4 from sep_offsets F (c := 148) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm517 (F + 0x118) = v122 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x118) 4 from sep_offsets F (c := 212) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x118) 4 from sep_offsets F (c := 168) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x118) 4 from sep_offsets F (c := 220) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x118) 4 from sep_offsets F (c := 148) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 Mm517 (F + 0x11C) = v231 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x11C) 4 from sep_offsets F (c := 212) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x11C) 4 from sep_offsets F (c := 168) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x11C) 4 from sep_offsets F (c := 220) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x11C) 4 from sep_offsets F (c := 148) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so120 : memLoad32 Mm517 (F + 0x120) = v116 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x120) 4 from sep_offsets F (c := 212) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x120) 4 from sep_offsets F (c := 168) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x120) 4 from sep_offsets F (c := 220) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x120) 4 from sep_offsets F (c := 148) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm517 (F + 0x124) = v124 := by
    rw [← hM517, memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0x124) 4 from sep_offsets F (c := 212) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM513, memLoad32_store32_sep (show Sep (F + 0xA8) 4 (F + 0x124) 4 from sep_offsets F (c := 168) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM487, memLoad32_store32_sep (show Sep (F + 0xDC) 4 (F + 0x124) 4 from sep_offsets F (c := 220) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM482, memLoad32_store32_sep (show Sep (F + 0x94) 4 (F + 0x124) 4 from sep_offsets F (c := 148) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n519, Mm517, v480, v481, v483, v484, v485, v486, v488, v489, v490, v491, v492, v493, v494, v495, v497, v498, v499, v500, v502, v503, v504, v505, v506, v507, v508, v509, v510, v511, v512, v514, v515, v516, v518, (.cons d480 (.cons d481 (.cons d482 (.cons d483 (.cons d484 (.cons d485 (.cons d486 (.cons d487 (.cons d488 (.cons d489 (.cons d490 (.cons d491 (.cons d492 (.cons d493 (.cons d494 (.cons d495 (.cons d496 (.cons d497 (.cons d498 (.cons d499 (.cons d500 (.cons d501 (.cons d502 (.cons d503 (.cons d504 (.cons d505 (.cons d506 (.cons d507 (.cons d508 (.cons d509 (.cons d510 (.cons d511 (.cons d512 (.cons d513 (.cons d514 (.cons d515 (.cons d516 (.cons d517 (.cons d518 (.single d519)))))))))))))))))))))))))))))))))))))))), u519.self, hc517, fr517, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so70, so74, so78, so7C, so80, so88, so8C, so90, so94, so9C, soA0, soA4, soA8, soAC, soB0, soB8, soBC, soC0, soC4, soC8, soCC, soD0, soD4, soD8, soDC, soE0, soE4, soEC, soF0, soF4, soF8, so104, so108, so10C, so110, so114, so118, so11C, so120, so124, hv480, hv481, hv483, hv484, hv485, hv486, hv488, hv489, hv490, hv491, hv492, hv493, hv494, hv495, hv497, hv498, hv499, hv500, hv502, hv503, hv504, hv505, hv506, hv507, hv508, hv509, hv510, hv511, hv512, hv514, hv515, hv516, hv518⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem evr_g15 {M0 Mi : Word → BitVec 8} {B F G21 G3 G4 : Word} {n : Machine} {v7 v16 v36 v40 v51 v62 v67 v75 v87 v111 v116 v122 v124 v133 v136 v150 v151 v174 v199 v203 v206 v219 v231 v236 v239 v254 v264 v274 v279 v284 v297 v302 v308 v310 v312 v320 v335 v337 v341 v352 v357 v388 v405 v409 v419 v467 v476 v480 v481 v483 v485 v488 v493 v506 v509 v510 v511 v514 v515 v516 v518 : Word}
    (s : St Mi B n 0x7EE (reg n)) (hc : CodeIn Mi B ed25519VerifyCode)
    (fr : ∀ x, Sep F 0x128 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (sFC : Sep F 0x128 B ed25519VerifyCode.length)
    (q1 : reg n ra = v409)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v279)
    (q6 : reg n (6 : Fin 32) = v419)
    (q7 : reg n (7 : Fin 32) = v518)
    (q8 : reg n (8 : Fin 32) = v51)
    (q9 : reg n (9 : Fin 32) = v40)
    (q10 : reg n a0 = v274)
    (q11 : reg n a1 = v514)
    (q12 : reg n a2 = v483)
    (q13 : reg n a3 = v510)
    (q14 : reg n a4 = v511)
    (q15 : reg n a5 = v515)
    (q16 : reg n a6 = v516)
    (q17 : reg n a7 = v509)
    (q18 : reg n (18 : Fin 32) = v7)
    (q19 : reg n (19 : Fin 32) = v133)
    (q20 : reg n (20 : Fin 32) = v310)
    (q21 : reg n (21 : Fin 32) = v485)
    (q22 : reg n (22 : Fin 32) = v488)
    (q23 : reg n (23 : Fin 32) = v302)
    (q24 : reg n (24 : Fin 32) = v476)
    (q25 : reg n (25 : Fin 32) = v352)
    (q26 : reg n (26 : Fin 32) = v480)
    (q27 : reg n (27 : Fin 32) = v506)
    (q28 : reg n (28 : Fin 32) = v239)
    (q29 : reg n (29 : Fin 32) = v493)
    (q30 : reg n (30 : Fin 32) = v388)
    (q31 : reg n (31 : Fin 32) = v150)
    (slC : memLoad32 Mi (F + 0xC) = G21)
    (sl10 : memLoad32 Mi (F + 0x10) = memLoad32 M0 (F + 0x10))
    (sl70 : memLoad32 Mi (F + 0x70) = v308)
    (sl74 : memLoad32 Mi (F + 0x74) = v320)
    (sl78 : memLoad32 Mi (F + 0x78) = v337)
    (sl7C : memLoad32 Mi (F + 0x7C) = v312)
    (sl80 : memLoad32 Mi (F + 0x80) = v254)
    (sl88 : memLoad32 Mi (F + 0x88) = v36)
    (sl8C : memLoad32 Mi (F + 0x8C) = v236)
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
    (sl104 : memLoad32 Mi (F + 0x104) = v62)
    (sl108 : memLoad32 Mi (F + 0x108) = v203)
    (sl10C : memLoad32 Mi (F + 0x10C) = v274)
    (sl110 : memLoad32 Mi (F + 0x110) = v67)
    (sl114 : memLoad32 Mi (F + 0x114) = v111)
    (sl118 : memLoad32 Mi (F + 0x118) = v122)
    (sl11C : memLoad32 Mi (F + 0x11C) = v231)
    (sl120 : memLoad32 Mi (F + 0x120) = v116)
    (sl124 : memLoad32 Mi (F + 0x124) = v124)
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v520 v521 v523 v525 v526 v527 v528 v529 v530 v531 v532 v533 v534 v535 v536 v537 v538 v539 v540 v542 v543 v545 v547 v548 v549 v550 v552 v553 v555 v556 v557 v559 : Word),
      Steps n n' ∧
      St M' B n' 0x862 (reg n') ∧
      CodeIn M' B ed25519VerifyCode ∧
      (∀ x, Sep F 0x128 x 1 → M' x = M0 x) ∧
      reg n' ra = v409 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v279 ∧
      reg n' (6 : Fin 32) = v419 ∧
      reg n' (7 : Fin 32) = v533 ∧
      reg n' (8 : Fin 32) = v538 ∧
      reg n' (9 : Fin 32) = v536 ∧
      reg n' a0 = v553 ∧
      reg n' a1 = v555 ∧
      reg n' a2 = v559 ∧
      reg n' a3 = v320 ∧
      reg n' a4 = v527 ∧
      reg n' a5 = v534 ∧
      reg n' a6 = v556 ∧
      reg n' a7 = v509 ∧
      reg n' (18 : Fin 32) = v7 ∧
      reg n' (19 : Fin 32) = v133 ∧
      reg n' (20 : Fin 32) = v310 ∧
      reg n' (21 : Fin 32) = v485 ∧
      reg n' (22 : Fin 32) = v557 ∧
      reg n' (23 : Fin 32) = v302 ∧
      reg n' (24 : Fin 32) = v476 ∧
      reg n' (25 : Fin 32) = v352 ∧
      reg n' (26 : Fin 32) = v480 ∧
      reg n' (27 : Fin 32) = v530 ∧
      reg n' (28 : Fin 32) = v254 ∧
      reg n' (29 : Fin 32) = v545 ∧
      reg n' (30 : Fin 32) = v388 ∧
      reg n' (31 : Fin 32) = v537 ∧
      memLoad32 M' (F + 0xC) = G21 ∧
      memLoad32 M' (F + 0x10) = memLoad32 M0 (F + 0x10) ∧
      memLoad32 M' (F + 0x70) = v308 ∧
      memLoad32 M' (F + 0x78) = v545 ∧
      memLoad32 M' (F + 0x7C) = v312 ∧
      memLoad32 M' (F + 0x88) = v36 ∧
      memLoad32 M' (F + 0x90) = v151 ∧
      memLoad32 M' (F + 0x94) = v481 ∧
      memLoad32 M' (F + 0x9C) = v75 ∧
      memLoad32 M' (F + 0xA0) = v87 ∧
      memLoad32 M' (F + 0xA4) = v357 ∧
      memLoad32 M' (F + 0xA8) = v279 ∧
      memLoad32 M' (F + 0xAC) = v219 ∧
      memLoad32 M' (F + 0xB0) = v16 ∧
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
      aluEval .add v274 v506 = v520 ∧
      aluEval .sltu v520 v506 = v521 ∧
      aluEval .mul v485 v174 = v523 ∧
      aluEval .add v521 v231 = v525 ∧
      aluEval .sll v509 0x3 = v526 ∧
      aluEval .or v511 v526 = v527 ∧
      aluEval .add v510 v525 = v528 ∧
      aluEval .add v514 v520 = v529 ∧
      aluEval .mulhu v352 v302 = v530 ∧
      aluEval .add v528 v515 = v531 ∧
      aluEval .add v516 v529 = v532 ∧
      aluEval .add v518 v532 = v533 ∧
      aluEval .mulhu v419 v239 = v534 ∧
      aluEval .sltu v529 v520 = v535 ∧
      aluEval .add v533 v523 = v536 ∧
      aluEval .add v536 v527 = v537 ∧
      aluEval .mulhu v485 v174 = v538 ∧
      aluEval .add v535 v531 = v539 ∧
      aluEval .mul v537 v133 = v540 ∧
      aluEval .add v539 v530 = v542 ∧
      aluEval .sltu v532 v529 = v543 ∧
      aluEval .add v493 v337 = v545 ∧
      aluEval .add v542 v543 = v547 ∧
      aluEval .add v547 v534 = v548 ∧
      aluEval .sltu v533 v532 = v549 ∧
      aluEval .add v548 v549 = v550 ∧
      aluEval .sll v236 0x14 = v552 ∧
      aluEval .add v550 v538 = v553 ∧
      aluEval .sub v552 v254 = v555 ∧
      aluEval .mulhu v254 v310 = v556 ∧
      aluEval .and v540 v7 = v557 ∧
      aluEval .add v320 v555 = v559 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n520, v520, d520, hv520, u520⟩ := s.aluG hc ev_at_7ee (off' := 0x7F0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv520
  obtain ⟨n521, v521, d521, hv521, u521⟩ := u520.aluG hc ev_at_7f0 (off' := 0x7F4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv521
  obtain ⟨n522, d522, u522⟩ := u521.lwE hc ev_at_7f4 (off' := 0x7F6) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 216) (by decide)) (v := v174)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [slD8])
  obtain ⟨n523, v523, d523, hv523, u523⟩ := u522.aluG hc ev_at_7f6 (off' := 0x7FA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv523
  obtain ⟨n524, d524, u524⟩ := u523.lwE hc ev_at_7fa (off' := 0x7FE) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 284) (by decide)) (v := v231)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [sl11C])
  obtain ⟨n525, v525, d525, hv525, u525⟩ := u524.aluG hc ev_at_7fe (off' := 0x800) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv525
  obtain ⟨n526, v526, d526, hv526, u526⟩ := u525.aluImmG hc ev_at_800 (off' := 0x804) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv526
  obtain ⟨n527, v527, d527, hv527, u527⟩ := u526.aluG hc ev_at_804 (off' := 0x806) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv527
  obtain ⟨n528, v528, d528, hv528, u528⟩ := u527.aluG hc ev_at_806 (off' := 0x808) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv528
  obtain ⟨n529, v529, d529, hv529, u529⟩ := u528.aluG hc ev_at_808 (off' := 0x80A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv529
  obtain ⟨n530, v530, d530, hv530, u530⟩ := u529.aluG hc ev_at_80a (off' := 0x80E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv530
  obtain ⟨n531, v531, d531, hv531, u531⟩ := u530.aluG hc ev_at_80e (off' := 0x810) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv531
  obtain ⟨n532, v532, d532, hv532, u532⟩ := u531.aluG hc ev_at_810 (off' := 0x812) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv532
  obtain ⟨n533, v533, d533, hv533, u533⟩ := u532.aluG hc ev_at_812 (off' := 0x814) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv533
  obtain ⟨n534, v534, d534, hv534, u534⟩ := u533.aluG hc ev_at_814 (off' := 0x818) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv534
  obtain ⟨n535, v535, d535, hv535, u535⟩ := u534.aluG hc ev_at_818 (off' := 0x81C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv535
  obtain ⟨n536, v536, d536, hv536, u536⟩ := u535.aluG hc ev_at_81c (off' := 0x820) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv536
  obtain ⟨n537, v537, d537, hv537, u537⟩ := u536.aluG hc ev_at_820 (off' := 0x824) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv537
  obtain ⟨n538, v538, d538, hv538, u538⟩ := u537.aluG hc ev_at_824 (off' := 0x828) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv538
  obtain ⟨n539, v539, d539, hv539, u539⟩ := u538.aluG hc ev_at_828 (off' := 0x82A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv539
  obtain ⟨n540, v540, d540, hv540, u540⟩ := u539.aluG hc ev_at_82a (off' := 0x82E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv540
  obtain ⟨n541, d541, u541⟩ := u540.swG hc ev_at_82e (off' := 0x832) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 256) (by decide)) (a := F + 0x100) (v := v540)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm541, hM541⟩ : ∃ M', memStore32 Mi (F + 0x100) v540 = M' := ⟨_, rfl⟩
  rw [hM541] at u541
  have hc541 : CodeIn Mm541 B ed25519VerifyCode := by rw [← hM541]; exact hc.store32 (frm_sep' sFC (by decide))
  have fr541 : ∀ x, Sep F 0x128 x 1 → Mm541 x = M0 x := fun x hx => by
    rw [← hM541, memStore32_get_sep (frm_sep' hx (by decide)), fr x hx]
  obtain ⟨n542, v542, d542, hv542, u542⟩ := u541.aluG hc541 ev_at_832 (off' := 0x834) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv542
  obtain ⟨n543, v543, d543, hv543, u543⟩ := u542.aluG hc541 ev_at_834 (off' := 0x838) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv543
  obtain ⟨n544, d544, u544⟩ := u543.lwE hc541 ev_at_838 (off' := 0x83A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 120) (by decide)) (v := v337)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x78) 4 from sep_offsets F (c := 256) (n := 4) (d := 120) (k := 4) (by decide) (by decide) (by decide)), sl78])
  obtain ⟨n545, v545, d545, hv545, u545⟩ := u544.aluG hc541 ev_at_83a (off' := 0x83C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv545
  obtain ⟨n546, d546, u546⟩ := u545.swG hc541 ev_at_83c (off' := 0x83E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 120) (by decide)) (a := F + 0x78) (v := v545)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31])
  obtain ⟨Mm546, hM546⟩ : ∃ M', memStore32 Mm541 (F + 0x78) v545 = M' := ⟨_, rfl⟩
  rw [hM546] at u546
  have hc546 : CodeIn Mm546 B ed25519VerifyCode := by rw [← hM546]; exact hc541.store32 (frm_sep' sFC (by decide))
  have fr546 : ∀ x, Sep F 0x128 x 1 → Mm546 x = M0 x := fun x hx => by
    rw [← hM546, memStore32_get_sep (frm_sep' hx (by decide)), fr541 x hx]
  obtain ⟨n547, v547, d547, hv547, u547⟩ := u546.aluG hc546 ev_at_83e (off' := 0x840) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv547
  obtain ⟨n548, v548, d548, hv548, u548⟩ := u547.aluG hc546 ev_at_840 (off' := 0x842) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv548
  obtain ⟨n549, v549, d549, hv549, u549⟩ := u548.aluG hc546 ev_at_842 (off' := 0x846) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv549
  obtain ⟨n550, v550, d550, hv550, u550⟩ := u549.aluG hc546 ev_at_846 (off' := 0x848) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv550
  obtain ⟨n551, d551, u551⟩ := u550.lwE hc546 ev_at_848 (off' := 0x84A) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 140) (by decide)) (v := v236)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x8C) 4 from sep_offsets F (c := 120) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x8C) 4 from sep_offsets F (c := 256) (n := 4) (d := 140) (k := 4) (by decide) (by decide) (by decide)), sl8C])
  obtain ⟨n552, v552, d552, hv552, u552⟩ := u551.aluImmG hc546 ev_at_84a (off' := 0x84C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv552
  obtain ⟨n553, v553, d553, hv553, u553⟩ := u552.aluG hc546 ev_at_84c (off' := 0x84E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv553
  obtain ⟨n554, d554, u554⟩ := u553.lwE hc546 ev_at_84e (off' := 0x850) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 128) (by decide)) (v := v254)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x80) 4 from sep_offsets F (c := 120) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x80) 4 from sep_offsets F (c := 256) (n := 4) (d := 128) (k := 4) (by decide) (by decide) (by decide)), sl80])
  obtain ⟨n555, v555, d555, hv555, u555⟩ := u554.aluG hc546 ev_at_850 (off' := 0x854) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv555
  obtain ⟨n556, v556, d556, hv556, u556⟩ := u555.aluG hc546 ev_at_854 (off' := 0x858) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv556
  obtain ⟨n557, v557, d557, hv557, u557⟩ := u556.aluG hc546 ev_at_858 (off' := 0x85C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv557
  obtain ⟨n558, d558, u558⟩ := u557.lwE hc546 ev_at_85c (off' := 0x85E) (by decide)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; exact aligned_add hF (k := 116) (by decide)) (v := v320)
    (by simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]; rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x74) 4 from sep_offsets F (c := 120) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x74) 4 from sep_offsets F (c := 256) (n := 4) (d := 116) (k := 4) (by decide) (by decide) (by decide)), sl74])
  obtain ⟨n559, v559, d559, hv559, u559⟩ := u558.aluG hc546 ev_at_85e (off' := 0x862) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv559
  have qo1 : reg n559 ra = v409 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n559 sp = F := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n559 (3 : Fin 32) = G3 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n559 (4 : Fin 32) = G4 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n559 (5 : Fin 32) = v279 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n559 (6 : Fin 32) = v419 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n559 (7 : Fin 32) = v533 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n559 (8 : Fin 32) = v538 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n559 (9 : Fin 32) = v536 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n559 a0 = v553 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n559 a1 = v555 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n559 a2 = v559 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n559 a3 = v320 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n559 a4 = v527 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n559 a5 = v534 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n559 a6 = v556 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n559 a7 = v509 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n559 (18 : Fin 32) = v7 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n559 (19 : Fin 32) = v133 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n559 (20 : Fin 32) = v310 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n559 (21 : Fin 32) = v485 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n559 (22 : Fin 32) = v557 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n559 (23 : Fin 32) = v302 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n559 (24 : Fin 32) = v476 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n559 (25 : Fin 32) = v352 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n559 (26 : Fin 32) = v480 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n559 (27 : Fin 32) = v530 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n559 (28 : Fin 32) = v254 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n559 (29 : Fin 32) = v545 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n559 (30 : Fin 32) = v388 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n559 (31 : Fin 32) = v537 := by rw [u559.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have soC : memLoad32 Mm546 (F + 0xC) = G21 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xC) 4 from sep_offsets F (c := 120) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xC) 4 from sep_offsets F (c := 256) (n := 4) (d := 12) (k := 4) (by decide) (by decide) (by decide)), slC]
  have so10 : memLoad32 Mm546 (F + 0x10) = memLoad32 M0 (F + 0x10) := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x10) 4 from sep_offsets F (c := 120) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x10) 4 from sep_offsets F (c := 256) (n := 4) (d := 16) (k := 4) (by decide) (by decide) (by decide)), sl10]
  have so70 : memLoad32 Mm546 (F + 0x70) = v308 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x70) 4 from sep_offsets F (c := 120) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x70) 4 from sep_offsets F (c := 256) (n := 4) (d := 112) (k := 4) (by decide) (by decide) (by decide)), sl70]
  have so78 : memLoad32 Mm546 (F + 0x78) = v545 := by
    rw [← hM546, memLoad32_store32_same]
  have so7C : memLoad32 Mm546 (F + 0x7C) = v312 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x7C) 4 from sep_offsets F (c := 120) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x7C) 4 from sep_offsets F (c := 256) (n := 4) (d := 124) (k := 4) (by decide) (by decide) (by decide)), sl7C]
  have so88 : memLoad32 Mm546 (F + 0x88) = v36 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x88) 4 from sep_offsets F (c := 120) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x88) 4 from sep_offsets F (c := 256) (n := 4) (d := 136) (k := 4) (by decide) (by decide) (by decide)), sl88]
  have so90 : memLoad32 Mm546 (F + 0x90) = v151 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x90) 4 from sep_offsets F (c := 120) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x90) 4 from sep_offsets F (c := 256) (n := 4) (d := 144) (k := 4) (by decide) (by decide) (by decide)), sl90]
  have so94 : memLoad32 Mm546 (F + 0x94) = v481 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x94) 4 from sep_offsets F (c := 120) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x94) 4 from sep_offsets F (c := 256) (n := 4) (d := 148) (k := 4) (by decide) (by decide) (by decide)), sl94]
  have so9C : memLoad32 Mm546 (F + 0x9C) = v75 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x9C) 4 from sep_offsets F (c := 120) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x9C) 4 from sep_offsets F (c := 256) (n := 4) (d := 156) (k := 4) (by decide) (by decide) (by decide)), sl9C]
  have soA0 : memLoad32 Mm546 (F + 0xA0) = v87 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xA0) 4 from sep_offsets F (c := 120) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xA0) 4 from sep_offsets F (c := 256) (n := 4) (d := 160) (k := 4) (by decide) (by decide) (by decide)), slA0]
  have soA4 : memLoad32 Mm546 (F + 0xA4) = v357 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xA4) 4 from sep_offsets F (c := 120) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xA4) 4 from sep_offsets F (c := 256) (n := 4) (d := 164) (k := 4) (by decide) (by decide) (by decide)), slA4]
  have soA8 : memLoad32 Mm546 (F + 0xA8) = v279 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xA8) 4 from sep_offsets F (c := 120) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xA8) 4 from sep_offsets F (c := 256) (n := 4) (d := 168) (k := 4) (by decide) (by decide) (by decide)), slA8]
  have soAC : memLoad32 Mm546 (F + 0xAC) = v219 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xAC) 4 from sep_offsets F (c := 120) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xAC) 4 from sep_offsets F (c := 256) (n := 4) (d := 172) (k := 4) (by decide) (by decide) (by decide)), slAC]
  have soB0 : memLoad32 Mm546 (F + 0xB0) = v16 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xB0) 4 from sep_offsets F (c := 120) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xB0) 4 from sep_offsets F (c := 256) (n := 4) (d := 176) (k := 4) (by decide) (by decide) (by decide)), slB0]
  have soB8 : memLoad32 Mm546 (F + 0xB8) = v136 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xB8) 4 from sep_offsets F (c := 120) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xB8) 4 from sep_offsets F (c := 256) (n := 4) (d := 184) (k := 4) (by decide) (by decide) (by decide)), slB8]
  have soBC : memLoad32 Mm546 (F + 0xBC) = v467 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xBC) 4 from sep_offsets F (c := 120) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xBC) 4 from sep_offsets F (c := 256) (n := 4) (d := 188) (k := 4) (by decide) (by decide) (by decide)), slBC]
  have soC0 : memLoad32 Mm546 (F + 0xC0) = v405 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xC0) 4 from sep_offsets F (c := 120) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xC0) 4 from sep_offsets F (c := 256) (n := 4) (d := 192) (k := 4) (by decide) (by decide) (by decide)), slC0]
  have soC4 : memLoad32 Mm546 (F + 0xC4) = v199 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xC4) 4 from sep_offsets F (c := 120) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xC4) 4 from sep_offsets F (c := 256) (n := 4) (d := 196) (k := 4) (by decide) (by decide) (by decide)), slC4]
  have soC8 : memLoad32 Mm546 (F + 0xC8) = v335 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xC8) 4 from sep_offsets F (c := 120) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xC8) 4 from sep_offsets F (c := 256) (n := 4) (d := 200) (k := 4) (by decide) (by decide) (by decide)), slC8]
  have soCC : memLoad32 Mm546 (F + 0xCC) = v264 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xCC) 4 from sep_offsets F (c := 120) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xCC) 4 from sep_offsets F (c := 256) (n := 4) (d := 204) (k := 4) (by decide) (by decide) (by decide)), slCC]
  have soD0 : memLoad32 Mm546 (F + 0xD0) = memLoad32 M0 (F + 0xD0) := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xD0) 4 from sep_offsets F (c := 120) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xD0) 4 from sep_offsets F (c := 256) (n := 4) (d := 208) (k := 4) (by decide) (by decide) (by decide)), slD0]
  have soD4 : memLoad32 Mm546 (F + 0xD4) = v239 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xD4) 4 from sep_offsets F (c := 120) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xD4) 4 from sep_offsets F (c := 256) (n := 4) (d := 212) (k := 4) (by decide) (by decide) (by decide)), slD4]
  have soD8 : memLoad32 Mm546 (F + 0xD8) = v174 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xD8) 4 from sep_offsets F (c := 120) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xD8) 4 from sep_offsets F (c := 256) (n := 4) (d := 216) (k := 4) (by decide) (by decide) (by decide)), slD8]
  have soDC : memLoad32 Mm546 (F + 0xDC) = v150 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xDC) 4 from sep_offsets F (c := 120) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xDC) 4 from sep_offsets F (c := 256) (n := 4) (d := 220) (k := 4) (by decide) (by decide) (by decide)), slDC]
  have soE0 : memLoad32 Mm546 (F + 0xE0) = v133 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xE0) 4 from sep_offsets F (c := 120) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xE0) 4 from sep_offsets F (c := 256) (n := 4) (d := 224) (k := 4) (by decide) (by decide) (by decide)), slE0]
  have soE4 : memLoad32 Mm546 (F + 0xE4) = v7 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xE4) 4 from sep_offsets F (c := 120) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xE4) 4 from sep_offsets F (c := 256) (n := 4) (d := 228) (k := 4) (by decide) (by decide) (by decide)), slE4]
  have soEC : memLoad32 Mm546 (F + 0xEC) = v341 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xEC) 4 from sep_offsets F (c := 120) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xEC) 4 from sep_offsets F (c := 256) (n := 4) (d := 236) (k := 4) (by decide) (by decide) (by decide)), slEC]
  have soF0 : memLoad32 Mm546 (F + 0xF0) = v206 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xF0) 4 from sep_offsets F (c := 120) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xF0) 4 from sep_offsets F (c := 256) (n := 4) (d := 240) (k := 4) (by decide) (by decide) (by decide)), slF0]
  have soF4 : memLoad32 Mm546 (F + 0xF4) = v297 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xF4) 4 from sep_offsets F (c := 120) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xF4) 4 from sep_offsets F (c := 256) (n := 4) (d := 244) (k := 4) (by decide) (by decide) (by decide)), slF4]
  have soF8 : memLoad32 Mm546 (F + 0xF8) = v284 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0xF8) 4 from sep_offsets F (c := 120) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0xF8) 4 from sep_offsets F (c := 256) (n := 4) (d := 248) (k := 4) (by decide) (by decide) (by decide)), slF8]
  have so100 : memLoad32 Mm546 (F + 0x100) = v540 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x100) 4 from sep_offsets F (c := 120) (n := 4) (d := 256) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_same]
  have so104 : memLoad32 Mm546 (F + 0x104) = v62 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x104) 4 from sep_offsets F (c := 120) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x104) 4 from sep_offsets F (c := 256) (n := 4) (d := 260) (k := 4) (by decide) (by decide) (by decide)), sl104]
  have so108 : memLoad32 Mm546 (F + 0x108) = v203 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x108) 4 from sep_offsets F (c := 120) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x108) 4 from sep_offsets F (c := 256) (n := 4) (d := 264) (k := 4) (by decide) (by decide) (by decide)), sl108]
  have so10C : memLoad32 Mm546 (F + 0x10C) = v274 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x10C) 4 from sep_offsets F (c := 120) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x10C) 4 from sep_offsets F (c := 256) (n := 4) (d := 268) (k := 4) (by decide) (by decide) (by decide)), sl10C]
  have so110 : memLoad32 Mm546 (F + 0x110) = v67 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x110) 4 from sep_offsets F (c := 120) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x110) 4 from sep_offsets F (c := 256) (n := 4) (d := 272) (k := 4) (by decide) (by decide) (by decide)), sl110]
  have so114 : memLoad32 Mm546 (F + 0x114) = v111 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x114) 4 from sep_offsets F (c := 120) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x114) 4 from sep_offsets F (c := 256) (n := 4) (d := 276) (k := 4) (by decide) (by decide) (by decide)), sl114]
  have so118 : memLoad32 Mm546 (F + 0x118) = v122 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x118) 4 from sep_offsets F (c := 120) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x118) 4 from sep_offsets F (c := 256) (n := 4) (d := 280) (k := 4) (by decide) (by decide) (by decide)), sl118]
  have so11C : memLoad32 Mm546 (F + 0x11C) = v231 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x11C) 4 from sep_offsets F (c := 120) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x11C) 4 from sep_offsets F (c := 256) (n := 4) (d := 284) (k := 4) (by decide) (by decide) (by decide)), sl11C]
  have so120 : memLoad32 Mm546 (F + 0x120) = v116 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x120) 4 from sep_offsets F (c := 120) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x120) 4 from sep_offsets F (c := 256) (n := 4) (d := 288) (k := 4) (by decide) (by decide) (by decide)), sl120]
  have so124 : memLoad32 Mm546 (F + 0x124) = v124 := by
    rw [← hM546, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x124) 4 from sep_offsets F (c := 120) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), ← hM541, memLoad32_store32_sep (show Sep (F + 0x100) 4 (F + 0x124) 4 from sep_offsets F (c := 256) (n := 4) (d := 292) (k := 4) (by decide) (by decide) (by decide)), sl124]
  exact ⟨n559, Mm546, v520, v521, v523, v525, v526, v527, v528, v529, v530, v531, v532, v533, v534, v535, v536, v537, v538, v539, v540, v542, v543, v545, v547, v548, v549, v550, v552, v553, v555, v556, v557, v559, (.cons d520 (.cons d521 (.cons d522 (.cons d523 (.cons d524 (.cons d525 (.cons d526 (.cons d527 (.cons d528 (.cons d529 (.cons d530 (.cons d531 (.cons d532 (.cons d533 (.cons d534 (.cons d535 (.cons d536 (.cons d537 (.cons d538 (.cons d539 (.cons d540 (.cons d541 (.cons d542 (.cons d543 (.cons d544 (.cons d545 (.cons d546 (.cons d547 (.cons d548 (.cons d549 (.cons d550 (.cons d551 (.cons d552 (.cons d553 (.cons d554 (.cons d555 (.cons d556 (.cons d557 (.cons d558 (.single d559)))))))))))))))))))))))))))))))))))))))), u559.self, hc546, fr546, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, soC, so10, so70, so78, so7C, so88, so90, so94, so9C, soA0, soA4, soA8, soAC, soB0, soB8, soBC, soC0, soC4, soC8, soCC, soD0, soD4, soD8, soDC, soE0, soE4, soEC, soF0, soF4, soF8, so100, so104, so108, so10C, so110, so114, so118, so11C, so120, so124, hv520, hv521, hv523, hv525, hv526, hv527, hv528, hv529, hv530, hv531, hv532, hv533, hv534, hv535, hv536, hv537, hv538, hv539, hv540, hv542, hv543, hv545, hv547, hv548, hv549, hv550, hv552, hv553, hv555, hv556, hv557, hv559⟩

end C3.RV32
