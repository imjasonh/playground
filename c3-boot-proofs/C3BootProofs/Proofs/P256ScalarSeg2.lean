import C3BootProofs.Proofs.P256ScalarDecode

/-! # P-256's `Scalar::mul`, segments 8 to 11

Each theorem steps 40 instructions. `scripts/gen-p256-scalar.py` writes this file. -/

namespace C3.RV32

open C3.Image

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g8 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v12 v17 v18 v19 v168 v169 v170 v171 v250 v264 v270 v275 v277 v280 v285 v287 v291 v295 v300 v302 v306 v310 v314 v317 v318 v319 : Word}
    (s : St Mi B n 0x43E (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v300)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v280)
    (q8 : reg n (8 : Fin 32) = v302)
    (q9 : reg n (9 : Fin 32) = v295)
    (q10 : reg n a0 = v318)
    (q11 : reg n a1 = v317)
    (q12 : reg n a2 = v168)
    (q13 : reg n a3 = v319)
    (q14 : reg n a4 = v310)
    (q15 : reg n a5 = v287)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v170)
    (q19 : reg n (19 : Fin 32) = v277)
    (q20 : reg n (20 : Fin 32) = v275)
    (q21 : reg n (21 : Fin 32) = v285)
    (q22 : reg n (22 : Fin 32) = v314)
    (q23 : reg n (23 : Fin 32) = v250)
    (q24 : reg n (24 : Fin 32) = v264)
    (q25 : reg n (25 : Fin 32) = v270)
    (q26 : reg n (26 : Fin 32) = v306)
    (q27 : reg n (27 : Fin 32) = v169)
    (q28 : reg n (28 : Fin 32) = v291)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v171)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v320 v321 v322 v323 v324 v325 v326 v327 v328 v329 v330 v331 v332 v333 v334 v335 v336 v337 v338 v339 v340 v341 v342 v343 v344 v345 v346 v347 v348 v349 v350 v351 v352 v353 v354 v355 v356 v357 v358 v359 : Word),
      Steps n n' ∧
      St M' B n' 0x4C0 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v300 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v337 ∧
      reg n' (8 : Fin 32) = v338 ∧
      reg n' (9 : Fin 32) = v342 ∧
      reg n' a0 = v357 ∧
      reg n' a1 = v352 ∧
      reg n' a2 = v348 ∧
      reg n' a3 = v359 ∧
      reg n' a4 = v356 ∧
      reg n' a5 = v355 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v170 ∧
      reg n' (19 : Fin 32) = v351 ∧
      reg n' (20 : Fin 32) = v326 ∧
      reg n' (21 : Fin 32) = v331 ∧
      reg n' (22 : Fin 32) = v314 ∧
      reg n' (23 : Fin 32) = v320 ∧
      reg n' (24 : Fin 32) = v264 ∧
      reg n' (25 : Fin 32) = v270 ∧
      reg n' (26 : Fin 32) = v306 ∧
      reg n' (27 : Fin 32) = v169 ∧
      reg n' (28 : Fin 32) = v345 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v171 ∧
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
      aluEval .add v318 v317 = v320 ∧
      aluEval .add v319 v310 = v321 ∧
      aluEval .sltu v320 v318 = v322 ∧
      aluEval .add v322 v321 = v323 ∧
      aluEval .sub v275 v168 = v324 ∧
      aluEval .sltu v324 v275 = v325 ∧
      aluEval .add v324 v323 = v326 ∧
      aluEval .add v325 v302 = v327 ∧
      aluEval .sltu v326 v324 = v328 ∧
      aluEval .sltu v285 v277 = v329 ∧
      aluEval .add v328 v327 = v330 ∧
      aluEval .add v285 v330 = v331 ∧
      aluEval .mul v169 v3 = v332 ∧
      aluEval .add v329 v280 = v333 ∧
      aluEval .sltu v331 v330 = v334 ∧
      aluEval .add v168 v333 = v335 ∧
      aluEval .mul v169 v4 = v336 ∧
      aluEval .add v334 v335 = v337 ∧
      aluEval .mulhu v169 v3 = v338 ∧
      aluEval .sltu v335 v333 = v339 ∧
      aluEval .sltu v337 v335 = v340 ∧
      aluEval .and v291 0xFFFFFFFE = v341 ∧
      aluEval .mulhu v169 v4 = v342 ∧
      aluEval .add v332 v341 = v343 ∧
      aluEval .mul v169 v12 = v344 ∧
      aluEval .add v339 v340 = v345 ∧
      aluEval .sltu v343 v341 = v346 ∧
      aluEval .add v336 v300 = v347 ∧
      aluEval .mulhu v169 v12 = v348 ∧
      aluEval .add v346 v338 = v349 ∧
      aluEval .sltu v347 v300 = v350 ∧
      aluEval .add v347 v349 = v351 ∧
      aluEval .mul v169 v19 = v352 ∧
      aluEval .add v350 v342 = v353 ∧
      aluEval .sltu v351 v347 = v354 ∧
      aluEval .add v344 v306 = v355 ∧
      aluEval .mulhu v169 v19 = v356 ∧
      aluEval .add v354 v353 = v357 ∧
      aluEval .sltu v355 v306 = v358 ∧
      aluEval .add v358 v348 = v359 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n320, v320, d320, hv320, u320⟩ := s.aluG hc psm_at_43e (off' := 0x442) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv320
  obtain ⟨n321, v321, d321, hv321, u321⟩ := u320.aluG hc psm_at_442 (off' := 0x444) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv321
  obtain ⟨n322, v322, d322, hv322, u322⟩ := u321.aluG hc psm_at_444 (off' := 0x448) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv322
  obtain ⟨n323, v323, d323, hv323, u323⟩ := u322.aluG hc psm_at_448 (off' := 0x44A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv323
  obtain ⟨n324, v324, d324, hv324, u324⟩ := u323.aluG hc psm_at_44a (off' := 0x44E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv324
  obtain ⟨n325, v325, d325, hv325, u325⟩ := u324.aluG hc psm_at_44e (off' := 0x452) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv325
  obtain ⟨n326, v326, d326, hv326, u326⟩ := u325.aluG hc psm_at_452 (off' := 0x456) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv326
  obtain ⟨n327, v327, d327, hv327, u327⟩ := u326.aluG hc psm_at_456 (off' := 0x458) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv327
  obtain ⟨n328, v328, d328, hv328, u328⟩ := u327.aluG hc psm_at_458 (off' := 0x45C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv328
  obtain ⟨n329, v329, d329, hv329, u329⟩ := u328.aluG hc psm_at_45c (off' := 0x460) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv329
  obtain ⟨n330, v330, d330, hv330, u330⟩ := u329.aluG hc psm_at_460 (off' := 0x462) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv330
  obtain ⟨n331, v331, d331, hv331, u331⟩ := u330.aluG hc psm_at_462 (off' := 0x464) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv331
  obtain ⟨n332, v332, d332, hv332, u332⟩ := u331.aluG hc psm_at_464 (off' := 0x468) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv332
  obtain ⟨n333, v333, d333, hv333, u333⟩ := u332.aluG hc psm_at_468 (off' := 0x46A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv333
  obtain ⟨n334, v334, d334, hv334, u334⟩ := u333.aluG hc psm_at_46a (off' := 0x46E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv334
  obtain ⟨n335, v335, d335, hv335, u335⟩ := u334.aluG hc psm_at_46e (off' := 0x470) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv335
  obtain ⟨n336, v336, d336, hv336, u336⟩ := u335.aluG hc psm_at_470 (off' := 0x474) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv336
  obtain ⟨n337, v337, d337, hv337, u337⟩ := u336.aluG hc psm_at_474 (off' := 0x476) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv337
  obtain ⟨n338, v338, d338, hv338, u338⟩ := u337.aluG hc psm_at_476 (off' := 0x47A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv338
  obtain ⟨n339, v339, d339, hv339, u339⟩ := u338.aluG hc psm_at_47a (off' := 0x47E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv339
  obtain ⟨n340, v340, d340, hv340, u340⟩ := u339.aluG hc psm_at_47e (off' := 0x482) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv340
  obtain ⟨n341, v341, d341, hv341, u341⟩ := u340.aluImmG hc psm_at_482 (off' := 0x486) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv341
  obtain ⟨n342, v342, d342, hv342, u342⟩ := u341.aluG hc psm_at_486 (off' := 0x48A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv342
  obtain ⟨n343, v343, d343, hv343, u343⟩ := u342.aluG hc psm_at_48a (off' := 0x48C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv343
  obtain ⟨n344, v344, d344, hv344, u344⟩ := u343.aluG hc psm_at_48c (off' := 0x490) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv344
  obtain ⟨n345, v345, d345, hv345, u345⟩ := u344.aluG hc psm_at_490 (off' := 0x494) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv345
  obtain ⟨n346, v346, d346, hv346, u346⟩ := u345.aluG hc psm_at_494 (off' := 0x498) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv346
  obtain ⟨n347, v347, d347, hv347, u347⟩ := u346.aluG hc psm_at_498 (off' := 0x49A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv347
  obtain ⟨n348, v348, d348, hv348, u348⟩ := u347.aluG hc psm_at_49a (off' := 0x49E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv348
  obtain ⟨n349, v349, d349, hv349, u349⟩ := u348.aluG hc psm_at_49e (off' := 0x4A0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv349
  obtain ⟨n350, v350, d350, hv350, u350⟩ := u349.aluG hc psm_at_4a0 (off' := 0x4A4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv350
  obtain ⟨n351, v351, d351, hv351, u351⟩ := u350.aluG hc psm_at_4a4 (off' := 0x4A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv351
  obtain ⟨n352, v352, d352, hv352, u352⟩ := u351.aluG hc psm_at_4a8 (off' := 0x4AC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv352
  obtain ⟨n353, v353, d353, hv353, u353⟩ := u352.aluG hc psm_at_4ac (off' := 0x4AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv353
  obtain ⟨n354, v354, d354, hv354, u354⟩ := u353.aluG hc psm_at_4ae (off' := 0x4B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv354
  obtain ⟨n355, v355, d355, hv355, u355⟩ := u354.aluG hc psm_at_4b2 (off' := 0x4B4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv355
  obtain ⟨n356, v356, d356, hv356, u356⟩ := u355.aluG hc psm_at_4b4 (off' := 0x4B8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv356
  obtain ⟨n357, v357, d357, hv357, u357⟩ := u356.aluG hc psm_at_4b8 (off' := 0x4BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv357
  obtain ⟨n358, v358, d358, hv358, u358⟩ := u357.aluG hc psm_at_4ba (off' := 0x4BE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv358
  obtain ⟨n359, v359, d359, hv359, u359⟩ := u358.aluG hc psm_at_4be (off' := 0x4C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv359
  have qo1 : reg n359 ra = v300 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n359 sp = F := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n359 (3 : Fin 32) = G3 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n359 (4 : Fin 32) = G4 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n359 (5 : Fin 32) = v3 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n359 (6 : Fin 32) = v12 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n359 (7 : Fin 32) = v337 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n359 (8 : Fin 32) = v338 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n359 (9 : Fin 32) = v342 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n359 a0 = v357 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n359 a1 = v352 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n359 a2 = v348 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n359 a3 = v359 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n359 a4 = v356 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n359 a5 = v355 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n359 a6 = v18 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n359 a7 = v17 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n359 (18 : Fin 32) = v170 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n359 (19 : Fin 32) = v351 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n359 (20 : Fin 32) = v326 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n359 (21 : Fin 32) = v331 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n359 (22 : Fin 32) = v314 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n359 (23 : Fin 32) = v320 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n359 (24 : Fin 32) = v264 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n359 (25 : Fin 32) = v270 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n359 (26 : Fin 32) = v306 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n359 (27 : Fin 32) = v169 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n359 (28 : Fin 32) = v345 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n359 (29 : Fin 32) = v4 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n359 (30 : Fin 32) = v19 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n359 (31 : Fin 32) = v171 := by rw [u359.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so20 : memLoad32 Mi (F + 0x20) = v7 := by
    rw [sl20]
  have so24 : memLoad32 Mi (F + 0x24) = v0 := by
    rw [sl24]
  have so28 : memLoad32 Mi (F + 0x28) = outp := by
    rw [sl28]
  have so2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [sl2C]
  have so30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [sl4C]
  have so50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [sl50]
  have so54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [sl54]
  have so58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [sl74]
  have so78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [sl8C]
  have so90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [sl90]
  have so94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [sl9C]
  exact ⟨n359, Mi, v320, v321, v322, v323, v324, v325, v326, v327, v328, v329, v330, v331, v332, v333, v334, v335, v336, v337, v338, v339, v340, v341, v342, v343, v344, v345, v346, v347, v348, v349, v350, v351, v352, v353, v354, v355, v356, v357, v358, v359, (.cons d320 (.cons d321 (.cons d322 (.cons d323 (.cons d324 (.cons d325 (.cons d326 (.cons d327 (.cons d328 (.cons d329 (.cons d330 (.cons d331 (.cons d332 (.cons d333 (.cons d334 (.cons d335 (.cons d336 (.cons d337 (.cons d338 (.cons d339 (.cons d340 (.cons d341 (.cons d342 (.cons d343 (.cons d344 (.cons d345 (.cons d346 (.cons d347 (.cons d348 (.cons d349 (.cons d350 (.cons d351 (.cons d352 (.cons d353 (.cons d354 (.cons d355 (.cons d356 (.cons d357 (.cons d358 (.single d359)))))))))))))))))))))))))))))))))))))))), u359.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv320, hv321, hv322, hv323, hv324, hv325, hv326, hv327, hv328, hv329, hv330, hv331, hv332, hv333, hv334, hv335, hv336, hv337, hv338, hv339, hv340, hv341, hv342, hv343, hv344, hv345, hv346, hv347, hv348, hv349, hv350, hv351, hv352, hv353, hv354, hv355, hv356, hv357, hv358, hv359⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g9 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v12 v17 v18 v19 v169 v170 v171 v264 v270 v300 v306 v314 v320 v326 v331 v337 v338 v342 v345 v348 v351 v352 v355 v356 v357 v359 : Word}
    (s : St Mi B n 0x4C0 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v300)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v337)
    (q8 : reg n (8 : Fin 32) = v338)
    (q9 : reg n (9 : Fin 32) = v342)
    (q10 : reg n a0 = v357)
    (q11 : reg n a1 = v352)
    (q12 : reg n a2 = v348)
    (q13 : reg n a3 = v359)
    (q14 : reg n a4 = v356)
    (q15 : reg n a5 = v355)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v170)
    (q19 : reg n (19 : Fin 32) = v351)
    (q20 : reg n (20 : Fin 32) = v326)
    (q21 : reg n (21 : Fin 32) = v331)
    (q22 : reg n (22 : Fin 32) = v314)
    (q23 : reg n (23 : Fin 32) = v320)
    (q24 : reg n (24 : Fin 32) = v264)
    (q25 : reg n (25 : Fin 32) = v270)
    (q26 : reg n (26 : Fin 32) = v306)
    (q27 : reg n (27 : Fin 32) = v169)
    (q28 : reg n (28 : Fin 32) = v345)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v171)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v360 v361 v362 v363 v364 v365 v366 v367 v368 v369 v370 v371 v372 v373 v374 v375 v376 v377 v378 v379 v380 v381 v382 v383 v384 v385 v386 v387 v388 v389 v390 v391 v392 v393 v394 v395 v396 v397 v398 v399 : Word),
      Steps n n' ∧
      St M' B n' 0x546 (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v300 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v391 ∧
      reg n' (8 : Fin 32) = v393 ∧
      reg n' (9 : Fin 32) = v342 ∧
      reg n' a0 = v399 ∧
      reg n' a1 = v394 ∧
      reg n' a2 = v360 ∧
      reg n' a3 = v398 ∧
      reg n' a4 = v390 ∧
      reg n' a5 = v366 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v170 ∧
      reg n' (19 : Fin 32) = v351 ∧
      reg n' (20 : Fin 32) = v397 ∧
      reg n' (21 : Fin 32) = v386 ∧
      reg n' (22 : Fin 32) = v380 ∧
      reg n' (23 : Fin 32) = v374 ∧
      reg n' (24 : Fin 32) = v264 ∧
      reg n' (25 : Fin 32) = v270 ∧
      reg n' (26 : Fin 32) = v306 ∧
      reg n' (27 : Fin 32) = v392 ∧
      reg n' (28 : Fin 32) = v396 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v171 ∧
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
      aluEval .add v355 v357 = v360 ∧
      aluEval .sltu v360 v355 = v361 ∧
      aluEval .mulhu v169 v17 = v362 ∧
      aluEval .add v361 v359 = v363 ∧
      aluEval .add v352 v314 = v364 ∧
      aluEval .sltu v364 v314 = v365 ∧
      aluEval .add v364 v363 = v366 ∧
      aluEval .add v365 v356 = v367 ∧
      aluEval .sltu v366 v364 = v368 ∧
      aluEval .sub v320 v169 = v369 ∧
      aluEval .mulhu v169 v18 = v370 ∧
      aluEval .add v368 v367 = v371 ∧
      aluEval .sltu v369 v320 = v372 ∧
      aluEval .add v372 v362 = v373 ∧
      aluEval .add v369 v371 = v374 ∧
      aluEval .sltu v374 v369 = v375 ∧
      aluEval .add v169 v169 = v376 ∧
      aluEval .add v375 v373 = v377 ∧
      aluEval .sub v326 v376 = v378 ∧
      aluEval .sltu v378 v326 = v379 ∧
      aluEval .add v378 v377 = v380 ∧
      aluEval .add v379 v370 = v381 ∧
      aluEval .sltu v380 v378 = v382 ∧
      aluEval .add v382 v381 = v383 ∧
      aluEval .sub v331 v169 = v384 ∧
      aluEval .sltu v384 v331 = v385 ∧
      aluEval .add v384 v383 = v386 ∧
      aluEval .add v385 v362 = v387 ∧
      aluEval .sltu v386 v384 = v388 ∧
      aluEval .add v388 v387 = v389 ∧
      aluEval .mul v170 v3 = v390 ∧
      aluEval .add v337 v389 = v391 ∧
      aluEval .add v169 v345 = v392 ∧
      aluEval .mulhu v170 v3 = v393 ∧
      aluEval .mul v170 v4 = v394 ∧
      aluEval .sltu v391 v389 = v395 ∧
      aluEval .sltu v392 v345 = v396 ∧
      aluEval .add v395 v392 = v397 ∧
      aluEval .mulhu v170 v4 = v398 ∧
      aluEval .and v351 0xFFFFFFFE = v399 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n360, v360, d360, hv360, u360⟩ := s.aluG hc psm_at_4c0 (off' := 0x4C4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv360
  obtain ⟨n361, v361, d361, hv361, u361⟩ := u360.aluG hc psm_at_4c4 (off' := 0x4C8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv361
  obtain ⟨n362, v362, d362, hv362, u362⟩ := u361.aluG hc psm_at_4c8 (off' := 0x4CC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv362
  obtain ⟨n363, v363, d363, hv363, u363⟩ := u362.aluG hc psm_at_4cc (off' := 0x4CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv363
  obtain ⟨n364, v364, d364, hv364, u364⟩ := u363.aluG hc psm_at_4ce (off' := 0x4D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv364
  obtain ⟨n365, v365, d365, hv365, u365⟩ := u364.aluG hc psm_at_4d0 (off' := 0x4D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv365
  obtain ⟨n366, v366, d366, hv366, u366⟩ := u365.aluG hc psm_at_4d4 (off' := 0x4D8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv366
  obtain ⟨n367, v367, d367, hv367, u367⟩ := u366.aluG hc psm_at_4d8 (off' := 0x4DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv367
  obtain ⟨n368, v368, d368, hv368, u368⟩ := u367.aluG hc psm_at_4da (off' := 0x4DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv368
  obtain ⟨n369, v369, d369, hv369, u369⟩ := u368.aluG hc psm_at_4de (off' := 0x4E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv369
  obtain ⟨n370, v370, d370, hv370, u370⟩ := u369.aluG hc psm_at_4e2 (off' := 0x4E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv370
  obtain ⟨n371, v371, d371, hv371, u371⟩ := u370.aluG hc psm_at_4e6 (off' := 0x4E8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv371
  obtain ⟨n372, v372, d372, hv372, u372⟩ := u371.aluG hc psm_at_4e8 (off' := 0x4EC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv372
  obtain ⟨n373, v373, d373, hv373, u373⟩ := u372.aluG hc psm_at_4ec (off' := 0x4EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv373
  obtain ⟨n374, v374, d374, hv374, u374⟩ := u373.aluG hc psm_at_4ee (off' := 0x4F2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv374
  obtain ⟨n375, v375, d375, hv375, u375⟩ := u374.aluG hc psm_at_4f2 (off' := 0x4F6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv375
  obtain ⟨n376, v376, d376, hv376, u376⟩ := u375.aluG hc psm_at_4f6 (off' := 0x4FA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv376
  obtain ⟨n377, v377, d377, hv377, u377⟩ := u376.aluG hc psm_at_4fa (off' := 0x4FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv377
  obtain ⟨n378, v378, d378, hv378, u378⟩ := u377.aluG hc psm_at_4fc (off' := 0x500) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv378
  obtain ⟨n379, v379, d379, hv379, u379⟩ := u378.aluG hc psm_at_500 (off' := 0x504) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv379
  obtain ⟨n380, v380, d380, hv380, u380⟩ := u379.aluG hc psm_at_504 (off' := 0x508) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv380
  obtain ⟨n381, v381, d381, hv381, u381⟩ := u380.aluG hc psm_at_508 (off' := 0x50A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv381
  obtain ⟨n382, v382, d382, hv382, u382⟩ := u381.aluG hc psm_at_50a (off' := 0x50E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv382
  obtain ⟨n383, v383, d383, hv383, u383⟩ := u382.aluG hc psm_at_50e (off' := 0x510) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv383
  obtain ⟨n384, v384, d384, hv384, u384⟩ := u383.aluG hc psm_at_510 (off' := 0x514) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv384
  obtain ⟨n385, v385, d385, hv385, u385⟩ := u384.aluG hc psm_at_514 (off' := 0x518) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv385
  obtain ⟨n386, v386, d386, hv386, u386⟩ := u385.aluG hc psm_at_518 (off' := 0x51C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv386
  obtain ⟨n387, v387, d387, hv387, u387⟩ := u386.aluG hc psm_at_51c (off' := 0x51E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv387
  obtain ⟨n388, v388, d388, hv388, u388⟩ := u387.aluG hc psm_at_51e (off' := 0x522) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv388
  obtain ⟨n389, v389, d389, hv389, u389⟩ := u388.aluG hc psm_at_522 (off' := 0x524) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv389
  obtain ⟨n390, v390, d390, hv390, u390⟩ := u389.aluG hc psm_at_524 (off' := 0x528) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv390
  obtain ⟨n391, v391, d391, hv391, u391⟩ := u390.aluG hc psm_at_528 (off' := 0x52A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv391
  obtain ⟨n392, v392, d392, hv392, u392⟩ := u391.aluG hc psm_at_52a (off' := 0x52C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv392
  obtain ⟨n393, v393, d393, hv393, u393⟩ := u392.aluG hc psm_at_52c (off' := 0x530) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv393
  obtain ⟨n394, v394, d394, hv394, u394⟩ := u393.aluG hc psm_at_530 (off' := 0x534) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv394
  obtain ⟨n395, v395, d395, hv395, u395⟩ := u394.aluG hc psm_at_534 (off' := 0x538) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv395
  obtain ⟨n396, v396, d396, hv396, u396⟩ := u395.aluG hc psm_at_538 (off' := 0x53C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv396
  obtain ⟨n397, v397, d397, hv397, u397⟩ := u396.aluG hc psm_at_53c (off' := 0x53E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv397
  obtain ⟨n398, v398, d398, hv398, u398⟩ := u397.aluG hc psm_at_53e (off' := 0x542) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv398
  obtain ⟨n399, v399, d399, hv399, u399⟩ := u398.aluImmG hc psm_at_542 (off' := 0x546) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv399
  have qo1 : reg n399 ra = v300 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n399 sp = F := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n399 (3 : Fin 32) = G3 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n399 (4 : Fin 32) = G4 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n399 (5 : Fin 32) = v3 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n399 (6 : Fin 32) = v12 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n399 (7 : Fin 32) = v391 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n399 (8 : Fin 32) = v393 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n399 (9 : Fin 32) = v342 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n399 a0 = v399 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n399 a1 = v394 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n399 a2 = v360 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n399 a3 = v398 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n399 a4 = v390 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n399 a5 = v366 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n399 a6 = v18 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n399 a7 = v17 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n399 (18 : Fin 32) = v170 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n399 (19 : Fin 32) = v351 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n399 (20 : Fin 32) = v397 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n399 (21 : Fin 32) = v386 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n399 (22 : Fin 32) = v380 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n399 (23 : Fin 32) = v374 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n399 (24 : Fin 32) = v264 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n399 (25 : Fin 32) = v270 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n399 (26 : Fin 32) = v306 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n399 (27 : Fin 32) = v392 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n399 (28 : Fin 32) = v396 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n399 (29 : Fin 32) = v4 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n399 (30 : Fin 32) = v19 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n399 (31 : Fin 32) = v171 := by rw [u399.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so20 : memLoad32 Mi (F + 0x20) = v7 := by
    rw [sl20]
  have so24 : memLoad32 Mi (F + 0x24) = v0 := by
    rw [sl24]
  have so28 : memLoad32 Mi (F + 0x28) = outp := by
    rw [sl28]
  have so2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [sl2C]
  have so30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [sl4C]
  have so50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [sl50]
  have so54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [sl54]
  have so58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [sl74]
  have so78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [sl8C]
  have so90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [sl90]
  have so94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [sl9C]
  exact ⟨n399, Mi, v360, v361, v362, v363, v364, v365, v366, v367, v368, v369, v370, v371, v372, v373, v374, v375, v376, v377, v378, v379, v380, v381, v382, v383, v384, v385, v386, v387, v388, v389, v390, v391, v392, v393, v394, v395, v396, v397, v398, v399, (.cons d360 (.cons d361 (.cons d362 (.cons d363 (.cons d364 (.cons d365 (.cons d366 (.cons d367 (.cons d368 (.cons d369 (.cons d370 (.cons d371 (.cons d372 (.cons d373 (.cons d374 (.cons d375 (.cons d376 (.cons d377 (.cons d378 (.cons d379 (.cons d380 (.cons d381 (.cons d382 (.cons d383 (.cons d384 (.cons d385 (.cons d386 (.cons d387 (.cons d388 (.cons d389 (.cons d390 (.cons d391 (.cons d392 (.cons d393 (.cons d394 (.cons d395 (.cons d396 (.cons d397 (.cons d398 (.single d399)))))))))))))))))))))))))))))))))))))))), u399.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv360, hv361, hv362, hv363, hv364, hv365, hv366, hv367, hv368, hv369, hv370, hv371, hv372, hv373, hv374, hv375, hv376, hv377, hv378, hv379, hv380, hv381, hv382, hv383, hv384, hv385, hv386, hv387, hv388, hv389, hv390, hv391, hv392, hv393, hv394, hv395, hv396, hv397, hv398, hv399⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g10 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v12 v17 v18 v19 v170 v171 v264 v270 v300 v306 v342 v351 v360 v366 v374 v380 v386 v390 v391 v392 v393 v394 v396 v397 v398 v399 : Word}
    (s : St Mi B n 0x546 (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v300)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v391)
    (q8 : reg n (8 : Fin 32) = v393)
    (q9 : reg n (9 : Fin 32) = v342)
    (q10 : reg n a0 = v399)
    (q11 : reg n a1 = v394)
    (q12 : reg n a2 = v360)
    (q13 : reg n a3 = v398)
    (q14 : reg n a4 = v390)
    (q15 : reg n a5 = v366)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v170)
    (q19 : reg n (19 : Fin 32) = v351)
    (q20 : reg n (20 : Fin 32) = v397)
    (q21 : reg n (21 : Fin 32) = v386)
    (q22 : reg n (22 : Fin 32) = v380)
    (q23 : reg n (23 : Fin 32) = v374)
    (q24 : reg n (24 : Fin 32) = v264)
    (q25 : reg n (25 : Fin 32) = v270)
    (q26 : reg n (26 : Fin 32) = v306)
    (q27 : reg n (27 : Fin 32) = v392)
    (q28 : reg n (28 : Fin 32) = v396)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v171)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v400 v401 v402 v403 v404 v405 v406 v407 v408 v409 v410 v411 v412 v413 v414 v415 v416 v417 v418 v419 v420 v421 v422 v423 v424 v425 v426 v427 v428 v429 v430 v431 v432 v433 v434 v435 v436 v437 v438 v439 : Word),
      Steps n n' ∧
      St M' B n' 0x5CA (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v300 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v3 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v391 ∧
      reg n' (8 : Fin 32) = v437 ∧
      reg n' (9 : Fin 32) = v426 ∧
      reg n' a0 = v418 ∧
      reg n' a1 = v435 ∧
      reg n' a2 = v417 ∧
      reg n' a3 = v439 ∧
      reg n' a4 = v427 ∧
      reg n' a5 = v414 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v170 ∧
      reg n' (19 : Fin 32) = v401 ∧
      reg n' (20 : Fin 32) = v397 ∧
      reg n' (21 : Fin 32) = v438 ∧
      reg n' (22 : Fin 32) = v380 ∧
      reg n' (23 : Fin 32) = v431 ∧
      reg n' (24 : Fin 32) = v410 ∧
      reg n' (25 : Fin 32) = v424 ∧
      reg n' (26 : Fin 32) = v306 ∧
      reg n' (27 : Fin 32) = v392 ∧
      reg n' (28 : Fin 32) = v396 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v171 ∧
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
      aluEval .mul v170 v12 = v400 ∧
      aluEval .sltu v397 v392 = v401 ∧
      aluEval .add v390 v399 = v402 ∧
      aluEval .sltu v402 v399 = v403 ∧
      aluEval .mulhu v170 v12 = v404 ∧
      aluEval .add v403 v393 = v405 ∧
      aluEval .add v394 v360 = v406 ∧
      aluEval .sltu v406 v360 = v407 ∧
      aluEval .mul v170 v19 = v408 ∧
      aluEval .add v407 v398 = v409 ∧
      aluEval .add v406 v405 = v410 ∧
      aluEval .add v400 v366 = v411 ∧
      aluEval .mulhu v170 v19 = v412 ∧
      aluEval .sltu v410 v406 = v413 ∧
      aluEval .sltu v411 v366 = v414 ∧
      aluEval .add v413 v409 = v415 ∧
      aluEval .add v404 v414 = v416 ∧
      aluEval .add v411 v415 = v417 ∧
      aluEval .mulhu v170 v17 = v418 ∧
      aluEval .sltu v417 v411 = v419 ∧
      aluEval .add v408 v374 = v420 ∧
      aluEval .add v419 v416 = v421 ∧
      aluEval .sltu v420 v374 = v422 ∧
      aluEval .add v412 v422 = v423 ∧
      aluEval .add v420 v421 = v424 ∧
      aluEval .sub v380 v170 = v425 ∧
      aluEval .mulhu v170 v18 = v426 ∧
      aluEval .sltu v424 v420 = v427 ∧
      aluEval .sltu v425 v380 = v428 ∧
      aluEval .add v423 v427 = v429 ∧
      aluEval .add v428 v418 = v430 ∧
      aluEval .add v425 v429 = v431 ∧
      aluEval .add v170 v170 = v432 ∧
      aluEval .sltu v431 v425 = v433 ∧
      aluEval .sub v386 v432 = v434 ∧
      aluEval .add v433 v430 = v435 ∧
      aluEval .sltu v434 v386 = v436 ∧
      aluEval .add v436 v426 = v437 ∧
      aluEval .add v434 v435 = v438 ∧
      aluEval .sltu v438 v434 = v439 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n400, v400, d400, hv400, u400⟩ := s.aluG hc psm_at_546 (off' := 0x54A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv400
  obtain ⟨n401, v401, d401, hv401, u401⟩ := u400.aluG hc psm_at_54a (off' := 0x54E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv401
  obtain ⟨n402, v402, d402, hv402, u402⟩ := u401.aluG hc psm_at_54e (off' := 0x550) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv402
  obtain ⟨n403, v403, d403, hv403, u403⟩ := u402.aluG hc psm_at_550 (off' := 0x554) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv403
  obtain ⟨n404, v404, d404, hv404, u404⟩ := u403.aluG hc psm_at_554 (off' := 0x558) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv404
  obtain ⟨n405, v405, d405, hv405, u405⟩ := u404.aluG hc psm_at_558 (off' := 0x55A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv405
  obtain ⟨n406, v406, d406, hv406, u406⟩ := u405.aluG hc psm_at_55a (off' := 0x55C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv406
  obtain ⟨n407, v407, d407, hv407, u407⟩ := u406.aluG hc psm_at_55c (off' := 0x560) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv407
  obtain ⟨n408, v408, d408, hv408, u408⟩ := u407.aluG hc psm_at_560 (off' := 0x564) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv408
  obtain ⟨n409, v409, d409, hv409, u409⟩ := u408.aluG hc psm_at_564 (off' := 0x566) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv409
  obtain ⟨n410, v410, d410, hv410, u410⟩ := u409.aluG hc psm_at_566 (off' := 0x56A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv410
  obtain ⟨n411, v411, d411, hv411, u411⟩ := u410.aluG hc psm_at_56a (off' := 0x56C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv411
  obtain ⟨n412, v412, d412, hv412, u412⟩ := u411.aluG hc psm_at_56c (off' := 0x570) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv412
  obtain ⟨n413, v413, d413, hv413, u413⟩ := u412.aluG hc psm_at_570 (off' := 0x574) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv413
  obtain ⟨n414, v414, d414, hv414, u414⟩ := u413.aluG hc psm_at_574 (off' := 0x578) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv414
  obtain ⟨n415, v415, d415, hv415, u415⟩ := u414.aluG hc psm_at_578 (off' := 0x57A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv415
  obtain ⟨n416, v416, d416, hv416, u416⟩ := u415.aluG hc psm_at_57a (off' := 0x57C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv416
  obtain ⟨n417, v417, d417, hv417, u417⟩ := u416.aluG hc psm_at_57c (off' := 0x580) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv417
  obtain ⟨n418, v418, d418, hv418, u418⟩ := u417.aluG hc psm_at_580 (off' := 0x584) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv418
  obtain ⟨n419, v419, d419, hv419, u419⟩ := u418.aluG hc psm_at_584 (off' := 0x588) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv419
  obtain ⟨n420, v420, d420, hv420, u420⟩ := u419.aluG hc psm_at_588 (off' := 0x58A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv420
  obtain ⟨n421, v421, d421, hv421, u421⟩ := u420.aluG hc psm_at_58a (off' := 0x58C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv421
  obtain ⟨n422, v422, d422, hv422, u422⟩ := u421.aluG hc psm_at_58c (off' := 0x590) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv422
  obtain ⟨n423, v423, d423, hv423, u423⟩ := u422.aluG hc psm_at_590 (off' := 0x592) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv423
  obtain ⟨n424, v424, d424, hv424, u424⟩ := u423.aluG hc psm_at_592 (off' := 0x596) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv424
  obtain ⟨n425, v425, d425, hv425, u425⟩ := u424.aluG hc psm_at_596 (off' := 0x59A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv425
  obtain ⟨n426, v426, d426, hv426, u426⟩ := u425.aluG hc psm_at_59a (off' := 0x59E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv426
  obtain ⟨n427, v427, d427, hv427, u427⟩ := u426.aluG hc psm_at_59e (off' := 0x5A2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv427
  obtain ⟨n428, v428, d428, hv428, u428⟩ := u427.aluG hc psm_at_5a2 (off' := 0x5A6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv428
  obtain ⟨n429, v429, d429, hv429, u429⟩ := u428.aluG hc psm_at_5a6 (off' := 0x5A8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv429
  obtain ⟨n430, v430, d430, hv430, u430⟩ := u429.aluG hc psm_at_5a8 (off' := 0x5AA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv430
  obtain ⟨n431, v431, d431, hv431, u431⟩ := u430.aluG hc psm_at_5aa (off' := 0x5AE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv431
  obtain ⟨n432, v432, d432, hv432, u432⟩ := u431.aluG hc psm_at_5ae (off' := 0x5B2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv432
  obtain ⟨n433, v433, d433, hv433, u433⟩ := u432.aluG hc psm_at_5b2 (off' := 0x5B6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv433
  obtain ⟨n434, v434, d434, hv434, u434⟩ := u433.aluG hc psm_at_5b6 (off' := 0x5BA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv434
  obtain ⟨n435, v435, d435, hv435, u435⟩ := u434.aluG hc psm_at_5ba (off' := 0x5BC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv435
  obtain ⟨n436, v436, d436, hv436, u436⟩ := u435.aluG hc psm_at_5bc (off' := 0x5C0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv436
  obtain ⟨n437, v437, d437, hv437, u437⟩ := u436.aluG hc psm_at_5c0 (off' := 0x5C2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv437
  obtain ⟨n438, v438, d438, hv438, u438⟩ := u437.aluG hc psm_at_5c2 (off' := 0x5C6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv438
  obtain ⟨n439, v439, d439, hv439, u439⟩ := u438.aluG hc psm_at_5c6 (off' := 0x5CA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv439
  have qo1 : reg n439 ra = v300 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n439 sp = F := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n439 (3 : Fin 32) = G3 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n439 (4 : Fin 32) = G4 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n439 (5 : Fin 32) = v3 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n439 (6 : Fin 32) = v12 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n439 (7 : Fin 32) = v391 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n439 (8 : Fin 32) = v437 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n439 (9 : Fin 32) = v426 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n439 a0 = v418 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n439 a1 = v435 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n439 a2 = v417 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n439 a3 = v439 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n439 a4 = v427 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n439 a5 = v414 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n439 a6 = v18 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n439 a7 = v17 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n439 (18 : Fin 32) = v170 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n439 (19 : Fin 32) = v401 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n439 (20 : Fin 32) = v397 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n439 (21 : Fin 32) = v438 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n439 (22 : Fin 32) = v380 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n439 (23 : Fin 32) = v431 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n439 (24 : Fin 32) = v410 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n439 (25 : Fin 32) = v424 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n439 (26 : Fin 32) = v306 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n439 (27 : Fin 32) = v392 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n439 (28 : Fin 32) = v396 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n439 (29 : Fin 32) = v4 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n439 (30 : Fin 32) = v19 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n439 (31 : Fin 32) = v171 := by rw [u439.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so20 : memLoad32 Mi (F + 0x20) = v7 := by
    rw [sl20]
  have so24 : memLoad32 Mi (F + 0x24) = v0 := by
    rw [sl24]
  have so28 : memLoad32 Mi (F + 0x28) = outp := by
    rw [sl28]
  have so2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [sl2C]
  have so30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [sl4C]
  have so50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [sl50]
  have so54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [sl54]
  have so58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [sl74]
  have so78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [sl8C]
  have so90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [sl90]
  have so94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [sl9C]
  exact ⟨n439, Mi, v400, v401, v402, v403, v404, v405, v406, v407, v408, v409, v410, v411, v412, v413, v414, v415, v416, v417, v418, v419, v420, v421, v422, v423, v424, v425, v426, v427, v428, v429, v430, v431, v432, v433, v434, v435, v436, v437, v438, v439, (.cons d400 (.cons d401 (.cons d402 (.cons d403 (.cons d404 (.cons d405 (.cons d406 (.cons d407 (.cons d408 (.cons d409 (.cons d410 (.cons d411 (.cons d412 (.cons d413 (.cons d414 (.cons d415 (.cons d416 (.cons d417 (.cons d418 (.cons d419 (.cons d420 (.cons d421 (.cons d422 (.cons d423 (.cons d424 (.cons d425 (.cons d426 (.cons d427 (.cons d428 (.cons d429 (.cons d430 (.cons d431 (.cons d432 (.cons d433 (.cons d434 (.cons d435 (.cons d436 (.cons d437 (.cons d438 (.single d439)))))))))))))))))))))))))))))))))))))))), u439.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv400, hv401, hv402, hv403, hv404, hv405, hv406, hv407, hv408, hv409, hv410, hv411, hv412, hv413, hv414, hv415, hv416, hv417, hv418, hv419, hv420, hv421, hv422, hv423, hv424, hv425, hv426, hv427, hv428, hv429, hv430, hv431, hv432, hv433, hv434, hv435, hv436, hv437, hv438, hv439⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
theorem psm_g11 {M0 Mi : Word → BitVec 8} {B F outp G3 G4 : Word} {n : Machine} {v0 v3 v4 v7 v12 v17 v18 v19 v170 v171 v300 v306 v380 v391 v392 v396 v397 v401 v410 v414 v417 v418 v424 v426 v427 v431 v435 v437 v438 v439 : Word}
    (s : St Mi B n 0x5CA (reg n)) (hc : CodeIn Mi B p256ScalarMulCode)
    (fr : ∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → Mi x = M0 x) (hF : F.toNat % 4 = 0) (hO : outp.toNat % 4 = 0) (hB : B.toNat % 2 = 0)
    (sFC : Sep F 0xA0 B p256ScalarMulCode.length) (sF4C : Sep (F + 0xFFFFFFFC) 4 B p256ScalarMulCode.length)
    (sOC : Sep outp 32 B p256ScalarMulCode.length) (sOF : Sep outp 32 F 0xA0)
    (sOF4 : Sep outp 32 (F + 0xFFFFFFFC) 4) (hbs : CodeIn M0 (psmBsub B) borrowingSubCode)
    (sFB : Sep F 0xA0 (psmBsub B) borrowingSubCode.length)
    (sF4B : Sep (F + 0xFFFFFFFC) 4 (psmBsub B) borrowingSubCode.length)
    (sOB : Sep outp 32 (psmBsub B) borrowingSubCode.length)
    (q1 : reg n ra = v300)
    (q2 : reg n sp = F)
    (q3 : reg n (3 : Fin 32) = G3)
    (q4 : reg n (4 : Fin 32) = G4)
    (q5 : reg n (5 : Fin 32) = v3)
    (q6 : reg n (6 : Fin 32) = v12)
    (q7 : reg n (7 : Fin 32) = v391)
    (q8 : reg n (8 : Fin 32) = v437)
    (q9 : reg n (9 : Fin 32) = v426)
    (q10 : reg n a0 = v418)
    (q11 : reg n a1 = v435)
    (q12 : reg n a2 = v417)
    (q13 : reg n a3 = v439)
    (q14 : reg n a4 = v427)
    (q15 : reg n a5 = v414)
    (q16 : reg n a6 = v18)
    (q17 : reg n a7 = v17)
    (q18 : reg n (18 : Fin 32) = v170)
    (q19 : reg n (19 : Fin 32) = v401)
    (q20 : reg n (20 : Fin 32) = v397)
    (q21 : reg n (21 : Fin 32) = v438)
    (q22 : reg n (22 : Fin 32) = v380)
    (q23 : reg n (23 : Fin 32) = v431)
    (q24 : reg n (24 : Fin 32) = v410)
    (q25 : reg n (25 : Fin 32) = v424)
    (q26 : reg n (26 : Fin 32) = v306)
    (q27 : reg n (27 : Fin 32) = v392)
    (q28 : reg n (28 : Fin 32) = v396)
    (q29 : reg n (29 : Fin 32) = v4)
    (q30 : reg n (30 : Fin 32) = v19)
    (q31 : reg n (31 : Fin 32) = v171)
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
    : ∃ (n' : Machine) (M' : Word → BitVec 8) (v440 v441 v442 v443 v444 v445 v446 v447 v448 v449 v450 v451 v452 v453 v454 v455 v456 v457 v458 v459 v460 v461 v462 v463 v464 v465 v466 v467 v468 v469 v470 v471 v472 v473 v474 v475 v476 v477 v478 v479 : Word),
      Steps n n' ∧
      St M' B n' 0x64A (reg n') ∧
      CodeIn M' B p256ScalarMulCode ∧
      (∀ x, Sep F 0xA0 x 1 → Sep (F + 0xFFFFFFFC) 0x4 x 1 → Sep outp 0x20 x 1 → M' x = M0 x) ∧
      reg n' ra = v300 ∧
      reg n' sp = F ∧
      reg n' (3 : Fin 32) = G3 ∧
      reg n' (4 : Fin 32) = G4 ∧
      reg n' (5 : Fin 32) = v454 ∧
      reg n' (6 : Fin 32) = v12 ∧
      reg n' (7 : Fin 32) = v459 ∧
      reg n' (8 : Fin 32) = v462 ∧
      reg n' (9 : Fin 32) = v449 ∧
      reg n' a0 = v474 ∧
      reg n' a1 = v470 ∧
      reg n' a2 = v478 ∧
      reg n' a3 = v477 ∧
      reg n' a4 = v479 ∧
      reg n' a5 = v476 ∧
      reg n' a6 = v18 ∧
      reg n' a7 = v17 ∧
      reg n' (18 : Fin 32) = v451 ∧
      reg n' (19 : Fin 32) = v465 ∧
      reg n' (20 : Fin 32) = v397 ∧
      reg n' (21 : Fin 32) = v438 ∧
      reg n' (22 : Fin 32) = v444 ∧
      reg n' (23 : Fin 32) = v431 ∧
      reg n' (24 : Fin 32) = v410 ∧
      reg n' (25 : Fin 32) = v424 ∧
      reg n' (26 : Fin 32) = v306 ∧
      reg n' (27 : Fin 32) = v392 ∧
      reg n' (28 : Fin 32) = v447 ∧
      reg n' (29 : Fin 32) = v4 ∧
      reg n' (30 : Fin 32) = v19 ∧
      reg n' (31 : Fin 32) = v171 ∧
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
      aluEval .sub v391 v170 = v440 ∧
      aluEval .add v439 v437 = v441 ∧
      aluEval .sltu v440 v391 = v442 ∧
      aluEval .add v418 v442 = v443 ∧
      aluEval .add v440 v441 = v444 ∧
      aluEval .sltu v444 v440 = v445 ∧
      aluEval .mul v171 v3 = v446 ∧
      aluEval .add v396 v401 = v447 ∧
      aluEval .add v443 v445 = v448 ∧
      aluEval .add v448 v397 = v449 ∧
      aluEval .mul v171 v4 = v450 ∧
      aluEval .add v170 v447 = v451 ∧
      aluEval .mulhu v171 v3 = v452 ∧
      aluEval .sltu v449 v448 = v453 ∧
      aluEval .sltu v451 v447 = v454 ∧
      aluEval .and v410 0xFFFFFFFE = v455 ∧
      aluEval .mulhu v171 v4 = v456 ∧
      aluEval .add v446 v455 = v457 ∧
      aluEval .mul v171 v12 = v458 ∧
      aluEval .add v453 v451 = v459 ∧
      aluEval .sltu v457 v455 = v460 ∧
      aluEval .add v450 v417 = v461 ∧
      aluEval .mulhu v171 v12 = v462 ∧
      aluEval .add v460 v452 = v463 ∧
      aluEval .sltu v461 v417 = v464 ∧
      aluEval .add v461 v463 = v465 ∧
      aluEval .mul v171 v19 = v466 ∧
      aluEval .add v464 v456 = v467 ∧
      aluEval .sltu v465 v461 = v468 ∧
      aluEval .add v458 v424 = v469 ∧
      aluEval .mulhu v171 v19 = v470 ∧
      aluEval .add v468 v467 = v471 ∧
      aluEval .sltu v469 v424 = v472 ∧
      aluEval .add v472 v462 = v473 ∧
      aluEval .add v471 v469 = v474 ∧
      aluEval .sltu v474 v469 = v475 ∧
      aluEval .mulhu v171 v17 = v476 ∧
      aluEval .add v473 v475 = v477 ∧
      aluEval .add v466 v431 = v478 ∧
      aluEval .sltu v478 v431 = v479 := by
  have hz0 : reg n 0 = 0 := s.zero
  obtain ⟨n440, v440, d440, hv440, u440⟩ := s.aluG hc psm_at_5ca (off' := 0x5CE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv440
  obtain ⟨n441, v441, d441, hv441, u441⟩ := u440.aluG hc psm_at_5ce (off' := 0x5D0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv441
  obtain ⟨n442, v442, d442, hv442, u442⟩ := u441.aluG hc psm_at_5d0 (off' := 0x5D4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv442
  obtain ⟨n443, v443, d443, hv443, u443⟩ := u442.aluG hc psm_at_5d4 (off' := 0x5D6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv443
  obtain ⟨n444, v444, d444, hv444, u444⟩ := u443.aluG hc psm_at_5d6 (off' := 0x5DA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv444
  obtain ⟨n445, v445, d445, hv445, u445⟩ := u444.aluG hc psm_at_5da (off' := 0x5DE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv445
  obtain ⟨n446, v446, d446, hv446, u446⟩ := u445.aluG hc psm_at_5de (off' := 0x5E2) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv446
  obtain ⟨n447, v447, d447, hv447, u447⟩ := u446.aluG hc psm_at_5e2 (off' := 0x5E4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv447
  obtain ⟨n448, v448, d448, hv448, u448⟩ := u447.aluG hc psm_at_5e4 (off' := 0x5E6) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv448
  obtain ⟨n449, v449, d449, hv449, u449⟩ := u448.aluG hc psm_at_5e6 (off' := 0x5EA) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv449
  obtain ⟨n450, v450, d450, hv450, u450⟩ := u449.aluG hc psm_at_5ea (off' := 0x5EE) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv450
  obtain ⟨n451, v451, d451, hv451, u451⟩ := u450.aluG hc psm_at_5ee (off' := 0x5F0) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv451
  obtain ⟨n452, v452, d452, hv452, u452⟩ := u451.aluG hc psm_at_5f0 (off' := 0x5F4) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv452
  obtain ⟨n453, v453, d453, hv453, u453⟩ := u452.aluG hc psm_at_5f4 (off' := 0x5F8) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv453
  obtain ⟨n454, v454, d454, hv454, u454⟩ := u453.aluG hc psm_at_5f8 (off' := 0x5FC) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv454
  obtain ⟨n455, v455, d455, hv455, u455⟩ := u454.aluImmG hc psm_at_5fc (off' := 0x600) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv455
  obtain ⟨n456, v456, d456, hv456, u456⟩ := u455.aluG hc psm_at_600 (off' := 0x604) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv456
  obtain ⟨n457, v457, d457, hv457, u457⟩ := u456.aluG hc psm_at_604 (off' := 0x606) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv457
  obtain ⟨n458, v458, d458, hv458, u458⟩ := u457.aluG hc psm_at_606 (off' := 0x60A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv458
  obtain ⟨n459, v459, d459, hv459, u459⟩ := u458.aluG hc psm_at_60a (off' := 0x60C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv459
  obtain ⟨n460, v460, d460, hv460, u460⟩ := u459.aluG hc psm_at_60c (off' := 0x610) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv460
  obtain ⟨n461, v461, d461, hv461, u461⟩ := u460.aluG hc psm_at_610 (off' := 0x612) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv461
  obtain ⟨n462, v462, d462, hv462, u462⟩ := u461.aluG hc psm_at_612 (off' := 0x616) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv462
  obtain ⟨n463, v463, d463, hv463, u463⟩ := u462.aluG hc psm_at_616 (off' := 0x618) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv463
  obtain ⟨n464, v464, d464, hv464, u464⟩ := u463.aluG hc psm_at_618 (off' := 0x61C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv464
  obtain ⟨n465, v465, d465, hv465, u465⟩ := u464.aluG hc psm_at_61c (off' := 0x620) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv465
  obtain ⟨n466, v466, d466, hv466, u466⟩ := u465.aluG hc psm_at_620 (off' := 0x624) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv466
  obtain ⟨n467, v467, d467, hv467, u467⟩ := u466.aluG hc psm_at_624 (off' := 0x626) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv467
  obtain ⟨n468, v468, d468, hv468, u468⟩ := u467.aluG hc psm_at_626 (off' := 0x62A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv468
  obtain ⟨n469, v469, d469, hv469, u469⟩ := u468.aluG hc psm_at_62a (off' := 0x62C) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv469
  obtain ⟨n470, v470, d470, hv470, u470⟩ := u469.aluG hc psm_at_62c (off' := 0x630) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv470
  obtain ⟨n471, v471, d471, hv471, u471⟩ := u470.aluG hc psm_at_630 (off' := 0x632) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv471
  obtain ⟨n472, v472, d472, hv472, u472⟩ := u471.aluG hc psm_at_632 (off' := 0x636) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv472
  obtain ⟨n473, v473, d473, hv473, u473⟩ := u472.aluG hc psm_at_636 (off' := 0x638) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv473
  obtain ⟨n474, v474, d474, hv474, u474⟩ := u473.aluG hc psm_at_638 (off' := 0x63A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv474
  obtain ⟨n475, v475, d475, hv475, u475⟩ := u474.aluG hc psm_at_63a (off' := 0x63E) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv475
  obtain ⟨n476, v476, d476, hv476, u476⟩ := u475.aluG hc psm_at_63e (off' := 0x642) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv476
  obtain ⟨n477, v477, d477, hv477, u477⟩ := u476.aluG hc psm_at_642 (off' := 0x644) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv477
  obtain ⟨n478, v478, d478, hv478, u478⟩ := u477.aluG hc psm_at_644 (off' := 0x646) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv478
  obtain ⟨n479, v479, d479, hv479, u479⟩ := u478.aluG hc psm_at_646 (off' := 0x64A) (by decide)
  simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] at hv479
  have qo1 : reg n479 ra = v300 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo2 : reg n479 sp = F := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo3 : reg n479 (3 : Fin 32) = G3 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo4 : reg n479 (4 : Fin 32) = G4 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo5 : reg n479 (5 : Fin 32) = v454 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo6 : reg n479 (6 : Fin 32) = v12 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo7 : reg n479 (7 : Fin 32) = v459 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo8 : reg n479 (8 : Fin 32) = v462 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo9 : reg n479 (9 : Fin 32) = v449 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo10 : reg n479 a0 = v474 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo11 : reg n479 a1 = v470 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo12 : reg n479 a2 = v478 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo13 : reg n479 a3 = v477 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo14 : reg n479 a4 = v479 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo15 : reg n479 a5 = v476 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo16 : reg n479 a6 = v18 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo17 : reg n479 a7 = v17 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo18 : reg n479 (18 : Fin 32) = v451 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo19 : reg n479 (19 : Fin 32) = v465 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo20 : reg n479 (20 : Fin 32) = v397 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo21 : reg n479 (21 : Fin 32) = v438 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo22 : reg n479 (22 : Fin 32) = v444 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo23 : reg n479 (23 : Fin 32) = v431 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo24 : reg n479 (24 : Fin 32) = v410 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo25 : reg n479 (25 : Fin 32) = v424 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo26 : reg n479 (26 : Fin 32) = v306 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo27 : reg n479 (27 : Fin 32) = v392 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo28 : reg n479 (28 : Fin 32) = v447 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo29 : reg n479 (29 : Fin 32) = v4 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo30 : reg n479 (30 : Fin 32) = v19 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have qo31 : reg n479 (31 : Fin 32) = v171 := by rw [u479.regs]; simp +decide only [upd, ↓reduceIte, hz0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]
  have so20 : memLoad32 Mi (F + 0x20) = v7 := by
    rw [sl20]
  have so24 : memLoad32 Mi (F + 0x24) = v0 := by
    rw [sl24]
  have so28 : memLoad32 Mi (F + 0x28) = outp := by
    rw [sl28]
  have so2C : memLoad32 Mi (F + 0x2C) = memLoad32 M0 (F + 0x2C) := by
    rw [sl2C]
  have so30 : memLoad32 Mi (F + 0x30) = memLoad32 M0 (F + 0x30) := by
    rw [sl30]
  have so34 : memLoad32 Mi (F + 0x34) = memLoad32 M0 (F + 0x34) := by
    rw [sl34]
  have so38 : memLoad32 Mi (F + 0x38) = memLoad32 M0 (F + 0x38) := by
    rw [sl38]
  have so3C : memLoad32 Mi (F + 0x3C) = memLoad32 M0 (F + 0x3C) := by
    rw [sl3C]
  have so40 : memLoad32 Mi (F + 0x40) = memLoad32 M0 (F + 0x40) := by
    rw [sl40]
  have so44 : memLoad32 Mi (F + 0x44) = memLoad32 M0 (F + 0x44) := by
    rw [sl44]
  have so48 : memLoad32 Mi (F + 0x48) = memLoad32 M0 (F + 0x48) := by
    rw [sl48]
  have so4C : memLoad32 Mi (F + 0x4C) = memLoad32 M0 (F + 0x4C) := by
    rw [sl4C]
  have so50 : memLoad32 Mi (F + 0x50) = memLoad32 M0 (F + 0x50) := by
    rw [sl50]
  have so54 : memLoad32 Mi (F + 0x54) = memLoad32 M0 (F + 0x54) := by
    rw [sl54]
  have so58 : memLoad32 Mi (F + 0x58) = memLoad32 M0 (F + 0x58) := by
    rw [sl58]
  have so5C : memLoad32 Mi (F + 0x5C) = memLoad32 M0 (F + 0x5C) := by
    rw [sl5C]
  have so60 : memLoad32 Mi (F + 0x60) = memLoad32 M0 (F + 0x60) := by
    rw [sl60]
  have so64 : memLoad32 Mi (F + 0x64) = memLoad32 M0 (F + 0x64) := by
    rw [sl64]
  have so68 : memLoad32 Mi (F + 0x68) = memLoad32 M0 (F + 0x68) := by
    rw [sl68]
  have so6C : memLoad32 Mi (F + 0x6C) = memLoad32 M0 (F + 0x6C) := by
    rw [sl6C]
  have so70 : memLoad32 Mi (F + 0x70) = memLoad32 M0 (F + 0x70) := by
    rw [sl70]
  have so74 : memLoad32 Mi (F + 0x74) = memLoad32 M0 (F + 0x74) := by
    rw [sl74]
  have so78 : memLoad32 Mi (F + 0x78) = memLoad32 M0 (F + 0x78) := by
    rw [sl78]
  have so7C : memLoad32 Mi (F + 0x7C) = memLoad32 M0 (F + 0x7C) := by
    rw [sl7C]
  have so80 : memLoad32 Mi (F + 0x80) = memLoad32 M0 (F + 0x80) := by
    rw [sl80]
  have so84 : memLoad32 Mi (F + 0x84) = memLoad32 M0 (F + 0x84) := by
    rw [sl84]
  have so88 : memLoad32 Mi (F + 0x88) = memLoad32 M0 (F + 0x88) := by
    rw [sl88]
  have so8C : memLoad32 Mi (F + 0x8C) = memLoad32 M0 (F + 0x8C) := by
    rw [sl8C]
  have so90 : memLoad32 Mi (F + 0x90) = memLoad32 M0 (F + 0x90) := by
    rw [sl90]
  have so94 : memLoad32 Mi (F + 0x94) = memLoad32 M0 (F + 0x94) := by
    rw [sl94]
  have so98 : memLoad32 Mi (F + 0x98) = memLoad32 M0 (F + 0x98) := by
    rw [sl98]
  have so9C : memLoad32 Mi (F + 0x9C) = memLoad32 M0 (F + 0x9C) := by
    rw [sl9C]
  exact ⟨n479, Mi, v440, v441, v442, v443, v444, v445, v446, v447, v448, v449, v450, v451, v452, v453, v454, v455, v456, v457, v458, v459, v460, v461, v462, v463, v464, v465, v466, v467, v468, v469, v470, v471, v472, v473, v474, v475, v476, v477, v478, v479, (.cons d440 (.cons d441 (.cons d442 (.cons d443 (.cons d444 (.cons d445 (.cons d446 (.cons d447 (.cons d448 (.cons d449 (.cons d450 (.cons d451 (.cons d452 (.cons d453 (.cons d454 (.cons d455 (.cons d456 (.cons d457 (.cons d458 (.cons d459 (.cons d460 (.cons d461 (.cons d462 (.cons d463 (.cons d464 (.cons d465 (.cons d466 (.cons d467 (.cons d468 (.cons d469 (.cons d470 (.cons d471 (.cons d472 (.cons d473 (.cons d474 (.cons d475 (.cons d476 (.cons d477 (.cons d478 (.single d479)))))))))))))))))))))))))))))))))))))))), u479.self, hc, fr, qo1, qo2, qo3, qo4, qo5, qo6, qo7, qo8, qo9, qo10, qo11, qo12, qo13, qo14, qo15, qo16, qo17, qo18, qo19, qo20, qo21, qo22, qo23, qo24, qo25, qo26, qo27, qo28, qo29, qo30, qo31, so20, so24, so28, so2C, so30, so34, so38, so3C, so40, so44, so48, so4C, so50, so54, so58, so5C, so60, so64, so68, so6C, so70, so74, so78, so7C, so80, so84, so88, so8C, so90, so94, so98, so9C, hv440, hv441, hv442, hv443, hv444, hv445, hv446, hv447, hv448, hv449, hv450, hv451, hv452, hv453, hv454, hv455, hv456, hv457, hv458, hv459, hv460, hv461, hv462, hv463, hv464, hv465, hv466, hv467, hv468, hv469, hv470, hv471, hv472, hv473, hv474, hv475, hv476, hv477, hv478, hv479⟩

end C3.RV32
